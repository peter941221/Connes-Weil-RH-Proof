#!/usr/bin/env python3
"""Aggregate byte manifest for record-2664 off-diagonal entry chains.

Entry chains are ~157-212 MB of Lean sources each (plus ~0.5-0.8 GB of
oleans); 869 entries are ~150-190 GB of sources and ~600-700 GB of oleans,
over the available disk.  The chains are therefore NOT byte-committed and
NOT kept on disk as a set: they are regenerated deterministically by

    python scripts/gen_2664_entry.py --row=R --col=C --degree=D --emit
    python scripts/gen_2664_entry.py --row=R --col=C --degree=D   (dry gate)

and each entry's own payload `results/2664_entry_{row}_{col}.json`
(~4.5 MB, untracked, dominated by per-panel table reports) carries
`modules_sha256` for all 951 modules of the chain.

THIS manifest is the committed byte evidence: for every on-disk entry
payload it

  1. re-hashes every module of the chain from disk and requires the result
     to equal the payload's own `modules_sha256` (drift fails loudly, and
     any extra .lean on disk beyond the manifest set is reported);
  2. records one canonical `chain_sha256` per entry =
     sha256(json.dumps(modules_sha256, sort_keys=True, separators=(",",":")))
     plus the entry parameters, degree and module count.

Usage: python scripts/build_entry_manifest_2664.py
Writes results/2664_offdiag_manifest.json (all disk-verified payloads).
"""

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH" / "Dev"
RESULTS = ROOT / "results"

PAYLOAD_RE = re.compile(r"^2664_entry_(\d+)_(\d+)\.json$")

DIGEST_CONVENTION = ("sha256 over the canonical JSON of the payload's "
                     "modules_sha256 map: json.dumps(map, sort_keys=True, "
                     "separators=(\",\", \":\")).encode(\"utf-8\")")


def canonical(map_):
    return json.dumps(map_, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")


def main():
    args = sys.argv[1:]
    if args:
        raise SystemExit("usage: build_entry_manifest_2664.py")
    payloads = sorted(
        p for p in RESULTS.glob("2664_entry_*.json")
        if PAYLOAD_RE.match(p.name))
    if not payloads:
        raise SystemExit("no results/2664_entry_{row}_{col}.json payloads "
                         "on disk")

    entries = []
    failures = []
    for path in payloads:
        payload = json.loads(path.read_text(encoding="utf-8"))
        row, col = payload["entry"]
        edir = DEV / f"OffDiagE{row:02d}_{col:02d}"
        digest_map = payload["modules_sha256"]
        mismatched = []
        for name, want in sorted(digest_map.items()):
            mpath = (DEV / name) if name.startswith("C1RouteAOffDiagEntry") \
                else (edir / name)
            if not mpath.exists():
                mismatched.append((name, "missing"))
                continue
            got = hashlib.sha256(mpath.read_bytes()).hexdigest()
            if got != want:
                mismatched.append((name, "sha-mismatch"))
        on_disk = {f.name for f in edir.glob("*.lean")}
        on_disk |= {f.name for f in DEV.glob(
            f"C1RouteAOffDiagEntry2664E{row:02d}_{col:02d}.lean")}
        extra = sorted(on_disk - set(digest_map))
        chain = hashlib.sha256(canonical(digest_map)).hexdigest()
        ok = not mismatched and not extra
        if not ok:
            failures.append((row, col, mismatched[:5], extra[:5]))
        entries.append({
            "row": row, "column": col,
            "degree": payload["degree"],
            "radius_exact": payload["radius_exact"],
            "beta_exact": payload["beta_exact"],
            "psi_exact": payload["psi_exact"],
            "vacuous_panels": len(payload["vacuous_panels"]),
            "module_count": payload["module_count"],
            "modules_sha256_count": len(digest_map),
            "chain_sha256": chain,
            "disk_verified": ok,
            "payload": path.name,
            "generator_sha256": payload["generator_sha256"],
            "capture_sha256": payload["capture_sha256"],
        })
        print(f"({row:2d},{col:2d}) deg {payload['degree']:2d} "
              f"{len(digest_map)} modules chain={chain[:16]}.. "
              f"disk_verified={ok}")

    out = {
        "record": 2664,
        "purpose": "committed byte evidence for the record-2664 off-diagonal "
                   "entry chains (regenerated deterministically; per-entry "
                   "payloads untracked)",
        "digest_convention": DIGEST_CONVENTION,
        "regeneration": "gen_2664_entry.py --row=R --col=C --degree=D --emit "
                        "followed by the same invocation in dry mode "
                        "(byte-stability gate); rebuild must reproduce "
                        "chain_sha256",
        "entries": entries,
    }
    out_path = RESULTS / "2664_offdiag_manifest.json"
    with open(out_path, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print(f"wrote {out_path.name} with {len(entries)} entries")
    if failures:
        for row, col, mism, extra in failures:
            print(f"FAIL ({row},{col}) mismatched={mism} extra={extra}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())