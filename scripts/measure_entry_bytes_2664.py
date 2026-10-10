#!/usr/bin/env python3
"""Record-2664 byte-wall measurement: size profile of ONE off-diagonal entry
chain, and the batch projection.

The per-entry five-family chain is generated (never byte-committed); this
script measures the committed (0,3) profile and the staged (29,3) degree-66
profile from disk and writes results/2664_byte_wall.json.  The projection
columns are the reason the batch is manifest-pinned instead of committed:
869 chains exceed both the free disk and any hosted-git scale.

Run: python3 scripts/measure_entry_bytes_2664.py
"""

import json
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH" / "Dev"
STAGE = ROOT / "_probe" / "stage_E29_03"

FAMILIES = (
    "C1RouteAComplexPanelTable2655P",
    "C1RouteAComplexPanelAnalytic2656P",
    "C1RouteAAmpPin2657P",
    "C1RouteAPhasePin2658P",
    "C1RouteAPanelTrueBall2662P",
)


def family_sizes(directory, patterns):
    out = {}
    total = 0
    count = 0
    for fam, pattern in patterns.items():
        files = sorted(directory.glob(pattern))
        size = sum(p.stat().st_size for p in files)
        out[fam] = {"modules": len(files), "bytes": size}
        total += size
        count += len(files)
    return count, total, out


def main():
    committed = family_sizes(DEV, {f: f + "*.lean" for f in FAMILIES})
    # stage dir is a probe artifact: report when present, else null
    staged = None
    if STAGE.is_dir():
        staged = family_sizes(STAGE, {f: f + "*.lean" for f in FAMILIES})
    disk = shutil.disk_usage(str(ROOT.anchor or "/"))

    batch = 869  # off-diagonal entries needing their own chain (record 2664)
    payload = {
        "record": 2664,
        "purpose": "size profile of one entry chain and the batch projection; "
                   "basis of the manifest-pin policy",
        "committed_0_3_chain": {
            "modules": committed[0], "bytes": committed[1],
            "per_family": committed[2],
            "note": "on disk and in git today (2655P109 replaced by 2648P109)",
        },
        "staged_29_3_degree66_chain": None if staged is None else {
            "modules": staged[0], "bytes": staged[1],
            "per_family": staged[2],
            "note": "probe staging dir _probe/stage_E29_03 (render validation)",
        },
        "batch_projection": {
            "offdiag_entries": batch,
            "committed_profile_bytes": batch * committed[1],
            "staged_profile_bytes": None if staged is None else batch * staged[1],
        },
        "disk": {"total": disk.total, "free": disk.free},
        "verdict": "one entry chain is ~%d MB (committed profile) / ~%d MB "
                   "(degree-66 profile); the %d-entry batch is %.0f-%.0f GB, "
                   "beyond the free disk and ~450x the repo pack, so entry "
                   "chains are regenerated deterministically and byte-pinned "
                   "by manifest sha256 lists instead of being committed"
                   % (committed[1] // 10**6,
                      (staged[1] // 10**6) if staged else -1, batch,
                      batch * committed[1] / 10**9,
                      (batch * staged[1] / 10**9) if staged else -1),
        "membership_claimed": False,
        "producer_go": False,
    }
    out = ROOT / "results" / "2664_byte_wall.json"
    out.write_text(json.dumps(payload, indent=1) + "\n",
                   encoding="utf-8", newline="\n")
    print(json.dumps(payload["batch_projection"], indent=1))
    print(payload["verdict"])
    return 0


if __name__ == "__main__":
    sys.exit(main())