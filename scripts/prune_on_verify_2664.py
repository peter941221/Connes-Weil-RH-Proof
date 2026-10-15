#!/usr/bin/env python3
"""Dependency-safe cleanup for one verified record-2664 entry.

The command is dry-run by default.  ``--apply`` removes only generated files
inside the selected entry's build directories after checking the committed
source and assembly SHA-256 manifests.  Shared ``ConnesWeilRH/Dev`` outputs
are never removed by this tool.
"""

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH" / "Dev"
RESULTS = ROOT / "results"
BUILD = ROOT / ".lake" / "build"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read_entry(row: int, col: int):
    payload_path = RESULTS / f"2664_entry_{row}_{col}.json"
    assembly_path = RESULTS / f"2664_assembly_{row}_{col}.json"
    if not payload_path.exists() or not assembly_path.exists():
        raise SystemExit("missing committed entry or assembly payload")
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    assembly = json.loads(assembly_path.read_text(encoding="utf-8"))
    names = set(payload["modules_sha256"]) | set(assembly["modules_sha256"])
    for name, want in {**payload["modules_sha256"],
                       **assembly["modules_sha256"]}.items():
        path = (DEV / name) if name.startswith("C1RouteAOffDiagEntry") \
            else DEV / f"OffDiagE{row:02d}_{col:02d}" / name
        if not path.exists() or sha256(path) != want:
            raise SystemExit(f"source manifest check failed: {path}")
    return names


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("row", type=int)
    ap.add_argument("col", type=int)
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()
    names = read_entry(args.row, args.col)
    sub = f"OffDiagE{args.row:02d}_{args.col:02d}"
    roots = [BUILD / "lib" / "lean" / "ConnesWeilRH" / "Dev" / sub,
             BUILD / "ir" / "ConnesWeilRH" / "Dev" / sub]
    candidates = [p for root in roots if root.is_dir() for p in root.rglob("*")
                  if p.is_file() and p.suffix in {".olean", ".ilean", ".ir", ".c"}
                  and p.stem in {Path(n).stem for n in names}]
    total = sum(p.stat().st_size for p in candidates)
    print(f"entry=({args.row},{args.col}) verified_sources={len(names)}")
    print(f"candidates={len(candidates)} bytes={total}")
    for p in candidates:
        print(p)
    if args.apply:
        for p in candidates:
            p.unlink()
        print(f"removed={len(candidates)} bytes={total}")
    else:
        print("dry-run only; pass --apply after reviewing the list")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
