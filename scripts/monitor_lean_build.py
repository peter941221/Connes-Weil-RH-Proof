#!/usr/bin/env python3
"""Record a Linux build's health until its supervising process exits."""
import argparse
import datetime
import json
from pathlib import Path
import shutil
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--pid", type=int, required=True)
parser.add_argument("--root", type=Path, required=True)
parser.add_argument("--log", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
args.output.parent.mkdir(parents=True, exist_ok=True)
offset = 0
errors = []
while True:
    try:
        with args.log.open("rb") as stream:
            if args.log.stat().st_size < offset:
                offset = 0
            stream.seek(offset)
            chunk = stream.read().decode("utf-8", errors="replace")
            offset = stream.tell()
        errors.extend(line for line in chunk.splitlines() if "error:" in line)
    except FileNotFoundError:
        pass
    running = Path(f"/proc/{args.pid}").exists()
    base = args.root / ".lake/build/lib/lean/ConnesWeilRH/Dev"
    row = {
        "time": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "supervisor_running": running,
        "free_gib": round(shutil.disk_usage(args.root).free / 2**30, 2),
        "memory": Path("/proc/meminfo").read_text().splitlines()[:3],
        "errors_seen": errors[-10:],
        "artifacts_present": {
            name: (base / f"{name}.olean").exists()
            for name in (
                "ZProbe2628K02", "ZProbe2628K04",
                "C1RouteACorrectionAnalyticOffDiagCertificate2695",
                "C1RouteACorrectionAnalyticOffDiagCertificate2695Audit",
            )
        },
    }
    with args.output.open("a") as stream:
        stream.write(json.dumps(row) + "\n")
    print(json.dumps(row), flush=True)
    if not running:
        break
    time.sleep(60)
