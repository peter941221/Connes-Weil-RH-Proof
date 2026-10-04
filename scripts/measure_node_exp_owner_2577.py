"""Separate fixed-input first-value proof checking from derivative reuse costs."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import re
import resource
import statistics
import subprocess
import tempfile
import time

import generate_node_exp_owner_2577 as generation

ROOT, DEV = generation.ROOT, generation.DEV


def measure(lake, mirror, repetitions):
    assert repetitions >= 2
    payload = json.loads((ROOT / "results/2577_node_exp_generation.json").read_text())
    reports = []
    with tempfile.TemporaryDirectory(prefix="rh_node_owner_") as temporary:
        for row in payload["rows"]:
            index, sign = row["index"], row["sign"]
            cases = [("value_owner", generation.names(index, sign)),
                     ("order_two", generation.names(index, sign, 2)),
                     ("order_three", generation.names(index, sign, 3))]
            samples = {label: [] for label, _ in cases}
            warmup = {}
            hashes = {}
            for repetition in range(repetitions + 1):
                ordered = cases if repetition % 2 == 0 else list(reversed(cases))
                for label, naming in ordered:
                    source_path = DEV / (naming["module"] + ".lean")
                    data = source_path.read_bytes()
                    relative = str(source_path.relative_to(ROOT))
                    assert data == (mirror / relative).read_bytes()
                    assert hashlib.sha256(data).hexdigest() == payload["output_sha256"][relative]
                    source = re.sub(r"^#print axioms.*\n?", "", data.decode(), flags=re.MULTILINE)
                    path = Path(temporary) / (naming["module"] + ".lean")
                    path.write_text(source, encoding="utf-8", newline="\n")
                    hashes[relative] = hashlib.sha256(data).hexdigest()
                    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
                    started = time.monotonic()
                    completed = subprocess.run([str(lake), "env", "lean", str(path)], cwd=mirror,
                                               capture_output=True, text=True)
                    elapsed = time.monotonic() - started
                    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
                    assert completed.returncode == 0, completed.stdout + completed.stderr
                    assert not re.search(r"\bsorry(?:Ax)?\b", completed.stdout + completed.stderr)
                    reading = dict(wall_seconds=elapsed,
                                   user_seconds=usage_after.ru_utime - usage_before.ru_utime,
                                   system_seconds=usage_after.ru_stime - usage_before.ru_stime,
                                   minor_faults=usage_after.ru_minflt - usage_before.ru_minflt,
                                   major_faults=usage_after.ru_majflt - usage_before.ru_majflt)
                    if repetition == 0:
                        warmup[label] = reading
                    else:
                        samples[label].append(reading)
                    print("NODE_COST", index, sign, label, repetition, elapsed, flush=True)
            reports.append(dict(index=index, sign=sign, active=len(row["active"]),
                                warmup=warmup, samples=samples,
                                mean_wall_seconds={label: statistics.mean(
                                    reading["wall_seconds"] for reading in readings)
                                    for label, readings in samples.items()}, source_sha256=hashes))
    result = dict(record=2577, status="NODE_OWNER_COST_MEASURED", rows=reports,
                  repetitions=repetitions, warmup_rounds=1, alternating_order=True,
                  imports_warm=True, platform=platform.platform(),
                  lean_toolchain=(ROOT / "lean-toolchain").read_text().strip(),
                  scope="fixed fresh-node inputs; value-owner source is checked in full; imported infrastructure is warm; not cold end-to-end generation or full-grid throughput",
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  generation_sha256=hashlib.sha256((ROOT / "results/2577_node_exp_generation.json").read_bytes()).hexdigest(),
                  full_grid_certificate=False, rh_claim=False)
    output = ROOT / "results/2577_node_exp_cost.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("NODE_OWNER_COST_MEASURED", len(reports), flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", type=Path, required=True)
    parser.add_argument("--mirror", type=Path, required=True)
    parser.add_argument("--repetitions", type=int, default=2)
    args = parser.parse_args()
    measure(args.lake, args.mirror, args.repetitions)


if __name__ == "__main__":
    main()
