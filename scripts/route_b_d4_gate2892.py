"""Run the committed Route B D4 artifact gate as one deterministic command."""
import json
import subprocess
import sys
from pathlib import Path


def main():
    checker = Path("scripts/route_b_d4_cauchy_certificate_check2891.py")
    result = subprocess.run([sys.executable, str(checker)], capture_output=True, text=True)
    if result.stdout:
        print(result.stdout, end="")
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr)
    if result.returncode != 0:
        raise SystemExit(result.returncode)
    payload = json.loads(Path("results/2891_route_b_d4_cauchy_certificate_check.json").read_text())
    required = ["artifact_consistency", "formal_cauchy_proof"]
    if not payload["all_checks_pass"] or not payload["claims"][required[0]]:
        raise SystemExit("D4 artifact gate failed")
    print("route_b_d4_gate2892: PASS (artifact consistency; formal proof remains open)")


if __name__ == "__main__":
    main()
