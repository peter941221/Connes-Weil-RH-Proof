#!/usr/bin/env python3
from __future__ import annotations
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH.Dev.C1RouteBAdaptiveVariableLambdaContradiction3132Audit"
SOURCE = "ConnesWeilRH/Dev/C1RouteBAdaptiveVariableLambdaContradiction3132.lean"
AUDIT = "ConnesWeilRH/Dev/C1RouteBAdaptiveVariableLambdaContradiction3132Audit.lean"
THEOREM = "ConnesWeilRH.Source.C1RouteBAdaptiveVariableLambdaContradiction3132.negative_owner_rejects_variable_lambda_gate3132"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()

def main() -> int:
    run = subprocess.run(["lake", "build", MODULE], cwd=ROOT, text=True, encoding="utf-8", errors="replace", stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    output = run.stdout or ""
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
    entry = next(((name, axioms) for name, axioms in matches if name == THEOREM), None)
    axioms = {part.strip() for part in (entry[1] if entry else "").split(",") if part.strip()}
    footer = re.search(r"Build completed successfully \((\d+) jobs?\)", output)
    report = {"record": 3132, "status": "PASS" if run.returncode == 0 and footer and entry and axioms == ALLOWED and "error:" not in output and "sorryAx" not in output else "FAIL", "module": MODULE, "build_jobs": int(footer.group(1)) if footer else None, "returncode": run.returncode, "theorem_found": bool(entry), "axioms": sorted(axioms), "unexpected_axioms": sorted(axioms - ALLOWED), "error_lines_present": "error:" in output, "sorryAx_present": "sorryAx" in output, "provenance": {SOURCE: digest(ROOT / SOURCE), AUDIT: digest(ROOT / AUDIT)}, "scope": "Same-owner logical rejection of the arbitrary variable-lambda gate under span qw < 0 and span triple vanishing; no numerical owner manifest, margin, Producer GO, SourceRH, or RH claim."}
    out = ROOT / "results/3132_routeb_adaptive_variable_lambda_contradiction_audit.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if report["status"] == "PASS" else 1

if __name__ == "__main__":
    raise SystemExit(main())