"""Generate exact rational Lean parameters for the captured 2338 owner."""

from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean"


def real_expr(value: float) -> str:
    fraction = Fraction.from_float(value)
    if fraction.denominator == 1:
        return f"({fraction.numerator} : ℝ)"
    return f"(({fraction.numerator} : ℝ) / {fraction.denominator})"


def complex_expr(pair) -> str:
    real, imaginary = (float.fromhex(item) for item in pair)
    return f"⟨{real_expr(real)}, {real_expr(imaginary)}⟩"


def vector(name: str, values: list[str], type_name: str) -> str:
    body = ",\n    ".join(values)
    return f"noncomputable def {name} : Fin 30 → {type_name} :=\n  ![{body}]\n"


def main():
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    source_hash = hashlib.sha256(CAPTURE.read_bytes()).hexdigest()
    widths = [real_expr(float.fromhex(width)) for width, _ in capture["families_hex"]]
    modulations = [real_expr(float.fromhex(modulation)) for _, modulation in capture["families_hex"]]
    nodes = [complex_expr(pair) for pair in capture["nodes_hex"]]
    targets = [complex_expr(pair) for pair in capture["values_hex"]]
    text = f'''import ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-! Exact rational lift of the captured 2338 owner parameters.
Capture SHA256: {source_hash}
The values are lifted from binary64 operands; no interval conclusion is stored.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

{vector("capturedWidth2584", widths, "ℝ")}
{vector("capturedModulations2584", modulations, "ℝ")}
{vector("capturedNodes2584", nodes, "ℂ")}
{vector("capturedTargets2584", targets, "ℂ")}

theorem storedWidth_eq_capturedWidth2584 (index : Fin 30) :
    storedWidth index = capturedWidth2584 index := by
  fin_cases index <;> norm_num [storedWidth, capturedWidth2584]

end ConnesWeilRH.Dev
'''
    OUTPUT.write_text(text, encoding="utf-8", newline="\n")
    print(json.dumps({
        "record": 2584,
        "output": str(OUTPUT.relative_to(ROOT)),
        "capture_sha256": source_hash,
        "family_count": len(widths),
        "node_count": len(nodes),
        "target_count": len(targets),
    }, indent=2))


if __name__ == "__main__":
    main()
