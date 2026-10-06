"""Generate the 2351 analytic matrix interval payload for Lean."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WITNESS = ROOT / "results/2351_moment_matrix_witness.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionAnalyticIntervals2597.lean"


def real_expr(value: str) -> str:
    fraction = Fraction(value)
    if fraction.denominator == 1:
        return f"({fraction.numerator} : ℝ)"
    return f"(({fraction.numerator} : ℝ) / {fraction.denominator})"


def rect_expr(entry: dict) -> str:
    return (
        "{ reLo := " + real_expr(entry["real"]["lower_exact"]) +
        "\n        reHi := " + real_expr(entry["real"]["upper_exact"]) +
        "\n        imLo := " + real_expr(entry["imag"]["lower_exact"]) +
        "\n        imHi := " + real_expr(entry["imag"]["upper_exact"]) + " }"
    )


def main() -> None:
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    matrix = payload["matrix"]
    if len(matrix) != 30 or any(len(row) != 30 for row in matrix):
        raise ValueError("expected a 30 by 30 analytic matrix")
    row_names = [f"analyticMomentInterval2597_row_{i:02d}" for i in range(30)]
    row_defs = []
    for name, row in zip(row_names, matrix):
        row_defs.append(
            f"/-- Witness interval row `{name}`. -/\n"
            f"noncomputable def {name} : Fin 30 → ComplexRect2427 :=\n"
            "  ![" + ",\n    ".join(rect_expr(entry) for entry in row) + "]\n"
        )
    source_hash = hashlib.sha256(WITNESS.read_bytes()).hexdigest()
    text = f'''import ConnesWeilRH.Dev.C1RouteAAnalyticMomentSystem
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

/-! Exact rational rectangles exported from the 2351 analytic-matrix witness.
Witness SHA256: {source_hash}
The rectangles are data only. Their containment of the Lean analytic integrals
is an explicit premise below; this file does not treat JSON or Arb output as a
Lean proof. -/

namespace ConnesWeilRH.Dev

{"\n\n".join(row_defs)}

/-- The 30 by 30 rectangle payload for the analytic moment matrix. -/
noncomputable def analyticMomentInterval2597 :
    Matrix (Fin 30) (Fin 30) ComplexRect2427 :=
  ![{",\n    ".join(row_names)}]

/-- Explicit soundness socket for the 2338 analytic interval certificate. -/
theorem actualOwnerMomentMatrix2351_entry_mem_analyticMomentInterval2597
    (h_interval : ∀ i j : Fin 30,
      (analyticMomentInterval2597 i j).Mem
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 i j))
    (i j : Fin 30) :
    (analyticMomentInterval2597 i j).Mem
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 i j) :=
  h_interval i j

end ConnesWeilRH.Dev
'''
    OUTPUT.write_text(text, encoding="utf-8", newline="\n")
    print(json.dumps({
        "record": 2597,
        "rows": 30,
        "entries": 900,
        "witness_sha256": source_hash,
        "output": str(OUTPUT.relative_to(ROOT)),
    }, indent=2))


if __name__ == "__main__":
    main()
