"""Generate exact rational Lean rectangles for the 2338 correction intervals."""

from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionExactIntervals2586.lean"


def real_expr(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : ℝ)"
    return f"(({value.numerator} : ℝ) / {value.denominator})"


def main():
    data = json.loads(REPAIR.read_text(encoding="utf-8"))
    rows = data["coefficient_rows"]
    if len(rows) != 30:
        raise AssertionError("expected 30 correction rows")
    source_hash = hashlib.sha256(REPAIR.read_bytes()).hexdigest()
    fields = []
    for row in rows:
        coefficient = row["ideal_correction_coefficient"]
        fields.append({
            "reLo": Fraction(coefficient["real"]["lower_exact"]),
            "reHi": Fraction(coefficient["real"]["upper_exact"]),
            "imLo": Fraction(coefficient["imag"]["lower_exact"]),
            "imHi": Fraction(coefficient["imag"]["upper_exact"]),
        })
    entries = []
    for field in fields:
        entries.append(
            "      { reLo := %s\n        reHi := %s\n        imLo := %s\n        imHi := %s }"
            % tuple(real_expr(field[name]) for name in ("reLo", "reHi", "imLo", "imHi"))
        )
    branches = "\n  | ".join(f"{index} =>\n{entry}" for index, entry in enumerate(entries))
    branches += "\n  | _ => ComplexRect2427.zero"
    text = f'''import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

/-! Exact rational lift of the record-2338 correction solution intervals.
Repair JSON SHA256: {source_hash}
These are imported interval endpoints only; analytic enclosure soundness is not
asserted in this file.
-/

namespace ConnesWeilRH.Dev

noncomputable def exactCorrectionInterval2586 (index : Fin 30) : ComplexRect2427 :=
  match index.val with
  | {branches}

theorem exactCorrectionInterval_mem_correctionBox2586 (i : Fin 30) :
    (correctionCoefficientBox2570 i).reLo ≤ (exactCorrectionInterval2586 i).reLo ∧
    (exactCorrectionInterval2586 i).reHi ≤ (correctionCoefficientBox2570 i).reHi ∧
    (correctionCoefficientBox2570 i).imLo ≤ (exactCorrectionInterval2586 i).imLo ∧
    (exactCorrectionInterval2586 i).imHi ≤ (correctionCoefficientBox2570 i).imHi := by
  fin_cases i <;> norm_num [exactCorrectionInterval2586, correctionCoefficientBox2570]

theorem actualCorrectionOwner_mem_correctionBox_of_exactInterval2586
    (actual : Fin 30 → ℂ)
    (h_exact_interval : ∀ i : Fin 30,
      (exactCorrectionInterval2586 i).Mem (actual i)) :
    ∀ i : Fin 30, (correctionCoefficientBox2570 i).Mem (actual i) := by
  intro i
  have hcontain := exactCorrectionInterval_mem_correctionBox2586 i
  have hactual := h_exact_interval i
  change (correctionCoefficientBox2570 i).reLo ≤ (actual i).re ∧
    (actual i).re ≤ (correctionCoefficientBox2570 i).reHi ∧
    (correctionCoefficientBox2570 i).imLo ≤ (actual i).im ∧
    (actual i).im ≤ (correctionCoefficientBox2570 i).imHi
  change (exactCorrectionInterval2586 i).reLo ≤ (actual i).re ∧
    (actual i).re ≤ (exactCorrectionInterval2586 i).reHi ∧
    (exactCorrectionInterval2586 i).imLo ≤ (actual i).im ∧
    (actual i).im ≤ (exactCorrectionInterval2586 i).imHi at hactual
  constructor
  · exact le_trans hcontain.1 hactual.1
  constructor
  · exact le_trans hactual.2.1 hcontain.2.1
  constructor
  · exact le_trans hcontain.2.2.1 hactual.2.2.1
  · exact le_trans hactual.2.2.2 hcontain.2.2.2

end ConnesWeilRH.Dev
'''
    OUTPUT.write_text(text, encoding="utf-8", newline="\n")
    print(json.dumps({
        "record": 2586,
        "output": str(OUTPUT.relative_to(ROOT)),
        "repair_source_sha256": source_hash,
        "rows": len(rows),
    }, indent=2))


if __name__ == "__main__":
    main()
