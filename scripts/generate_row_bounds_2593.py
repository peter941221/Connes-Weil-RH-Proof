import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results/2351_moment_matrix_exact_check.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionRowBounds2593.lean"

def expr(value):
    f = Fraction(value)
    return f"(({f.numerator} : NNReal) / {f.denominator})"

def main():
    data = json.loads(SOURCE.read_text())
    rows = data["row_bounds_exact"]
    if len(rows) != 30:
        raise AssertionError(len(rows))
    values = ",\n    ".join(expr(row) for row in rows)
    text = f'''import ConnesWeilRH.Dev.C1RouteACorrectionOperatorNorm2590

/-! Exact rational row bounds exported by the independent 2351 Fraction check.
These bounds are imported as data only; the relation to the actual analytic
operator remains a separate premise. -/

namespace ConnesWeilRH.Dev

noncomputable def analyticDefectRowBounds2593 : Fin 30 → NNReal :=
  ![{values}]

theorem analyticDefectRowBounds2593_lt_one (i : Fin 30) :
    analyticDefectRowBounds2593 i < 1 := by
  fin_cases i <;> norm_num [analyticDefectRowBounds2593]

end ConnesWeilRH.Dev
'''
    OUTPUT.write_text(text, encoding="utf-8")
    print({"record": 2593, "rows": len(rows), "source": str(SOURCE.relative_to(ROOT))})

if __name__ == "__main__":
    main()