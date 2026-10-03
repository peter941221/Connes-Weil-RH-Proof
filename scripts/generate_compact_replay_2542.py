"""Emit exact 30-family replay against the accepted 2541 outputs."""
from pathlib import Path

from generate_complex_exp_node_2541 import integer, witness

ROOT = Path(__file__).resolve().parents[1]
HEADER = """import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

"""


def rational(q):
    return f"(({integer(q.numerator)} : ℚ) /\n        {integer(q.denominator)})"


def pair(z):
    return f"({rational(z[0])},\n    {rational(z[1])})"


def render():
    parts = [HEADER]
    for i in range(30):
        z, _, squares, errors, _ = witness(i)
        tag = f"P{i:03d}"
        inp, out = f"compactInput{tag}2542", f"compactOutput{tag}2542"
        replay = f"compactReplay{tag}2542"
        parts.append(f"""def {inp} : RatPair2542 :=
  {pair(z)}

def {out} : RatState2542 :=
  ({pair(squares[-1])},\n    {rational(errors[-1])})

theorem {replay} : compactExp2542 {inp} 6 = {out} := by
  cbv

theorem compactError{tag}2542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZ{tag}2541) - nodeS{tag}2541 6‖ ≤
      nodeE{tag}2541 6 := by
  have hz : ‖embedPair2542 {inp}‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, {inp}]
  have h := compactExp_error2542 {inp} hz 6
  rw [{replay}] at h
  convert h using 1 <;> norm_num [embedPair2542, {inp}, {out},
    nodeZ{tag}2541, nodeS{tag}2541, nodeE{tag}2541]

""")
    parts.append("end ConnesWeilRH.Dev\n")
    for i in range(30):
        parts.append(f"#print axioms ConnesWeilRH.Dev.compactErrorP{i:03d}2542\n")
    return "".join(parts)


def render_consumer():
    source = (ROOT / "ConnesWeilRH/Dev/C1RouteANonzeroNode2541.lean").read_text()
    start = source.index("theorem signedJet_nonzero_le2541")
    end = source.index("theorem production_grid_nonzero2541", start)
    body = source[start:end].replace("nodeExp_error2541", "compactNodeError2542")
    body = body.replace("signedJet_nonzero_le2541", "signedJet_compact_le2542")
    body = body.replace("weightedPhysical_nonzero_le2541", "weightedPhysical_compact_le2542")
    parts = ["""import ConnesWeilRH.Dev.C1RouteACompactExpBatch2542

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem compactNodeError2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541 -
      nodeValue2541 i‖ ≤ nodeError2541 i := by
  rw [nodeUnit_eq2541]
  fin_cases i
"""]
    for i in range(30):
        parts.append("  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using\n"
                     f"      compactErrorP{i:03d}2542\n")
    parts.extend(["\n", body, "end ConnesWeilRH.Dev\n\n"])
    for name in ("compactNodeError2542", "signedJet_compact_le2542", "weightedPhysical_compact_le2542"):
        parts.append(f"#print axioms ConnesWeilRH.Dev.{name}\n")
    return "".join(parts)


if __name__ == "__main__":
    target = ROOT / "ConnesWeilRH/Dev/C1RouteACompactExpBatch2542.lean"
    target.write_text(render(), encoding="utf-8", newline="\n")
    baseline = ROOT / "ConnesWeilRH/Dev/C1RouteACompactExpBaseline2542.lean"
    baseline.write_text(HEADER + "end ConnesWeilRH.Dev\n", encoding="utf-8", newline="\n")
    consumer = ROOT / "ConnesWeilRH/Dev/C1RouteACompactNode2542.lean"
    consumer.write_text(render_consumer(), encoding="utf-8", newline="\n")
    print(f"Generated {target.name}: {target.stat().st_size} bytes", flush=True)
