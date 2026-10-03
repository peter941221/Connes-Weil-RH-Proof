"""Certify concrete endpoint third-derivative norms without splitting channels."""
import argparse
from fractions import Fraction as Q
from math import isqrt
import textwrap

from generate_complex_exp_node_2541 import ROOT, real, mul
from validate_compact_replay_2542 import value
from validate_adaptive_nodes_2542 import scalar_def


def render(side,count):
    source = (ROOT/f"ConnesWeilRH/Dev/C1RouteAEndpoint{side}Third2544.lean").read_text()
    parts = [f"""import ConnesWeilRH.Dev.C1RouteAEndpoint{side}Third2544
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

"""]
    for i in range(count):
        p = f"endpoint{side}P{i:03d}"
        factor,center = value(source,p+"Factor2544"),value(source,p+"Center2544")
        error = scalar_def(source,p+"Error2544")
        product = mul(factor,center)
        square = sum(v*v for v in product)
        scale = 2**100
        center_bound = Q(isqrt(square.numerator*scale**2//square.denominator)+1,scale)
        needed = center_bound+sum(abs(v) for v in factor)*error
        scaled = needed*scale
        upper = Q(-((-scaled.numerator)//scaled.denominator),scale)
        assert center_bound**2 >= square and upper >= needed
        parts.append(f"""noncomputable def {p}NormUpper2544 : ℝ := {real(upper)}

theorem {p}NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨{i}, by omega⟩ endpoint{side}Position2544‖ ≤
      {p}NormUpper2544 := by
  have hc : ‖embedPair2542 {p}Factor2544 * embedPair2542 {p}Center2544‖ ≤
      {real(center_bound)} := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, {p}Factor2544, {p}Center2544, Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨{i}, by omega⟩ endpoint{side}Position2544)
    (embedPair2542 {p}Factor2544 * embedPair2542 {p}Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add {p}DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, {p}Factor2544, {p}Error2544, {p}NormUpper2544]

""")
    if count == 30:
        name = f"endpoint{side}NormUpper2544"
        parts.append(f"noncomputable def {name} (i : Fin 30) : ℝ :=\n  match i.val with\n")
        parts.extend(f"  | {i} => endpoint{side}P{i:03d}NormUpper2544\n" for i in range(30))
        parts.append("  | _ => 0\n\n")
        parts.append(f"""theorem endpoint{side}NormBound2544 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i endpoint{side}Position2544‖ ≤ {name} i := by
  fin_cases i
""")
        parts.extend(f"  · exact endpoint{side}P{i:03d}NormBound2544\n" for i in range(30))
    parts.append("\nend ConnesWeilRH.Dev\n\n")
    parts.extend(f"#print axioms ConnesWeilRH.Dev.endpoint{side}P{i:03d}NormBound2544\n" for i in range(count))
    lines = []
    for line in "".join(parts).splitlines():
        indent = len(line)-len(line.lstrip())
        lines.extend(textwrap.wrap(line,width=98,subsequent_indent=" "*(indent+4),
                                   break_long_words=False,break_on_hyphens=False) or [""])
    return "\n".join(lines)+"\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--side",choices=("Left","Right"),required=True)
    parser.add_argument("--count",type=int,choices=range(1,31),default=30)
    args = parser.parse_args()
    path = ROOT/f"ConnesWeilRH/Dev/C1RouteAEndpoint{args.side}Norms2544.lean"
    path.write_text(render(args.side,args.count),encoding="utf-8",newline="\n")
    print("ENDPOINT_NORM_GENERATED",args.side,args.count,flush=True)
