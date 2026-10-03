"""Generate actual second-derivative error certificates at cell 5440 midpoint."""
import argparse
from fractions import Fraction as Q
import json
import textwrap

from generate_complex_exp_node_2541 import ROOT, CAPTURE, real
from generate_compact_replay_2542 import pair
from routea_exp_schedule_probe_2542 import evaluate, R, STEP
from routea_derivative_pricing_2543 import multiplier


def render(count, *, order=2, grid_index=None):
    assert 0 <= order <= 4
    coordinate = Q(10881,2) if grid_index is None else Q(grid_index)
    x, sigma = -R+coordinate*STEP, Q(1,2)
    capture = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    parts = ["""import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

""", f"noncomputable def midpointPosition2543 : ℝ := {real(x)}\n\n"]
    for i in range(count):
        width, theta = (Q.from_float(float.fromhex(v)) for v in capture[i])
        assert abs(x) < width**2
        evaluation = evaluate(width**2,theta,x,sigma)
        z,k = evaluation["trace"][0],evaluation["depth"]
        factor = multiplier(order,width**2,theta,sigma,x)
        p = f"midpointP{i:03d}"
        parts.append(f"""def {p}Input2543 : RatPair2542 :=
  {pair(z)}

def {p}Center2543 : RatPair2542 :=
  {pair(evaluation['center'])}

noncomputable def {p}Error2543 : ℝ := {real(evaluation['error'])}

def {p}Factor2543 : RatPair2542 :=
  {pair(factor)}

theorem {p}BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨{i}, by omega⟩ midpointPosition2543 -
      embedPair2542 {p}Center2543‖ ≤ {p}Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨{i}, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 {p}Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, {p}Input2543]
  have hc : (compactExp2542 {p}Input2543 {k}).1 = {p}Center2543 := by cbv
  have he : ((compactExp2542 {p}Input2543 {k}).2 : ℝ) = {p}Error2543 := by
    have hq : (compactExp2542 {p}Input2543 {k}).2 =
        {real(evaluation['error']).replace('ℝ','ℚ')} := by cbv
    rw [hq]
    norm_num [{p}Error2543]
  have h := compactExp_error2542 {p}Input2543 hz {k}
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨{i}, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^{k} * embedPair2542 {p}Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, {p}Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem {p}DerivativeError2543 :
    ‖weightedUnitJet2539 {order} (1/2) nodeModulation2541 ⟨{i}, by omega⟩ midpointPosition2543 -
      embedPair2542 {p}Factor2543 * embedPair2542 {p}Center2543‖ ≤
      (pairMagnitude2542 {p}Factor2543 : ℝ) * {p}Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨{i}, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 {order} (1/2) (nodeModulation2541 ⟨{i}, by omega⟩)
      (storedWidth ⟨{i}, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 {p}Factor2543 := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542, {p}Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 {order} (by omega) (1/2)
    (nodeModulation2541 ⟨{i}, by omega⟩) (pow_pos (storedWidth_pos ⟨{i}, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv {order} _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ {p}BaseError2543
    (embedPair_magnitude2542 {p}Factor2543)

""")
    grid_proof = """theorem midpoint_grid2543 :
    (-stripRadius2303 + (5440 : ℝ)*(2*stripRadius2303/10240) +
      (-stripRadius2303 + (5441 : ℝ)*(2*stripRadius2303/10240)))/2 =
        midpointPosition2543 := by
  norm_num [stripRadius2303, midpointPosition2543]

end ConnesWeilRH.Dev

"""
    if grid_index is not None:
        grid_proof = f"""theorem midpoint_grid2543 :
    -stripRadius2303 + ({grid_index} : ℝ)*(2*stripRadius2303/10240) = midpointPosition2543 := by
  norm_num [stripRadius2303, midpointPosition2543]

end ConnesWeilRH.Dev

"""
    parts.append(grid_proof)
    parts.extend(f"#print axioms ConnesWeilRH.Dev.midpointP{i:03d}DerivativeError2543\n" for i in range(count))
    lines = []
    for line in "".join(parts).splitlines():
        indent = len(line)-len(line.lstrip())
        lines.extend(textwrap.wrap(line,width=98,subsequent_indent=" "*(indent+4),
                                   break_long_words=False,break_on_hyphens=False) or [""])
    return "\n".join(lines)+"\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--count",type=int,choices=range(1,31),default=30)
    args = parser.parse_args()
    path = ROOT/"ConnesWeilRH/Dev/C1RouteAMidpointDerivatives2543.lean"
    path.write_text(render(args.count),encoding="utf-8",newline="\n")
    print("GENERATED_MIDPOINT_DERIVATIVES",args.count,flush=True)
