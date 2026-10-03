"""Generate all same-owner jets at the endpoints/midpoint of cell 2700."""
import argparse
from fractions import Fraction as Q
import json
import re
import textwrap

from generate_complex_exp_node_2541 import ROOT, CAPTURE, real
from generate_boundary_replay_2547 import render as render_one
from routea_exp_schedule_probe_2542 import R, STEP


CASES = {"Left":(Q(2700),3),"Right":(Q(2701),3),"Midpoint":(Q(5401,2),2)}


def render(side, *, grid_order=None, sigma=Q(1,2), paired=False):
    grid,order = CASES[side] if grid_order is None else grid_order
    assert sigma in (Q(1,2), Q(-1,2))
    sigma_lean = "(1/2)" if sigma == Q(1,2) else "(-1/2)"
    x = -R+grid*STEP
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    parts = ["""import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

""",f"""noncomputable def edge{side}Position2548 : ℝ := {real(x)}

theorem edge{side}Zero2548 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

"""]
    active = []
    for i,values in enumerate(raw):
        width,theta = (Q.from_float(float.fromhex(v)) for v in values)
        p = f"edge{side}P{i:03d}"
        if abs(x) < width**2:
            source,_ = render_one(grid_index=grid,family_index=i,order=order,sigma=sigma,paired=paired)
            source = source[source.index("noncomputable def boundaryPosition2547"):source.index("end ConnesWeilRH.Dev")]
            source = re.sub(r"\bboundary(\w*)2547\b",lambda m:p+m[1]+"2548",source)
            source = source.replace(p+"ThirdError2548",p+"DerivativeError2548")
            source = re.sub(r"noncomputable def "+p+r"Position2548.*?(?=\n\n)","",source,flags=re.S)
            source = source.replace(p+"Position2548",f"edge{side}Position2548")
            parts.append(source.lstrip())
            active.append(i)
        else:
            parts.append(f"""def {p}Center2548 : RatPair2542 := (0, 0)

def {p}Factor2548 : RatPair2542 := (0, 0)

noncomputable def {p}Error2548 : ℝ := 0

theorem {p}Exterior2548 (n : ℕ) :
    weightedUnitJet2539 n {sigma_lean} nodeModulation2541 ⟨{i}, by omega⟩ edge{side}Position2548 = 0 := by
  have hx : storedWidth ⟨{i}, by omega⟩ ^ 2 ≤ |edge{side}Position2548| := by
    norm_num [storedWidth, edge{side}Position2548]
  exact weightedFamily_outside_zero2543 n {sigma_lean} (nodeModulation2541 ⟨{i}, by omega⟩)
    (pow_pos (storedWidth_pos ⟨{i}, by omega⟩) 2) hx

theorem {p}BaseError2548 :
    ‖weightedUnitJet2539 0 {sigma_lean} nodeModulation2541 ⟨{i}, by omega⟩ edge{side}Position2548 -
      embedPair2542 {p}Center2548‖ ≤ {p}Error2548 := by
  rw [{p}Exterior2548]
  norm_num [{p}Center2548, {p}Error2548, edge{side}Zero2548]

theorem {p}DerivativeError2548 :
    ‖weightedUnitJet2539 {order} {sigma_lean} nodeModulation2541 ⟨{i}, by omega⟩ edge{side}Position2548 -
      embedPair2542 {p}Factor2548 * embedPair2542 {p}Center2548‖ ≤
        (pairMagnitude2542 {p}Factor2548 : ℝ) * {p}Error2548 := by
  rw [{p}Exterior2548]
  norm_num [{p}Factor2548, {p}Center2548, {p}Error2548, edge{side}Zero2548, pairMagnitude2542]

""")
    parts.append(f"""theorem edge{side}Grid2548 :
    -stripRadius2303 + {real(grid)} * (2 * stripRadius2303 / 10240) =
      edge{side}Position2548 := by
  norm_num [stripRadius2303, edge{side}Position2548]

end ConnesWeilRH.Dev

""")
    parts.extend(f"#print axioms ConnesWeilRH.Dev.edge{side}P{i:03d}DerivativeError2548\n" for i in range(30))
    parts.append(f"#print axioms ConnesWeilRH.Dev.edge{side}Grid2548\n")
    lines = []
    for line in "".join(parts).splitlines():
        indent = len(line)-len(line.lstrip())
        lines.extend(textwrap.wrap(line,width=98,subsequent_indent=" "*(indent+4),
                                  break_long_words=False,break_on_hyphens=False) or [""])
    return "\n".join(lines)+"\n",active


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--side",choices=tuple(CASES),required=True)
    args = parser.parse_args()
    assert render_one()[0] == (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryReplay2547.lean").read_text()
    source,active = render(args.side)
    (ROOT/f"ConnesWeilRH/Dev/C1RouteABoundary{args.side}2548.lean").write_text(source,encoding="utf-8",newline="\n")
    print("BOUNDARY_JETS_GENERATED",args.side,"active",active,flush=True)
