"""Certify the unchanged fourth envelope across the support boundary."""
import argparse
from fractions import Fraction as Q
import json
import re

from generate_complex_exp_node_2541 import ROOT,CAPTURE
from generate_fourth_envelope_2545 import render as template
from generate_boundary_bounds_2549 import wrap
from routea_exp_schedule_probe_2542 import R,STEP


def render(*, smoke=False, cell_index=2700, sigma=Q(1,2)):
    a,b = -R+cell_index*STEP,-R+(cell_index+1)*STEP
    assert a*b >= 0
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    active = [i for i,v in enumerate(raw) if min(abs(a),abs(b)) < Q.from_float(float.fromhex(v[0]))**2]
    selected = active[:1] if smoke else active
    out,rows = template(len(selected),cell_index=cell_index,indices=selected,precision=160,sigma=sigma)
    out = out.replace("import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545",
        "import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545\n"
        "import ConnesWeilRH.Dev.C1RouteACompactExp1602547\n"
        "import ConnesWeilRH.Dev.C1RouteABoundaryLeft2548\n"
        "import ConnesWeilRH.Dev.C1RouteABoundaryRight2548")
    out = out.replace("fourthCellTerm2544","edgeFourthCell2550")
    out = out.replace("endpointLeftPosition2544","edgeLeftPosition2548")
    out = out.replace("endpointRightPosition2544","edgeRightPosition2548")
    out = re.sub(r"\bfourth(P\d{3}\w*)2545\b",lambda m:"edgeFourth"+m[1]+"2550",out)
    definition = """
noncomputable def edgeFourthCell2550 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 edgeLeftPosition2548 edgeRightPosition2548 < storedWidth i ^ 2 then
    weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 edgeLeftPosition2548 edgeRightPosition2548 / (storedWidth i ^ 2))
      (min (max |edgeLeftPosition2548| |edgeRightPosition2548|) (storedWidth i ^ 2) /
        (storedWidth i ^ 2)) edgeLeftPosition2548 edgeRightPosition2548
  else 0

"""
    if sigma < 0:
        definition = definition.replace("(1/2)","(-1/2)")
    out = out.replace("open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit\n",
                      "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit\n"+definition)
    if selected == list(range(30)):
        out = re.sub(r"\bfourth(Upper|Bound)2545\b",lambda m:"edgeFourth"+m[1]+"2550",out)
        return wrap(out),rows
    if not smoke:
        extra = []
        for i in range(30):
            if i in active:
                continue
            extra.append(f"""noncomputable def edgeFourthP{i:03d}Upper2550 : ℝ := 0

theorem edgeFourthP{i:03d}Bound2550 :
    edgeFourthCell2550 ⟨{i}, by omega⟩ ≤ edgeFourthP{i:03d}Upper2550 := by
  norm_num [edgeFourthCell2550, edgeFourthP{i:03d}Upper2550, cellNearAbs2538,
    edgeLeftPosition2548, edgeRightPosition2548, storedWidth]

""")
        extra.append("noncomputable def edgeFourthUpper2550 (i : Fin 30) : ℝ :=\n  match i.val with\n")
        extra.extend(f"  | {i} => edgeFourthP{i:03d}Upper2550\n" for i in range(30))
        extra.append("  | _ => 0\n\n")
        extra.append("theorem edgeFourthBound2550 (i : Fin 30) :\n"
                     "    edgeFourthCell2550 i ≤ edgeFourthUpper2550 i := by\n  fin_cases i\n")
        extra.extend(f"  · exact edgeFourthP{i:03d}Bound2550\n" for i in range(30))
        out = out.replace("end ConnesWeilRH.Dev","".join(extra)+"\nend ConnesWeilRH.Dev")
        out += "#print axioms ConnesWeilRH.Dev.edgeFourthBound2550\n"
        out += "".join(f"#print axioms ConnesWeilRH.Dev.edgeFourthP{i:03d}Bound2550\n"
                       for i in range(30) if i not in active)
    return wrap(out),rows


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--smoke",action="store_true")
    args = parser.parse_args()
    assert template(30)[0] == (ROOT/"ConnesWeilRH/Dev/C1RouteAFourthEnvelope2545.lean").read_text()
    source,rows = render(smoke=args.smoke)
    (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryFourth2550.lean").write_text(source,encoding="utf-8",newline="\n")
    print("BOUNDARY_FOURTH_GENERATED",len(rows),flush=True)
