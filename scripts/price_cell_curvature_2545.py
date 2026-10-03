"""Price the remaining cell arithmetic from the exported rational bounds.

This is exact arithmetic planning, not a Lean aggregate certificate.
The decision is whether the already chosen precision remains inexpensive
after multiplying by the same owner's actual coefficient magnitudes.
"""
from fractions import Fraction as Q
import hashlib
import json

from generate_complex_exp_node_2541 import ROOT
from validate_adaptive_nodes_2542 import scalar_def


def main():
    paths = [ROOT/f"ConnesWeilRH/Dev/C1RouteAEndpoint{s}Norms2544.lean"
             for s in ("Left","Right")]
    paths += [ROOT/"ConnesWeilRH/Dev/C1RouteAFourthEnvelope2545.lean",
              ROOT/"results/2338_exact_interpolation_repair.json"]
    left,right,fourth = (p.read_text() for p in paths[:3])
    rows = json.loads(paths[3].read_text())["coefficient_rows"]
    h = Q(65536001,51200000000)
    endpoint_charge = fourth_charge = Q(0)
    for i,row in enumerate(rows):
        coefficient = [(Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                        Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2
                       for p in ("real","imag")]
        magnitude = sum(abs(v) for v in coefficient)+Q(1,10**30)
        endpoint = max(scalar_def(left,f"endpointLeftP{i:03d}NormUpper2544"),
                       scalar_def(right,f"endpointRightP{i:03d}NormUpper2544"))
        envelope = scalar_def(fourth,f"fourthP{i:03d}Upper2545")
        endpoint_charge += magnitude*endpoint
        fourth_charge += magnitude*envelope*h/2
    midpoint = Q(997840737,400000)
    curvature = midpoint+(endpoint_charge+fourth_charge)*h/2
    result = dict(record=2545,scope="exact rational planning; no Lean aggregate claim",
                  cell=5440,sigma="1/2",families=len(rows),
                  source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in paths},
                  whole_cell_certificate=False,rh_claim=False)
    for name,v in (("endpoint_third_charge",endpoint_charge),("fourth_variation_charge",fourth_charge),
                   ("curvature_upper",curvature),("integral_curvature_charge",curvature*h**3/12)):
        result[name] = str(v)
        result[name+"_display"] = float(v)
    (ROOT/"results/2545_cell_curvature_price.json").write_text(json.dumps(result,indent=2)+"\n")
    print({k:v for k,v in result.items() if k.endswith("_display")},flush=True)


if __name__ == "__main__":
    main()
