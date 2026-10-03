"""Price direct versus analytically capped coupled fourth envelopes.

Decision: can the compact exponential's positive rounding floor be used
directly in the cell-2700 fourth envelope under a 1e-8 local contribution?
The capped expression needs a separate Lean transfer theorem before use.
"""
from fractions import Fraction as Q
from math import comb,isqrt
import hashlib
import json
from pathlib import Path

from generate_complex_exp_node_2541 import ROOT,CAPTURE
from generate_fourth_envelope_2545 import polynomial
from price_boundary_precision_2547 import precision_evaluate
from routea_exp_schedule_probe_2542 import R,STEP


def main():
    a,b = -R+2700*STEP,-R+2701*STEP
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    repair = ROOT/"results/2338_exact_interpolation_repair.json"
    coeffs = json.loads(repair.read_text())["coefficient_rows"]
    totals = {"direct":Q(0),"capped":Q(0)}
    rows = []
    for i,(values,row) in enumerate(zip(raw,coeffs)):
        width,theta = (Q.from_float(float.fromhex(v)) for v in values)
        radius = width**2
        near,far = min(abs(a),abs(b))/radius,min(max(abs(a),abs(b)),radius)/radius
        if near >= 1:
            rows.append(dict(family=i,exterior=True))
            continue
        t = 1/(1-near**2)
        sq = Q(1,4)+theta**2
        frequency = Q(isqrt(sq.numerator*2**80//sq.denominator)+1,2**40)
        magnitude = sum(abs((Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                            Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2)
                        for p in ("real","imag"))+Q(1,10**30)
        entry = dict(family=i,exterior=False,inverse_deficit=str(t),crossing=far==1)
        for method,tref in (("direct",t),("capped",min(t,Q(4)))):
            exponent = b/2-30*tref
            # Synthetic scalar input realizes exactly this real exponent:
            # x=1/2, radius=1 gives bump exponent -40; imaginary part is zero.
            center,error,_ = precision_evaluate(Q(1),Q(0),Q(1,2),2*(exponent+40),160)
            expupper = sum(abs(v) for v in center)+error
            poly = sum(comb(4,j)*frequency**j*polynomial(4-j,far)*
                       tref**(2*(4-j))/radius**(4-j) for j in range(5))
            charge = magnitude*expupper*poly*STEP**5/48
            totals[method] += charge
            entry[method+"_display"] = float(charge)
        rows.append(entry)
    result = dict(record=2548,scope="cell2700 sigma+1/2 fourth contribution planning only",
                  allowance="1/100000000",cap="4",rows=rows,
                  transfer_lemma_candidate="powerExp_le_at_lower2536 for orders 0..8 and decay30",
                  capped_lean_transfer=False,whole_cell_certificate=False,rh_claim=False,
                  source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in (Path(__file__),CAPTURE,repair,
                                           ROOT/"scripts/generate_fourth_envelope_2545.py",
                                           ROOT/"scripts/price_boundary_precision_2547.py")})
    for method,v in totals.items():
        s = v*2**160
        exported = Q(-((-s.numerator)//s.denominator),2**160)
        assert (v<=Q(1,10**8)) == (exported<=Q(1,10**8))
        result[method] = dict(charge_upper=str(exported),display=float(exported),
                              allowance_pass=exported<=Q(1,10**8))
    (ROOT/"results/2548_boundary_fourth_price.json").write_text(json.dumps(result,indent=2)+"\n")
    print("BOUNDARY_FOURTH_PRICE",result["direct"],result["capped"],flush=True)


if __name__ == "__main__":
    main()
