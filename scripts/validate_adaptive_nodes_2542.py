"""Independently replay adaptive arithmetic and signed sums from Lean literals."""
from fractions import Fraction as Q
import hashlib
import json
import re

from generate_complex_exp_node_2541 import ROOT, CAPTURE
from validate_compact_replay_2542 import value
from validate_center_node_2540 import exact_expression
from validate_nonzero_node_2541 import complex_value, definition, multiply


def scalar_def(source, name):
    return exact_expression(definition(source, name).split(":=", 1)[1])


def check(source, index, sign):
    prefix = f"adaptiveN{index:05d}{'Plus' if sign > 0 else 'Minus'}"
    position = scalar_def(source, prefix+"Position2542")
    assert position == -Q(65536001,10**7) + index*Q(65536001,51200000000)
    capture = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    coeffs = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    total, charge, depths, active = (Q(0),Q(0)), Q(0), [], 0
    delta = Q(1,2**99)
    for i, (raw, coeff) in enumerate(zip(capture, coeffs)):
        p = f"{prefix}P{i:03d}"
        width, theta = (Q.from_float(float.fromhex(v)) for v in raw)
        output, error = value(source, p+"Output2542")
        if abs(position) >= width**2:
            assert (output,error) == ((0,0),0)
            continue
        active += 1
        z = value(source, p+"Input2542")
        match = re.search(r"theorem " + p + r"Compute2542\b.*?compactExp2542\s+" +
                          p + r"Input2542\s+(\d+)\s*=", source, re.S)
        assert match
        k = int(match[1])
        depths.append(k)
        expected = ((Q(sign,2)*position-30/(1-(position/width**2)**2))/2**k,
                    theta*position/2**k)
        assert z == expected and abs(z[0])+abs(z[1]) <= 1
        h = (Q(1),Q(0))
        def down(q):
            return Q((q*2**100).numerator//(q*2**100).denominator,2**100)
        for d in range(19,0,-1):
            product = multiply(z,h)
            h = (down(1+product[0]/d), down(product[1]/d))
        e = Q(1,10**18)+19*delta
        for _ in range(k):
            bound = (e*(2*(abs(h[0])+abs(h[1]))+e)+delta)*2**140
            e = Q(-((-bound.numerator)//bound.denominator),2**140)
            h = tuple(down(q) for q in multiply(h,h))
        assert (h,e) == (output,error), (i,"computed output")
        c = tuple((Q(coeff["ideal_base_coefficient"][part]["lower_exact"])+
                   Q(coeff["ideal_base_coefficient"][part]["upper_exact"]))/2
                  for part in ("real","imag"))
        term = multiply(c,h)
        total = tuple(a+b for a,b in zip(total,term))
        charge += sum(abs(q) for q in c)*e
    stored = complex_value(definition(source,prefix+"SumValue2542").split(":=",1)[1])
    assert stored == total
    upper = scalar_def(source,prefix+"Upper2542")
    assert sum(q*q for q in total) <= (upper-Q(1,10**10))**2
    assert charge+Q(30,10**30) <= Q(1,10**10) and charge <= Q(1,10**12)
    return dict(index=index,sign=sign,position=str(position),active_families=active,
                max_depth=max(depths,default=0),signed_upper=str(upper),
                evaluation_charge=str(charge))


if __name__ == "__main__":
    reports = []
    for path in sorted((ROOT/"ConnesWeilRH/Dev").glob("C1RouteAAdaptiveN*2542.lean")):
        match = re.fullmatch(r"C1RouteAAdaptiveN(\d+)(Plus|Minus)2542.lean",path.name)
        assert match
        index,sign = int(match[1]), 1 if match[2] == "Plus" else -1
        source = path.read_text()
        result = check(source,index,sign)
        active = re.search(r"theorem (adaptive\w+P\d{3})Compute2542", source)
        assert active
        mutated = re.sub(r"(def " + active[1] + r"Output2542\b.*?:=).*?(?=\n\n)",
                         r"\1 ((0, 0), 0)", source, count=1, flags=re.S)
        assert mutated != source
        try:
            check(mutated,index,sign)
        except AssertionError:
            result["zeroed_active_output_rejected"] = True
        else:
            raise AssertionError("Corrupted active output accepted")
        result["source_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        reports.append(result)
    assert reports
    out = dict(record=2542,scope="independent exact arithmetic, Lean acceptance separate",
               cases=reports,full_grid_certificate=False,exact_owner_transfer=False,
               producer_go=False,rh_claim=False)
    (ROOT/"results/2542_adaptive_node_readback.json").write_text(json.dumps(out,indent=2)+"\n")
    print("ADAPTIVE_LITERAL_READBACK_PASS",len(reports),"cases",flush=True)
