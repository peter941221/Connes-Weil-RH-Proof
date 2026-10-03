"""Read second-derivative factors using independent logarithmic differentiation."""
from fractions import Fraction as Q
import argparse
import hashlib
import json
from pathlib import Path
import re

from generate_complex_exp_node_2541 import ROOT, CAPTURE
from validate_compact_replay_2542 import value
from validate_adaptive_nodes_2542 import scalar_def
from validate_nonzero_node_2541 import multiply, complex_value, definition


def check(source):
    position = scalar_def(source,"midpointPosition2543")
    assert position == -Q(65536001,10**7)+Q(10881,2)*Q(65536001,51200000000)
    names = re.findall(r"def (midpointP\d{3})Input2543",source)
    assert names == [f"midpointP{i:03d}" for i in range(len(names))] and names
    capture = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    for i,name in enumerate(names):
        width,theta = (Q.from_float(float.fromhex(v)) for v in capture[i])
        radius = width**2
        assert abs(position) < radius
        q = 1-(position/radius)**2
        log_first = (Q(1,2)-60*position/(radius**2*q**2),theta)
        log_second = -60/(radius**2*q**2)-240*position**2/(radius**4*q**3)
        squared = multiply(log_first,log_first)
        factor = value(source,name+"Factor2543")
        assert factor == (squared[0]+log_second,squared[1]), (name,"factor")
        depth = int(re.search(r"compactExp2542\s+"+name+r"Input2543\s+(\d+)",source)[1])
        z = value(source,name+"Input2543")
        assert z == ((position/2-30/q)/2**depth,theta*position/2**depth)
        assert abs(z[0])+abs(z[1]) <= 1
        center, error = (Q(1),Q(0)), Q(1,10**18)+19*Q(1,2**99)
        def down(v):
            scaled = v*2**100
            return Q(scaled.numerator//scaled.denominator,2**100)
        for denominator in range(19,0,-1):
            product = multiply(z,center)
            center = (down(1+product[0]/denominator),down(product[1]/denominator))
        for _ in range(depth):
            scaled = (error*(2*sum(abs(v) for v in center)+error)+Q(1,2**99))*2**140
            error = Q(-((-scaled.numerator)//scaled.denominator),2**140)
            center = tuple(down(v) for v in multiply(center,center))
        assert center == value(source,name+"Center2543")
        assert error == scalar_def(source,name+"Error2543")
    return len(names)


def check_signed(source, base):
    coefficients = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    total,charge = (Q(0),Q(0)),Q(0)
    for i in range(30):
        name = f"midpointP{i:03d}"
        factor = value(base,name+"Factor2543")
        center = value(base,name+"Center2543")
        error = scalar_def(base,name+"Error2543")
        exact = multiply(factor,center)
        rounded = value(source,name+"Rounded2543")
        for a,b in zip(exact,rounded):
            scaled = a*2**100
            assert b == Q(scaled.numerator//scaled.denominator,2**100)
        radius = scalar_def(source,name+"Radius2543")
        needed = sum(abs(v) for v in factor)*error+Q(1,2**99)
        scaled = needed*2**140
        assert radius == Q(-((-scaled.numerator)//scaled.denominator),2**140)
        assert radius+sum(abs(v) for v in rounded) <= 1
        coeff = tuple((Q(coefficients[i]["ideal_base_coefficient"][p]["lower_exact"])+
                       Q(coefficients[i]["ideal_base_coefficient"][p]["upper_exact"]))/2
                      for p in ("real","imag"))
        product = multiply(coeff,rounded)
        total = tuple(a+b for a,b in zip(total,product))
        charge += sum(abs(v) for v in coeff)*radius
    assert complex_value(definition(source,"signedMidpointSum2543").split(":=",1)[1]) == total
    upper = scalar_def(source,"signedMidpointUpper2543")
    assert upper > Q(1,10**7)
    assert sum(v*v for v in total) <= (upper-Q(1,10**7))**2
    assert charge <= Q(1,10**8) and charge+Q(30,10**30) <= Q(1,10**7)
    return dict(signed_upper=str(upper),evaluation_charge=str(charge),
                evaluation_charge_display=float(charge))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    parser.add_argument("--signed",action="store_true")
    args = parser.parse_args()
    path = ROOT/"ConnesWeilRH/Dev/C1RouteAMidpointDerivatives2543.lean"
    source = path.read_text()
    count = check(source)
    mutated = re.sub(r"(def midpointP000Factor2543\b.*?:=).*?(?=\n\n)",
                     r"\1 (0, 0)",source,count=1,flags=re.S)
    try:
        check(mutated)
    except AssertionError:
        rejected = True
    else:
        raise AssertionError("Corrupted multiplier was accepted")
    result = dict(record=2543,scope="exact midpoint arithmetic; Lean acceptance separate",
                  families_checked=count,independent_factor_method="logarithmic differentiation",
                  corrupted_factor_rejected=rejected,
                  source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  signed_aggregate_certificate=False,full_grid_certificate=False,
                  producer_go=False,rh_claim=False)
    if args.signed:
        signed_path = ROOT/"ConnesWeilRH/Dev/C1RouteASignedMidpoint2543.lean"
        signed_source = signed_path.read_text()
        result["signed_arithmetic"] = check_signed(signed_source,source)
        mutated_radius = re.sub(r"(noncomputable def midpointP000Radius2543\b.*?:=).*?(?=\n\n)",
                                r"\1 (0 : ℝ)",signed_source,count=1,flags=re.S)
        try:
            check_signed(mutated_radius,source)
        except AssertionError:
            result["zeroed_radius_rejected"] = True
        else:
            raise AssertionError("Zeroed derivative radius accepted")
        mutated_center = re.sub(r"(def midpointP000Rounded2543\b.*?:=).*?(?=\n\n)",
                                r"\1 (0, 0)",signed_source,count=1,flags=re.S)
        assert mutated_center != signed_source
        try:
            check_signed(mutated_center,source)
        except AssertionError:
            result["changed_rounded_center_rejected"] = True
        else:
            raise AssertionError("Corrupted rounded derivative center accepted")
    if args.log:
        assert args.mirror
        from generate_midpoint_derivatives_2543 import render
        assert count == 30 and source == render(30)
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:",log,re.M)
        assert not re.search(r"^warning: .*2543\.lean:",log,re.M)
        expected = {f"midpointP{i:03d}DerivativeError2543" for i in range(30)} | {
            "widthBump_inside_factor2543", "weightedFamily_inside_factor2543",
            "weightedFamily_outside_zero2543", "complex_multiplier_error2543", "midpoint_grid2543"}
        if args.signed:
            from generate_signed_midpoint_2543 import render as render_signed
            assert signed_source == render_signed()[0]
            expected.update({"signedMidpointExpError2543", "signedMidpointSum_eq2543",
                             "signedMidpointCharge2543", "signedMidpointUpper_le2543",
                             "weightedPhysical_second_midpoint_le2543"})
        matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2543)' depends on axioms:\s*\[([^]]*)\]",log)
        reports = {name:[v.strip() for v in axioms.split(",")] for name,axioms in matches}
        assert set(reports) == expected
        assert all(v == ["propext","Classical.choice","Quot.sound"] for v in reports.values())
        pending, hashes = ["ConnesWeilRH", "ConnesWeilRH.Dev.C1RouteAMidpointDerivatives2543Audit"], {}
        if args.signed:
            pending.append("ConnesWeilRH.Dev.C1RouteASignedMidpoint2543")
        while pending:
            relative = pending.pop().replace(".","/")+".lean"
            if relative in hashes:
                continue
            data = (ROOT/relative).read_bytes()
            assert data == (args.mirror/relative).read_bytes(),relative
            hashes[relative] = hashlib.sha256(data).hexdigest()
            for line in data.decode("utf-8-sig").splitlines():
                if line.startswith("import "):
                    pending.extend(v for v in line[7:].split() if v.startswith("ConnesWeilRH"))
        for name in ("lean-toolchain","lake-manifest.json","lakefile.toml"):
            assert (ROOT/name).read_bytes() == (args.mirror/name).read_bytes(),name
        result.update(status="BUILD_AXIOM_SOURCE_DERIVATIVE_IDENTITY_PASS",audits=reports,
                      build_footer=footers[-1],project_sources_checked=len(hashes),
                      project_source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
        result["signed_aggregate_certificate"] = args.signed
    (ROOT/"results/2543_midpoint_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print("MIDPOINT_READBACK_PASS",count,flush=True)
