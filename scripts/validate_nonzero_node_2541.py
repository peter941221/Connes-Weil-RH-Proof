"""Audit the Lean proof and independently read its exact arithmetic witnesses."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re

from generate_complex_exp_node_2541 import render as render_family
from generate_nonzero_node_2541 import render as render_node
from validate_center_node_2540 import exact_expression

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["ConnesWeilRH.Dev.C1RouteANonzeroNode2541Audit", "ConnesWeilRH"]
EXPECTED = {
    "expHorner2541_error", "square_ball2541", "nodeUnit_eq2541",
    "nodeEvaluation_charge2541", "signedJet_nonzero_le2541", "weightedPhysical_nonzero_le2541",
} | {f"nodeExpP{i:03d}_error2541" for i in range(30)}


def definition(source, name):
    match = re.search(r"noncomputable def " + name + r"\b.*?(?=\n\n)", source, re.S)
    assert match, name
    return match.group(0)


def scalar(expression):
    return exact_expression(expression.replace("\n", " "))


def complex_value(expression):
    match = re.fullmatch(r"\s*⟨(.*?),(.*?)⟩\s*", expression, re.S)
    assert match, expression
    return scalar(match[1]), scalar(match[2])


def table(source, name, parse):
    body = definition(source, name)
    rows = re.findall(r"\| (\d+) =>(.*?)(?=\n  \|)", body, re.S)
    assert [int(i) for i,_ in rows] == list(range(len(rows)))
    return [parse(expr) for _,expr in rows]


def multiply(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def check_family(source, index, capture, node):
    tag = f"P{index:03d}2541"
    z = complex_value(definition(source, "nodeZ"+tag).split(":=", 1)[1])
    h = table(source, "nodeH"+tag, complex_value)
    s = table(source, "nodeS"+tag, complex_value)
    e = table(source, "nodeE"+tag, scalar)
    width, theta = (Q.from_float(float.fromhex(v)) for v in capture[index])
    assert abs(node) < width**2
    assert z == ((node/2-30/(1-(node/width**2)**2))/64, theta*node/64)
    assert abs(z[0])+abs(z[1]) <= 1
    assert len(h) == 20 and len(s) == len(e) == 7
    assert h[0] == (1,0) and s[0] == h[-1]
    rounding = Q(1,2**99)
    for n in range(19):
        product = multiply(z, h[n])
        expected = (1+product[0]/(19-n), product[1]/(19-n))
        assert sum(abs(a-b) for a,b in zip(expected,h[n+1])) <= rounding
    assert e[0] >= Q(1,10**18)+19*rounding
    assert all(radius >= 0 for radius in e)
    for k in range(6):
        squared = multiply(s[k], s[k])
        assert sum(abs(a-b) for a,b in zip(squared,s[k+1])) <= rounding
        magnitude = abs(s[k][0])+abs(s[k][1])
        assert e[k+1] >= e[k]*(2*magnitude+e[k])+rounding
    return s[-1], e[-1]


def check_payload():
    capture_path = ROOT/"results/2275_gap_owner_audit.json"
    repair_path = ROOT/"results/2338_exact_interpolation_repair.json"
    capture = json.loads(capture_path.read_text())["owner_capture"]["families_hex"]
    repair = json.loads(repair_path.read_text())
    assert repair["capture_sha256"] == hashlib.sha256(capture_path.read_bytes()).hexdigest()
    node_path = ROOT/"ConnesWeilRH/Dev/C1RouteANonzeroNode2541.lean"
    source = node_path.read_text(encoding="utf-8")
    assert source == render_node()
    node = scalar(definition(source, "nodePosition2541").split(":=",1)[1])
    assert node == -Q(65536001,10**7)+5121*2*Q(65536001,10**7)/10240
    modulations = table(source, "nodeModulation2541", scalar)
    assert modulations == [Q.from_float(float.fromhex(row[1])) for row in capture]
    total, charge, errors = (Q(0),Q(0)), Q(0), []
    witness_bytes = 0
    first_source = None
    for i,row in enumerate(repair["coefficient_rows"]):
        path = ROOT/f"ConnesWeilRH/Dev/C1RouteAExpNode2541P{i:03d}.lean"
        family_source = path.read_text(encoding="utf-8")
        witness_bytes += len(family_source.encode("utf-8"))
        assert family_source == render_family(i)
        value, error = check_family(family_source, i, capture, node)
        center = tuple((Q(row["ideal_base_coefficient"][part]["lower_exact"])+
                        Q(row["ideal_base_coefficient"][part]["upper_exact"]))/2
                       for part in ("real","imag"))
        weighted = multiply(center,value)
        total = (total[0]+weighted[0],total[1]+weighted[1])
        charge += (abs(center[0])+abs(center[1]))*error
        errors.append(error)
        if i == 0:
            first_source = family_source
    assert charge <= Q(1,10**12)
    assert complex_value(definition(source,"nodeSumValue2541").split(":=",1)[1]) == total
    upper = scalar(definition(source,"nodeUpper2541").split(":=",1)[1])
    available = upper-Q(1,10**12)-Q(30,10**30)
    assert available >= 0 and available**2 >= total[0]**2+total[1]**2
    mutations = [first_source.replace("(1 : ℝ)","(2 : ℝ)",1),
                 re.sub(r"(noncomputable def nodeEP0002541.*?\| 6 =>).*?(?=\n  \| _)",
                        r"\1 (0 : ℝ)",first_source,flags=re.S)]
    for changed in mutations:
        assert changed != first_source
        try:
            check_family(changed,0,capture,node)
        except AssertionError:
            pass
        else:
            raise AssertionError("corrupted numerical witness accepted")
    return dict(grid_index=5121, grid_cells=10240, node=str(node), sigma="1/2",
                signed_node_upper=str(upper), horner_steps_checked=570,
                square_steps_checked=180, family_inputs_checked=30,
                family_witness_source_bytes=witness_bytes,
                evaluation_charge_exact=str(charge), evaluation_charge_display=float(charge),
                final_family_error_min=str(min(errors)), final_family_error_max=str(max(errors)),
                changed_center_rejected=True, zeroed_radius_rejected=True,
                capture_sha256=hashlib.sha256(capture_path.read_bytes()).hexdigest(),
                coefficient_source_sha256=hashlib.sha256(repair_path.read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror",type=Path,required=True)
    parser.add_argument("--log",type=Path,required=True)
    args = parser.parse_args()
    payload = check_payload()
    log = args.log.read_text(encoding="utf-8")
    footers = re.findall(r"^Build completed successfully.*$",log,re.M)
    assert footers and not re.search(r"^error:",log,re.M)
    matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+)' depends on axioms:\s*\[([^]]*)\]",log)
    matches = [(name,axioms) for name,axioms in matches if "2541" in name]
    assert len(matches) == len(EXPECTED) and {name for name,_ in matches} == EXPECTED
    reports = {name:[x.strip() for x in axioms.split(",")] for name,axioms in matches}
    assert all(v == ["propext","Classical.choice","Quot.sound"] for v in reports.values())
    pending, hashes, mismatches = MODULES[:], {}, []
    while pending:
        name = pending.pop()
        path = name.replace(".","/")+".lean"
        if path in hashes:
            continue
        source = (ROOT/path).read_bytes()
        mirror = args.mirror/path
        if not mirror.exists() or source != mirror.read_bytes():
            mismatches.append(path)
        hashes[path] = hashlib.sha256(source).hexdigest()
        for line in source.decode("utf-8-sig").splitlines():
            if line.startswith("import "):
                pending.extend(x for x in line[7:].split()
                               if x.startswith("ConnesWeilRH.") or x == "ConnesWeilRH")
    assert not mismatches, mismatches
    for name in ("lean-toolchain","lake-manifest.json","lakefile.toml"):
        assert (ROOT/name).read_bytes() == (args.mirror/name).read_bytes(), name
    result = dict(record=2541,status="BUILD_AXIOM_SOURCE_WITNESS_IDENTITY_PASS",
                  build_footer=footers[-1],audits=reports,project_sources_checked=len(hashes),
                  source_sha256=hashes,payload=payload,
                  build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
                  nonzero_node_numeric_certificate=True,full_grid_numeric_certificate=False,
                  exact_owner_transfer=False,producer_go=False,rh_claim=False)
    (ROOT/"results/2541_nonzero_node_validation.json").write_text(
        json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(result["status"],len(reports),len(hashes),flush=True)


if __name__ == "__main__":
    main()
