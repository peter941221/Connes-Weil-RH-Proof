"""Validate the center-node proof and exact record-2338 endpoint import."""
import argparse
import ast
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

from generate_center_node_2540 import render, SOURCE, TARGET

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["ConnesWeilRH.Dev.C1RouteACenterNode2540Audit", "ConnesWeilRH"]
EXPECTED = {
    "baseCoefficient_sum_norm_le2540", "exp_neg_thirty_upper2540",
    "weightedPhysical_center_eq2540", "weightedPhysical_center_le2540",
    "baseCoefficient_error_of_box2540", "signedJet_center_le2540",
}


def exact_expression(expression):
    node = ast.parse(expression.replace(": ℝ", "").replace("^", "**").strip(), mode="eval").body

    def evaluate(term):
        if isinstance(term, ast.Constant) and type(term.value) is int:
            return Fraction(term.value)
        if isinstance(term, ast.UnaryOp) and isinstance(term.op, ast.USub):
            return -evaluate(term.operand)
        if isinstance(term, ast.BinOp):
            left, right = evaluate(term.left), evaluate(term.right)
            if isinstance(term.op, ast.Add):
                return left + right
            if isinstance(term.op, ast.Sub):
                return left - right
            if isinstance(term.op, ast.Mult):
                return left * right
            if isinstance(term.op, ast.Div):
                return left / right
            if isinstance(term.op, ast.Pow) and right.denominator == 1:
                return left ** right.numerator
        raise ValueError("unsupported generated rational expression")

    return evaluate(node)


def check_endpoint_values(source):
    rows = json.loads(SOURCE.read_text(encoding="utf-8"))["coefficient_rows"]
    blocks = re.findall(r"  \| (\d+) =>\n(.*?)(?=\n  \|)", source, re.S)
    assert len(blocks) == len(rows) == 30
    for expected_index, (index, block) in enumerate(blocks):
        assert int(index) == expected_index == rows[expected_index]["index"]
        body = block.strip().removeprefix("{").removesuffix("}").strip()
        fields = re.split(r"\b(reLo|reHi|imLo|imHi)\s*:=", body)[1:]
        assert fields[::2] == ["reLo", "reHi", "imLo", "imHi"]
        for slot, expression in enumerate(fields[1::2]):
            component = ("real", "imag")[slot//2]
            side = ("lower_exact", "upper_exact")[slot % 2]
            expected = Fraction(rows[expected_index]["ideal_base_coefficient"][component][side])
            assert exact_expression(expression.replace("\n", " ")) == expected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=ROOT/"results/2540_center_node_validation.json")
    args = parser.parse_args()
    assert TARGET.read_text(encoding="utf-8") == render(), "coefficient endpoint import changed"
    check_endpoint_values(TARGET.read_text(encoding="utf-8"))
    log = args.log.read_text(encoding="utf-8")
    footers = re.findall(r"^Build completed successfully.*$", log, re.M)
    assert footers and not re.search(r"^error:", log, re.M)
    matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2540)' depends on axioms:\s*\[([^]]*)\]", log)
    assert len(matches) == len(EXPECTED) and {name for name, _ in matches} == EXPECTED
    reports = {name: [part.strip() for part in axioms.split(",")] for name, axioms in matches}
    assert all(axioms == ["propext", "Classical.choice", "Quot.sound"] for axioms in reports.values())
    pending, hashes, mismatches = MODULES[:], {}, []
    while pending:
        name = pending.pop()
        path = name.replace(".", "/")+".lean"
        if path in hashes:
            continue
        source = (ROOT/path).read_bytes()
        mirror_path = args.mirror/path
        if not mirror_path.exists() or source != mirror_path.read_bytes():
            mismatches.append(path)
        hashes[path] = hashlib.sha256(source).hexdigest()
        for line in source.decode("utf-8-sig").splitlines():
            if line.startswith("import "):
                pending.extend(item for item in line[7:].split()
                               if item.startswith("ConnesWeilRH.") or item == "ConnesWeilRH")
    assert not mismatches, mismatches
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        assert (ROOT/name).read_bytes() == (args.mirror/name).read_bytes(), name
    result = dict(record=2540, status="BUILD_AXIOM_SOURCE_ENDPOINT_IDENTITY_PASS",
                  build_footer=footers[-1], audits=reports,
                  project_sources_checked=len(hashes), source_sha256=hashes,
                  coefficient_input_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                  exact_coefficient_endpoints_checked=120,
                  endpoint_readback="independent exact-arithmetic parser plus regeneration",
                  build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
                  grid_index=5120, grid_cells=10240, node="0", signed_node_upper="69/5",
                  coefficient_ball_radius="1/1000000000000000000000000000000",
                  center_node_numeric_certificate=True, full_grid_numeric_certificate=False,
                  exact_owner_transfer=False, producer_go=False, rh_claim=False)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(result["status"], len(reports), len(hashes), flush=True)


if __name__ == "__main__":
    main()
