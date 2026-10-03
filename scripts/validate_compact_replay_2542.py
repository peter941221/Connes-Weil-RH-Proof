"""Read compact literals independently against accepted full witnesses."""
import ast
import argparse
import hashlib
import json
from pathlib import Path
import re

from validate_center_node_2540 import exact_expression
from validate_nonzero_node_2541 import complex_value, definition, table, scalar

ROOT = Path(__file__).resolve().parents[1]


def value(source, name):
    match = re.search(r"\bdef " + name + r"\b[^\n]*?:=(.*?)(?=\n\n)", source, re.S)
    assert match, name
    expression = re.sub(r":\s*ℚ", "", match[1]).replace("^", "**").strip()
    tree = ast.parse(expression, mode="eval").body

    def read(node):
        if isinstance(node, ast.Tuple):
            return tuple(read(item) for item in node.elts)
        return exact_expression(ast.unparse(node))

    return read(tree)


def check(source):
    for i in range(30):
        tag = f"P{i:03d}"
        old = (ROOT / f"ConnesWeilRH/Dev/C1RouteAExpNode2541{tag}.lean").read_text()
        z = complex_value(definition(old, f"nodeZ{tag}2541").split(":=", 1)[1])
        s = table(old, f"nodeS{tag}2541", complex_value)[-1]
        e = table(old, f"nodeE{tag}2541", scalar)[-1]
        assert value(source, f"compactInput{tag}2542") == z, (tag, "input")
        assert value(source, f"compactOutput{tag}2542") == (s, e), (tag, "output")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--adaptive", action="store_true")
    args = parser.parse_args()
    path = ROOT / "ConnesWeilRH/Dev/C1RouteACompactExpBatch2542.lean"
    source = path.read_text()
    check(source)
    corrupted = re.sub(r"(def compactOutputP0002542 : RatState2542 :=).*?(?=\n\n)",
                       r"\1 ((0, 0), 0)", source, count=1, flags=re.S)
    try:
        check(corrupted)
    except AssertionError:
        rejected = True
    else:
        raise AssertionError("Corrupted output was accepted")
    result = dict(record=2542, scope="exact literal replay of 2541, no new production node",
                  families_checked=30, corrupted_output_rejected=rejected,
                  source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  source_bytes=len(path.read_bytes()), full_grid_certificate=False,
                  exact_owner_transfer=False, producer_go=False, rh_claim=False)
    if args.log:
        assert args.mirror is not None
        from generate_compact_replay_2542 import render, render_consumer
        assert source == render(), "batch regeneration mismatch"
        consumer = ROOT / "ConnesWeilRH/Dev/C1RouteACompactNode2542.lean"
        assert consumer.read_text() == render_consumer(), "consumer regeneration mismatch"
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$", log, re.M)
        assert footers and not re.search(r"^error:", log, re.M)
        assert not re.search(r"^warning: .*2542\.lean:", log, re.M)
        expected = {f"compactErrorP{i:03d}2542" for i in range(30)} | {
            "compactNodeError2542", "signedJet_compact_le2542", "weightedPhysical_compact_le2542",
            "compactReplay2542", "embedPair_round_error2542", "hornerRat_error2542",
            "squareState_error2542", "compactExp_error2542", "compactReplay_error2542"}
        adaptive_modules = []
        if args.adaptive:
            from generate_adaptive_nodes_2542 import render as render_adaptive
            from validate_adaptive_nodes_2542 import check as check_adaptive
            adaptive_reports = []
            for index in (5440,10239):
                for sign in (-1,1):
                    tag = f"N{index:05d}{'Plus' if sign > 0 else 'Minus'}"
                    module = "ConnesWeilRH.Dev.C1RouteAAdaptive" + tag + "2542"
                    adaptive_modules.append(module)
                    actual = (ROOT/(module.replace(".","/")+".lean")).read_text()
                    assert actual == render_adaptive(index,sign)[0]
                    adaptive_reports.append(check_adaptive(actual,index,sign))
                    expected.update({f"adaptive{tag}Signed_le2542", f"adaptive{tag}Physical_le2542"})
            result["adaptive_cases"] = adaptive_reports
        matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2542)' depends on axioms:\s*\[([^]]*)\]", log)
        reports = {name: [v.strip() for v in axioms.split(",")] for name, axioms in matches}
        assert set(reports) == expected, (set(reports) - expected, expected - set(reports))
        assert all(v == ["propext", "Classical.choice", "Quot.sound"] for v in reports.values())
        pending = ["ConnesWeilRH", "ConnesWeilRH.Dev.C1RouteACompactNode2542",
                   "ConnesWeilRH.Dev.C1RouteACompactExpAudit2542"] + adaptive_modules
        hashes = {}
        while pending:
            name = pending.pop()
            relative = name.replace(".", "/") + ".lean"
            if relative in hashes:
                continue
            data = (ROOT / relative).read_bytes()
            assert data == (args.mirror / relative).read_bytes(), relative
            hashes[relative] = hashlib.sha256(data).hexdigest()
            for line in data.decode("utf-8-sig").splitlines():
                if line.startswith("import "):
                    pending.extend(v for v in line[7:].split() if v.startswith("ConnesWeilRH"))
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            assert (ROOT/name).read_bytes() == (args.mirror/name).read_bytes(), name
        result.update(status="BUILD_AXIOM_SOURCE_REPLAY_IDENTITY_PASS", build_footer=footers[-1],
                      audits=reports, project_sources_checked=len(hashes), source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
                      signed_node_upper="137900014901/10000000000")
    out = ROOT / "results/2542_compact_replay_readback.json"
    out.write_text(json.dumps(result, indent=2)+"\n")
    print(result.get("status", "LITERAL_READBACK_PASS"), "30 families",
          result.get("project_sources_checked", "unmeasured"), "sources", flush=True)
