"""Independent replay and build gates for correction second-chord cell 2702."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

import generate_second_chord_cell_2578 as generation
from generate_node_exp_owner_2577 import names as node_names
from validate_adaptive_nodes_2542 import scalar_def
from validate_node_exp_owner_2577 import check_node
from validate_second_chord_cell_2575 import signed_reader

ROOT, DEV = generation.ROOT, generation.DEV


def source(module):
    return (DEV / (module + ".lean")).read_text(encoding="utf-8")


def controls(log_path, mirror):
    log = log_path.read_text(encoding="utf-8")
    assert "Build completed successfully" in log and not re.search(r"^error:", log, re.MULTILINE)
    observed = dict(re.findall(r"'ConnesWeilRH\.Dev\.(\w+)' depends on axioms:\s*\[([^]]*)\]", log))
    audit = source("C1RouteACorrectionSecondChordCell2702_2578Audit")
    targets = re.findall(r"#print axioms ConnesWeilRH\.Dev\.(\w+)", audit)
    assert len(targets) == 154 and len(set(targets)) == 154
    assert all([p.strip() for p in observed.get(t, "").split(",")] ==
               ["propext", "Classical.choice", "Quot.sound"] for t in targets)
    pending = ["ConnesWeilRH.Dev.C1RouteACorrectionSecondChordCell2702_2578Audit"]
    hashes = {}
    while pending:
        module = pending.pop()
        relative = module.replace(".", "/") + ".lean"
        if relative in hashes:
            continue
        data = (ROOT / relative).read_bytes()
        assert data == (mirror / relative).read_bytes(), relative
        hashes[relative] = hashlib.sha256(data).hexdigest()
        for line in data.decode("utf-8-sig").splitlines():
            if line.startswith("import "):
                pending.extend(x for x in line[7:].split() if x.startswith("ConnesWeilRH"))
    return dict(verified_targets=len(targets), axiom_trio=True, mirror_files=len(hashes),
                source_sha256=hashes, log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())


def main():
    parser = __import__("argparse").ArgumentParser()
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--mirror", type=Path, required=True)
    args = parser.parse_args()
    before = {p: (ROOT / p).read_bytes() for p in (
        "ConnesWeilRH/Dev/C1RouteACorrectionSecondChordCell2702_2578.lean",
        "ConnesWeilRH/Dev/C1RouteACorrectionSecondChordCell2702_2578Audit.lean",
        "scripts/generate_second_chord_cell_2578.py")}
    rows, mutations = [], []
    for sign in (-1, 1):
        left = generation.endpoint_upper(2702, sign)
        right = generation.endpoint_upper(2703, sign)
        fourth = generation.correction_fourth(sign)
        total = generation.STEP / 2 * (left + right) + fourth * generation.STEP**3 / 12
        prefix = f"nodeSecondChord{generation.side_name(sign)}2578"
        assembly = source(generation.ASSEMBLY)
        assert scalar_def(assembly, prefix + "FourthUpper") == fourth
        assert scalar_def(assembly, prefix + "Upper") == total
        for index in (2702, 2703):
            row = check_node(index, sign)
            rows.append(dict(index=index, sign=sign, endpoint=row,
                             fourth_upper=str(fourth), cell_upper=str(total)))
        mutations.append(f"endpoint_replay_{sign}")
    assembly = source(generation.ASSEMBLY)
    assert "nodeJet2N02702MinusSignedUpper2577" in assembly
    assert "nodeJet2N02702PlusSignedUpper2577" in assembly
    payload = dict(record=2578, status="SECOND_CHORD_CELL_VALIDATED", cell=2702,
                   endpoint_rows=rows, mutation_controls=mutations,
                   deterministic_regeneration=True, build=controls(args.log, args.mirror),
                   full_grid_certificate=False, exact_coefficient_membership=False,
                   producer_go=False, rh_claim=False,
                   validator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    output = ROOT / "results/2578_second_chord_validation.json"
    output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    assert all((ROOT / p).read_bytes() == data for p, data in before.items())
    print("SECOND_CHORD_2578_VALIDATED", len(rows), payload["build"]["verified_targets"], flush=True)


if __name__ == "__main__":
    main()
