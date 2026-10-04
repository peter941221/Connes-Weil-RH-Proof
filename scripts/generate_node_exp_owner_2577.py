"""Certify a fresh node value once and reuse it at derivative orders two/three."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

from generate_boundary_jets_2548 import render as render_jets
from generate_complex_exp_node_2541 import CAPTURE, ROOT
from generate_correction_pair_2570 import CENTER_SWAPS, derive_generator, finalize_correction, rename
from generate_shared_second_chord_2576 import declarations, proof_header
from generate_second_chord_cell_2575 import side_name
from format_lean_source_2553 import wrap_source
from validate_adaptive_nodes_2542 import scalar_def
from validate_compact_replay_2542 import value

DEV = ROOT / "ConnesWeilRH/Dev"
RECORD = 2577
AUDIT = "C1RouteANodeExpOwner2577Audit"


def names(index, sign, order=None):
    assert isinstance(index, int) and 0 <= index <= 10240
    assert sign in (-1, 1)
    stem = f"NodeExpN{index:05d}{side_name(sign)}"
    if order is not None:
        assert order in (2, 3)
        stem = f"NodeJet{order}N{index:05d}{side_name(sign)}"
    prefix = stem[0].lower() + stem[1:]
    return dict(prefix=prefix, point=prefix + "Point", signed=prefix + "Signed",
                module="C1RouteA" + stem + "2577", bounds="C1RouteA" + stem + "Bounds2577")


def standalone(index, sign, order):
    naming = names(index, sign, order)
    source, active = render_jets("Midpoint", grid_order=(Q(index), order),
                               sigma=Q(sign, 2), paired=True)
    source = rename(source, "edgeMidpoint", 2548, naming["point"], RECORD)
    source = source.replace(":= by cbv", ":= by decide +kernel")
    source = source[:source.index("end ConnesWeilRH.Dev")] + "end ConnesWeilRH.Dev\n"
    return naming, wrap_source(source), active


def owner_source(index, sign, raw):
    naming = names(index, sign)
    child = names(index, sign, 2)
    fields = declarations(raw)
    parts = [raw[:raw.index("noncomputable def " + child["point"] + "Position2577")]]
    for suffix in ("Position", "Zero"):
        parts.extend([fields[child["point"] + suffix + "2577"], "\n"])
    for family in range(30):
        prefix = child["point"] + f"P{family:03d}"
        for suffix in ("Input", "Center", "Error", "Exterior", "BaseError"):
            key = prefix + suffix + "2577"
            if key in fields:
                parts.extend([fields[key], "\n"])
    parts += [fields[child["point"] + "Grid2577"], "\nend ConnesWeilRH.Dev\n"]
    source = rename("".join(parts), child["point"], RECORD, naming["point"], RECORD)
    assert "Factor2577" not in source and "DerivativeError2577" not in source
    return wrap_source(source)


def shared_source(index, sign, order, raw, owner):
    naming = names(index, sign, order)
    parent = names(index, sign)
    fields, parent_fields = declarations(raw), declarations(owner)
    assert scalar_def(raw, naming["point"] + "Position2577") == scalar_def(
        owner, parent["point"] + "Position2577")
    parts = [f"import ConnesWeilRH.Dev.{parent['module']}\n\n",
             "namespace ConnesWeilRH.Dev\n\n",
             "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit\n",
             "open ConnesWeilRH.Source.C1RouteAItem5Arithmetic\n\n"]
    for suffix in ("Position", "Zero"):
        parts += [fields[naming["point"] + suffix + "2577"], "\n"]
    for family in range(30):
        prefix = naming["point"] + f"P{family:03d}"
        upstream = parent["point"] + f"P{family:03d}"
        for suffix in ("Input", "Center", "Factor", "Error"):
            key = prefix + suffix + "2577"
            if key in fields:
                if suffix != "Factor":
                    read = scalar_def if suffix == "Error" else value
                    assert read(raw, key) == read(owner, upstream + suffix + "2577")
                parts += [fields[key], "\n"]
        for suffix in ("Exterior", "BaseError"):
            key = prefix + suffix + "2577"
            if key in fields:
                assert upstream + suffix + "2577" in parent_fields
                header = proof_header(fields[key])
                argument = " n" if suffix == "Exterior" else ""
                parts += [header + f":= by\n  exact {upstream}{suffix}2577{argument}\n\n"]
        parts += [fields[prefix + "DerivativeError2577"], "\n"]
    parts += [fields[naming["point"] + "Grid2577"], "\nend ConnesWeilRH.Dev\n"]
    source = wrap_source("".join(parts))
    assert "compactExp2547" not in source and "decide +kernel" not in source
    return source


def signed_source(index, sign, raw):
    naming = names(index, sign, 2)
    adapted = rename(raw, naming["point"], RECORD, "midpoint", 2543)
    renderer = derive_generator(ROOT / "scripts/generate_signed_midpoint_2543.py", CENTER_SWAPS)
    source, upper, charge = renderer["render"](source=adapted, sigma=Q(sign, 2))
    source = source.replace("C1RouteAMidpointDerivatives2543", naming["module"])
    source = rename(source, "midpoint", 2543, naming["point"], RECORD)
    source = rename(source, "signedMidpoint", 2543, naming["signed"], RECORD)
    source = source.replace("weightedPhysical_second_midpoint_le2543", naming["prefix"] + "Physical2577")
    source = wrap_source(finalize_correction(source))
    assert "baseCoefficient" not in source
    return source, upper, charge


def generate(indices):
    assert indices and len(indices) == len(set(indices))
    outputs, readings, audit_targets = {}, [], []
    for sign in (-1, 1):
        for index in indices:
            naming2, raw2, active = standalone(index, sign, 2)
            parent = names(index, sign)
            owner = owner_source(index, sign, raw2)
            outputs[parent["module"]] = owner
            for family in range(30):
                audit_targets.append(parent["point"] + f"P{family:03d}BaseError2577")
            audit_targets.append(parent["point"] + "Grid2577")
            for order in (2, 3):
                naming, raw, observed = (naming2, raw2, active) if order == 2 else standalone(index, sign, order)
                assert observed == active
                outputs[naming["module"]] = shared_source(index, sign, order, raw, owner)
                for family in range(30):
                    audit_targets += [naming["point"] + f"P{family:03d}" + suffix + "2577"
                                      for suffix in ("BaseError", "DerivativeError")]
                audit_targets.append(naming["point"] + "Grid2577")
            bounds, upper, charge = signed_source(index, sign, raw2)
            outputs[naming2["bounds"]] = bounds
            audit_targets += [naming2["signed"] + suffix + "2577"
                              for suffix in ("ExpError", "Sum_eq", "Charge", "Upper_le")]
            audit_targets.append(naming2["prefix"] + "Physical2577")
            readings.append(dict(index=index, sign=sign, active=active,
                                 position=str(scalar_def(owner, parent["point"] + "Position2577")),
                                 second_upper=str(upper), rounding_charge=str(charge),
                                 first_owner_module=parent["module"]))
    outputs[AUDIT] = "\n".join("import ConnesWeilRH.Dev." + module for module in outputs) + "\n\n"
    outputs[AUDIT] += "\n".join("#print axioms ConnesWeilRH.Dev." + target for target in audit_targets) + "\n"
    for module, source in outputs.items():
        (DEV / (module + ".lean")).write_text(source, encoding="utf-8", newline="\n")
    inputs = [Path(__file__), CAPTURE, ROOT / "results/2338_exact_interpolation_repair.json"]
    inputs += [ROOT / ("scripts/" + name) for name in (
        "generate_boundary_jets_2548.py", "generate_boundary_replay_2547.py",
        "generate_shared_second_chord_2576.py", "generate_signed_midpoint_2543.py",
        "generate_correction_pair_2570.py", "price_boundary_precision_2547.py",
        "routea_derivative_pricing_2543.py", "format_lean_source_2553.py")]
    payload = dict(record=RECORD, status="NODE_EXP_OWNER_GENERATED", indices=indices, signs=[-1, 1],
                   orders=[2, 3], coefficient_owner="ideal_correction_coefficient", error=str(Q(1, 10**28)),
                   rows=readings, modules=list(outputs), audit_targets=audit_targets,
                   input_sha256={str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                                 for path in inputs},
                   output_sha256={str((DEV / (module + ".lean")).relative_to(ROOT)):
                                  hashlib.sha256(source.encode()).hexdigest()
                                  for module, source in outputs.items()},
                   full_grid_certificate=False, exact_coefficient_membership=False,
                   producer_go=False, rh_claim=False)
    path = ROOT / "results/2577_node_exp_generation.json"
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("NODE_EXP_OWNER_GENERATED", len(outputs), len(audit_targets), flush=True)
    return payload


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--indices", type=int, nargs="+", default=[2702, 2703])
    args = parser.parse_args()
    generate(args.indices)


if __name__ == "__main__":
    main()
