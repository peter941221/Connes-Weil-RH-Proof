"""Reuse certified order-zero endpoint exponentials for order-two chord jets.

The stored center/error/input/position are checked against both committed
owners before replacing only the base-exponential proof with a reference.
The order-two multiplier and derivative proof remain the accepted 2575 ones.
"""
import hashlib
import json
from pathlib import Path
import re

import generate_second_chord_cell_2575 as prior
from generate_correction_pair_2570 import rename
from format_lean_source_2553 import wrap_source
from validate_adaptive_nodes_2542 import scalar_def
from validate_compact_replay_2542 import value

ROOT = prior.ROOT
DEV = prior.DEV
RECORD = 2576
ASSEMBLY = "C1RouteACorrectionSecondChordSharedCell2700_2576"


def names(index, sign):
    side = prior.side_name(sign)
    stem = f"SharedSecondN{index:05d}{side}"
    prefix = stem[0].lower() + stem[1:]
    return dict(prefix=prefix, point=prefix + "Point", signed=prefix + "Signed",
                deriv="C1RouteA" + stem + "Derivatives2576",
                bounds="C1RouteA" + stem + "Bounds2576",
                kernel=f"kernelN{index:05d}{side}",
                kernel_module=f"C1RouteAKernelN{index:05d}{side}2555")


def declarations(source):
    source = source[:source.index("end ConnesWeilRH.Dev")]
    matches = list(re.finditer(r"^(?:(?:noncomputable )?def|theorem) (\w+)", source, re.MULTILINE))
    return {match[1]: source[match.start():matches[index + 1].start()
                            if index + 1 < len(matches) else len(source)].strip() + "\n"
            for index, match in enumerate(matches)}


def translate(source, old, new):
    source = rename(source, old["point"], 2575, new["point"], RECORD)
    source = rename(source, old["signed"], 2575, new["signed"], RECORD)
    return source.replace(old["prefix"] + "Physical2575", new["prefix"] + "Physical2576")


def proof_header(source):
    match = re.search(r"\s*:=\s*by\b", source)
    assert match, "missing theorem proof boundary"
    return source[:match.start()].rstrip() + " "


def shared_point(index, sign):
    old = prior.point_names(index, sign)
    new = names(index, sign)
    original = (DEV / (old["deriv"] + ".lean")).read_text()
    kernel = (DEV / (new["kernel_module"] + ".lean")).read_text()
    fields = declarations(original)
    assert scalar_def(original, old["point"] + "Position2575") == scalar_def(
        kernel, new["kernel"] + "Position2555")
    active = []
    for family in range(30):
        old_family = old["point"] + f"P{family:03d}"
        kernel_family = new["kernel"] + f"P{family:03d}"
        for suffix in ("Center", "Error"):
            read = value if suffix == "Center" else scalar_def
            assert read(original, old_family + suffix + "2575") == read(
                kernel, kernel_family + suffix + "2555"), (index, sign, family, suffix)
        if old_family + "Input2575" in fields:
            active.append(family)
            assert value(original, old_family + "Input2575") == value(
                kernel, kernel_family + "Input2555")
    parts = [f"import ConnesWeilRH.Dev.{new['kernel_module']}\n\n",
             "namespace ConnesWeilRH.Dev\n\n",
             "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit\n",
             "open ConnesWeilRH.Source.C1RouteAItem5Arithmetic\n\n"]
    for suffix in ("Position", "Zero"):
        parts.append(translate(fields[old["point"] + suffix + "2575"], old, new))
        parts.append("\n")
    for family in range(30):
        old_family = old["point"] + f"P{family:03d}"
        new_family = new["point"] + f"P{family:03d}"
        kernel_family = new["kernel"] + f"P{family:03d}"
        for suffix in ("Input", "Center", "Factor", "Error"):
            key = old_family + suffix + "2575"
            if key in fields:
                parts.extend([translate(fields[key], old, new), "\n"])
        exterior = old_family + "Exterior2575"
        if exterior in fields:
            header = translate(proof_header(fields[exterior]), old, new)
            assert header != translate(fields[exterior], old, new)
            parts.append(header + ":= by\n  exact " + kernel_family + "Exterior2555 n\n\n")
        base_key = old_family + "BaseError2575"
        base = fields[base_key]
        header = translate(proof_header(base), old, new)
        parts.append(header + ":= by\n  exact " + kernel_family + "BaseError2555\n\n")
        parts.extend([translate(fields[old_family + "DerivativeError2575"], old, new), "\n"])
    parts.extend([translate(fields[old["point"] + "Grid2575"], old, new),
                  "\nend ConnesWeilRH.Dev\n"])
    derivative = wrap_source("".join(parts))
    assert "compactExp2547" not in derivative and "decide +kernel" not in derivative
    assert len(re.findall(r"exact kernelN\d{5}\w+P\d{3}BaseError2555", derivative)) == 30
    bounds = translate((DEV / (old["bounds"] + ".lean")).read_text(), old, new)
    bounds = bounds.replace(old["deriv"], new["deriv"])
    return new, derivative, wrap_source(bounds), dict(index=index, sign=sign, active=active,
        active_exponentials_reused=len(active), base_error_references=30,
        input_center_error_equal=True, old_bytes=len(original.encode()),
        shared_bytes=len(derivative.encode()))


def main():
    predecessor_path = ROOT / "results/2575_second_chord_generation.json"
    predecessor = json.loads(predecessor_path.read_text())
    outputs = {}
    controls = []
    assembly = (DEV / (prior.ASSEMBLY + ".lean")).read_text()
    audit_names = []
    input_paths = [Path(__file__), predecessor_path,
                   DEV / (prior.ASSEMBLY + ".lean")]
    for sign in (-1, 1):
        for index in (2700, 2701):
            old = prior.point_names(index, sign)
            new, raw, bounds, control = shared_point(index, sign)
            outputs[new["deriv"]] = raw
            outputs[new["bounds"]] = bounds
            controls.append(control)
            assembly = translate(assembly, old, new).replace(old["bounds"], new["bounds"])
            input_paths += [DEV / (old["deriv"] + ".lean"), DEV / (old["bounds"] + ".lean"),
                            DEV / (new["kernel_module"] + ".lean")]
            for family in range(30):
                audit_names += [new["point"] + f"P{family:03d}" + suffix + "2576"
                                for suffix in ("BaseError", "DerivativeError")]
            audit_names.append(new["point"] + "Grid2576")
            audit_names += [new["signed"] + suffix + "2576"
                            for suffix in ("ExpError", "Sum_eq", "Charge", "Upper_le")]
            audit_names.append(new["prefix"] + "Physical2576")
        old_prefix = f"corrSecondChord{prior.side_name(sign)}2575"
        new_prefix = f"sharedSecondChord{prior.side_name(sign)}2576"
        assembly = assembly.replace(old_prefix, new_prefix)
        audit_names += [new_prefix + suffix for suffix in
                        ("Fourth_bound", "Fourth_eq", "Summand_le", "ProductionSummand_le", "Integral_le")]
    outputs[ASSEMBLY] = wrap_source(assembly)
    audit = "import ConnesWeilRH.Dev." + ASSEMBLY + "\n\n"
    audit += "\n".join("#print axioms ConnesWeilRH.Dev." + name for name in audit_names) + "\n"
    outputs[ASSEMBLY + "Audit"] = audit
    for module, source in outputs.items():
        (DEV / (module + ".lean")).write_text(source, encoding="utf-8", newline="\n")
    result = dict(record=2576, status="SHARED_EXP_SECOND_CHORD_GENERATED", cell=2700,
                  controls=controls, modules=list(outputs), audit_targets=audit_names,
                  endpoint_rows=predecessor["endpoint_rows"], cell_rows=predecessor["cell_rows"],
                  input_sha256={str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in input_paths},
                  output_sha256={str((DEV / (module + ".lean")).relative_to(ROOT)):
                                 hashlib.sha256(source.encode()).hexdigest()
                                 for module, source in outputs.items()},
                  exponentials_recomputed=0, full_grid_certificate=False,
                  exact_coefficient_membership=False, producer_go=False, rh_claim=False)
    output = ROOT / "results/2576_shared_exp_generation.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(dict(status=result["status"], controls=controls, audits=len(audit_names))), flush=True)


if __name__ == "__main__":
    main()
