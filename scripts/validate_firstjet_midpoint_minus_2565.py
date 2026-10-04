"""Independent order-1 minus midpoint jets and the minus cell2700 summand."""
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
from price_cell2700_minus_2565 import scalar_defs

POSITION = -Q(65536001, 10**7) + Q(5401, 2) * Q(65536001, 51200000000)
SIGMA = Q(-1, 2)


def replay_exp(z, depth):
    center, error = (Q(1), Q(0)), Q(1, 10**18) + 19 * Q(1, 2**159)
    def down(v):
        t = v * 2**160
        return Q(t.numerator // t.denominator, 2**160)
    for j in range(19, 0, -1):
        product = multiply(z, center)
        center = down(1 + product[0] / j), down(product[1] / j)
    for _ in range(depth):
        t = (error * (2 * sum(abs(v) for v in center) + error) + Q(1, 2**159)) * 2**200
        error = Q(-((-t.numerator) // t.denominator), 2**200)
        center = tuple(down(v) for v in multiply(center, center))
    return center, error


def check(source, *, prefix="fjmin", record=2565):
    suffix = str(record)
    names = re.findall(r"def (" + prefix + r"P\d{3})Center" + suffix, source)
    assert names == [f"{prefix}P{i:03d}" for i in range(len(names))] and len(names) == 30
    capture = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    active = 0
    for i, name in enumerate(names):
        width, theta = (Q.from_float(float.fromhex(v)) for v in capture[i])
        radius = width**2
        if abs(POSITION) >= radius:
            assert value(source, name + "Factor" + suffix) == (Q(0), Q(0))
            assert value(source, name + "Center" + suffix) == (Q(0), Q(0))
            assert scalar_def(source, name + "Error" + suffix) == 0
            assert value(source, name + "Rounded" + suffix) == (Q(0), Q(0))
            assert scalar_def(source, name + "Radius" + suffix) == 0
            continue
        active += 1
        q = 1 - (POSITION / radius) ** 2
        factor = value(source, name + "Factor" + suffix)
        assert factor == (SIGMA - 60 * POSITION / (radius**2 * q**2), theta), (name, "factor")
        depth = int(re.search(r"compactExp2547\s+" + name + r"Input" + suffix + r"\s+(\d+)",
                              source)[1])
        z = value(source, name + "Input" + suffix)
        assert z == ((SIGMA * POSITION - 30 / q) / 2**depth, theta * POSITION / 2**depth)
        assert sum(abs(v) for v in z) <= 1
        center, error = replay_exp(z, depth)
        assert value(source, name + "Center" + suffix) == center
        assert scalar_def(source, name + "Error" + suffix) == error
    return active


def check_signed(source):
    coefficients = json.loads(
        (ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    total, charge = (Q(0), Q(0)), Q(0)
    active = 0
    for i in range(30):
        name = f"fjminP{i:03d}"
        factor = value(source, name + "Factor2565")
        center = value(source, name + "Center2565")
        error = scalar_def(source, name + "Error2565")
        radius = scalar_def(source, name + "Radius2565")
        if factor == (Q(0), Q(0)) and center == (Q(0), Q(0)) and error == 0 and radius == 0:
            continue
        active += 1
        exact = multiply(factor, center)
        rounded = value(source, name + "Rounded2565")
        for a, b in zip(exact, rounded):
            scaled = a * 2**100
            assert b == Q(scaled.numerator // scaled.denominator, 2**100)
        needed = sum(abs(v) for v in factor) * error + Q(1, 2**99)
        scaled = needed * 2**140
        assert radius == Q(-((-scaled.numerator) // scaled.denominator), 2**140)
        assert radius + sum(abs(v) for v in rounded) <= 1
        coeff = tuple(
            (Q(coefficients[i]["ideal_base_coefficient"][p]["lower_exact"]) +
             Q(coefficients[i]["ideal_base_coefficient"][p]["upper_exact"])) / 2
            for p in ("real", "imag"))
        total = tuple(a + b for a, b in zip(total, multiply(coeff, rounded)))
        charge += sum(abs(v) for v in coeff) * radius
    assert active == 28
    assert complex_value(definition(source, "fjminSum2565").split(":=", 1)[1]) == total
    upper = scalar_def(source, "fjminUpper2565")
    assert upper > Q(1, 10**7)
    assert sum(v * v for v in total) <= (upper - Q(1, 10**7)) ** 2
    assert charge <= Q(1, 10**8) and charge + Q(30, 10**30) <= Q(1, 10**7)
    return dict(active_families=active, first_jet_upper=str(upper),
                first_jet_upper_display=float(upper), evaluation_charge=str(charge),
                evaluation_charge_display=float(charge))


def check_assembly(firstjet_source, assembly_source):
    r = Q(65536001, 10**7)
    step = 2 * r / 10240
    half = step / 2
    left_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusLeftBounds2558.lean").read_text()
    right_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusRightBounds2558.lean").read_text()
    fourth_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusFourth2558.lean").read_text()
    vals = {}
    vals.update(scalar_defs(left_src, r"batchC02700MinusLeftP\d{3}NormUpper2558"))
    vals.update(scalar_defs(right_src, r"batchC02700MinusRightP\d{3}NormUpper2558"))
    vals.update(scalar_defs(fourth_src, r"batchC02700MinusFourthP\d{3}Upper2558"))
    assert len(vals) == 90, len(vals)
    rows = json.loads(
        (ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    third_agg = Q(0)
    for i, row in enumerate(rows):
        box = row["ideal_base_coefficient"]
        l1 = sum(abs((Q(box[p]["lower_exact"]) + Q(box[p]["upper_exact"])) / 2)
                 for p in ("real", "imag"))
        t = max(vals[f"batchC02700MinusLeftP{i:03d}NormUpper2558"],
                vals[f"batchC02700MinusRightP{i:03d}NormUpper2558"]) \
            + vals[f"batchC02700MinusFourthP{i:03d}Upper2558"] * half
        third_agg += (l1 + Q(1, 10**30)) * t
    l1_def = scalar_defs(assembly_source, "correctionThirdL1Upper2565")[
        "correctionThirdL1Upper2565"]
    assert l1_def == third_agg, (float(l1_def), float(third_agg))
    mid_upper = scalar_def(
        (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusMidpointBounds2558.lean").read_text(),
        "batchC02700MinusSignedMidpointUpper2558")
    curvature = mid_upper + third_agg * half
    jet1 = scalar_def(firstjet_source, "fjminUpper2565")
    n0l = scalar_def((ROOT / "ConnesWeilRH/Dev/C1RouteASharedN02700Minus2556.lean").read_text(),
                     "sharedN02700MinusUpper2556")
    n0r = scalar_def((ROOT / "ConnesWeilRH/Dev/C1RouteASharedN02701Minus2556.lean").read_text(),
                     "sharedN02701MinusUpper2556")
    match = re.search(
        r"correctionSecondCell2700MinusUpper2565 : ℝ :=\s*\(\((\d+) : ℝ\) / (\d+)\)",
        assembly_source)
    assert match
    bound = Q(int(match.group(1)), int(match.group(2)))
    pieces = (step * curvature,
              2 * abs(SIGMA) * (step * (jet1 + curvature * half)),
              SIGMA**2 * (half * (n0l + n0r) + curvature * (step**3 / 12)))
    assert sum(pieces) <= bound, (float(sum(pieces)), float(bound))
    return dict(curvature_upper=str(curvature), curvature_display=float(curvature),
                first_jet_upper=str(jet1), endpoint_left=str(n0l), endpoint_right=str(n0r),
                third_aggregate_l1=str(third_agg),
                pieces_display=[float(v) for v in pieces],
                piece_sum_display=float(sum(pieces)), cell_bound=float(bound))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path)
    parser.add_argument("--mirror", type=Path)
    args = parser.parse_args()
    path = ROOT / "ConnesWeilRH/Dev/C1RouteAFirstJetMidpointMinus2565.lean"
    source = path.read_text()
    assembly_path = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionSecondCell2700Minus_2565.lean"
    assembly_source = assembly_path.read_text()
    active = check(source)
    signed = check_signed(source)
    assembly = check_assembly(source, assembly_source)
    capture = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    probe = next(i for i, vals in enumerate(capture)
                 if abs(POSITION) < Q.from_float(float.fromhex(vals[0]))**2)
    name = f"fjminP{probe:03d}"
    corrupted = re.sub(r"(def " + name + r"Factor2565\b.*?:=).*?(?=\n\n)",
                       r"\1 (0, 0)", source, count=1, flags=re.S)
    assert corrupted != source
    try:
        check(corrupted)
    except AssertionError:
        factor_rejected = True
    else:
        raise AssertionError("Corrupted minus first-jet factor was accepted")
    corrupted = re.sub(r"(noncomputable def " + name + r"Radius2565\b.*?:=).*?(?=\n\n)",
                       r"\1 (0 : ℝ)", source, count=1, flags=re.S)
    assert corrupted != source
    try:
        check_signed(corrupted)
    except AssertionError:
        radius_rejected = True
    else:
        raise AssertionError("Zeroed minus first-jet radius accepted")
    corrupted = re.sub(r"(def " + name + r"Rounded2565 : RatPair2542 :=).*?(?=\n\n)",
                       r"\1 (0, 0)", source, count=1, flags=re.S)
    assert corrupted != source
    try:
        check_signed(corrupted)
    except AssertionError:
        rounded_rejected = True
    else:
        raise AssertionError("Corrupted rounded minus first jet accepted")
    corrupted_assembly = re.sub(
        r"(noncomputable def correctionSecondCell2700MinusUpper2565 : ℝ :=\s*)\(\(\d+ : ℝ\) / \d+\)",
        r"\1 ((0 : ℝ) / 1)", assembly_source, count=1)
    assert corrupted_assembly != assembly_source
    try:
        check_assembly(source, corrupted_assembly)
    except AssertionError:
        bound_rejected = True
    else:
        raise AssertionError("Zeroed minus cell bound accepted")
    result = dict(record=2565, active_families=active,
                  scope="order-1 minus midpoint jet arithmetic plus minus cell2700 "
                        "correction summand; Lean acceptance separate",
                  independent_factor_method="logarithmic differentiation",
                  corrupted_factor_rejected=factor_rejected,
                  zeroed_radius_rejected=radius_rejected,
                  changed_rounded_rejected=rounded_rejected,
                  zeroed_cell_bound_rejected=bound_rejected,
                  signed_aggregate=signed, cell2700_minus_summand=assembly,
                  membership_claim=False, full_grid_certificate=False,
                  rh_claim=False,
                  source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  assembly_sha256=hashlib.sha256(assembly_path.read_bytes()).hexdigest())
    if args.log:
        assert args.mirror
        from generate_firstjet_midpoint_minus_2565 import render
        assert source == render()
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$", log, re.M)
        assert footers and not re.search(r"^error:", log, re.M)
        assert not re.search(r"^warning: .*2565\.lean:", log, re.M)
        expected = {"fjminExpError2565", "fjminSum_eq2565", "fjminSum_norm2565",
                    "fjminCharge2565", "firstJetMidpointMinusUpper_le2565",
                    "weightedPhysicalFirstJetMidpointMinus_le2565",
                    "correctionSecondCell2700MinusSummand_le_2565",
                    "correctionThirdL1Sum_eq_2565"}
        matches = re.findall(
            r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2565)' depends on axioms:\s*\[([^]]*)\]", log)
        audits = {name_: [v.strip() for v in ax.split(",")] for name_, ax in matches}
        assert set(audits) == expected
        assert all(v == ["propext", "Classical.choice", "Quot.sound"] for v in audits.values())
        pending = ["ConnesWeilRH", "ConnesWeilRH.Dev.C1RouteAFirstJetMidpointMinus2565",
                   "ConnesWeilRH.Dev.C1RouteACorrectionSecondCell2700Minus_2565"]
        hashes = {}
        while pending:
            relative = pending.pop().replace(".", "/") + ".lean"
            if relative in hashes:
                continue
            data = (ROOT / relative).read_bytes()
            assert data == (args.mirror / relative).read_bytes(), relative
            hashes[relative] = hashlib.sha256(data).hexdigest()
            for line in data.decode("utf-8-sig").splitlines():
                if line.startswith("import "):
                    pending.extend(v for v in line[7:].split() if v.startswith("ConnesWeilRH"))
        for fname in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            assert (ROOT / fname).read_bytes() == (args.mirror / fname).read_bytes(), fname
        result.update(status="BUILD_AXIOM_SOURCE_MINUS_FIRST_JET_CELL2700_PASS",
                      build_footer=footers[-1], audits=audits,
                      project_sources_checked=len(hashes), project_source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
    (ROOT / "results/2565_minus_firstjet_midpoint_readback.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("MINUS_FIRST_JET_CELL2700_READBACK_PASS", active, signed["first_jet_upper_display"],
          assembly["piece_sum_display"], assembly["cell_bound"], flush=True)
