"""Independent order-1 midpoint jets and the cell2700 correction summand."""
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

POSITION = -Q(65536001, 10**7) + Q(5401, 2) * Q(65536001, 51200000000)
SIGMA = Q(1, 2)


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


def check(source, *, prefix="fjmid", record=2563):
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
        name = f"fjmidP{i:03d}"
        factor = value(source, name + "Factor2563")
        center = value(source, name + "Center2563")
        error = scalar_def(source, name + "Error2563")
        radius = scalar_def(source, name + "Radius2563")
        if factor == (Q(0), Q(0)) and center == (Q(0), Q(0)) and error == 0 and radius == 0:
            continue
        active += 1
        exact = multiply(factor, center)
        rounded = value(source, name + "Rounded2563")
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
    assert complex_value(definition(source, "fjmidSum2563").split(":=", 1)[1]) == total
    upper = scalar_def(source, "fjmidUpper2563")
    assert upper > Q(1, 10**7)
    assert sum(v * v for v in total) <= (upper - Q(1, 10**7)) ** 2
    assert charge <= Q(1, 10**8) and charge + Q(30, 10**30) <= Q(1, 10**7)
    return dict(active_families=active, first_jet_upper=str(upper),
                first_jet_upper_display=float(upper), evaluation_charge=str(charge),
                evaluation_charge_display=float(charge))


def check_assembly(firstjet_source, assembly_source):
    base = (ROOT / "ConnesWeilRH/Dev/C1RouteABoundaryIntegral2551.lean").read_text()
    left = scalar_def(
        (ROOT / "ConnesWeilRH/Dev/C1RouteASharedN02700Plus2556.lean").read_text(),
        "sharedN02700PlusUpper2556")
    right = scalar_def(
        (ROOT / "ConnesWeilRH/Dev/C1RouteASharedN02701Plus2556.lean").read_text(),
        "sharedN02701PlusUpper2556")
    r = Q(65536001, 10**7)
    step = 2 * r / 10240
    curvature = scalar_def(base, "boundaryCellCurvatureUpper2551")
    jet1 = scalar_def(firstjet_source, "fjmidUpper2563")
    match = re.search(r"correctionSecondCell2700Upper2563 : ℝ :=\s*\(\((\d+) : ℝ\) / (\d+)\)",
                      assembly_source)
    assert match
    bound = Q(int(match.group(1)), int(match.group(2)))
    pieces = (step * curvature,
              2 * SIGMA * (step * (jet1 + curvature * (step / 2))),
              SIGMA**2 * ((step / 2) * (left + right) + curvature * (step**3 / 12)))
    assert sum(pieces) <= bound, (float(sum(pieces)), float(bound))
    return dict(curvature_upper=str(curvature), first_jet_upper=str(jet1),
                endpoint_left=str(left), endpoint_right=str(right),
                pieces_display=[float(v) for v in pieces],
                piece_sum_display=float(sum(pieces)), cell_bound=float(bound))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path)
    parser.add_argument("--mirror", type=Path)
    args = parser.parse_args()
    path = ROOT / "ConnesWeilRH/Dev/C1RouteAFirstJetMidpoint2563.lean"
    source = path.read_text()
    assembly_path = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionSecondCell2700_2563.lean"
    assembly_source = assembly_path.read_text()
    active = check(source)
    signed = check_signed(source)
    assembly = check_assembly(source, assembly_source)
    capture = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    probe = next(i for i, vals in enumerate(capture)
                 if abs(POSITION) < Q.from_float(float.fromhex(vals[0]))**2)
    name = f"fjmidP{probe:03d}"
    corrupted = re.sub(r"(def " + name + r"Factor2563\b.*?:=).*?(?=\n\n)",
                       r"\1 (0, 0)", source, count=1, flags=re.S)
    assert corrupted != source
    try:
        check(corrupted)
    except AssertionError:
        factor_rejected = True
    else:
        raise AssertionError("Corrupted first-jet factor was accepted")
    corrupted = re.sub(r"(noncomputable def " + name + r"Radius2563\b.*?:=).*?(?=\n\n)",
                       r"\1 (0 : ℝ)", source, count=1, flags=re.S)
    assert corrupted != source
    try:
        check_signed(corrupted)
    except AssertionError:
        radius_rejected = True
    else:
        raise AssertionError("Zeroed first-jet radius accepted")
    corrupted = re.sub(r"(def " + name + r"Rounded2563 : RatPair2542 :=).*?(?=\n\n)",
                       r"\1 (0, 0)", source, count=1, flags=re.S)
    assert corrupted != source
    try:
        check_signed(corrupted)
    except AssertionError:
        rounded_rejected = True
    else:
        raise AssertionError("Corrupted rounded first jet accepted")
    corrupted_assembly = re.sub(
        r"(noncomputable def correctionSecondCell2700Upper2563 : ℝ :=\s*)\(\(\d+ : ℝ\) / \d+\)",
        r"\1 ((0 : ℝ) / 1)", assembly_source, count=1)
    assert corrupted_assembly != assembly_source
    try:
        check_assembly(source, corrupted_assembly)
    except AssertionError:
        bound_rejected = True
    else:
        raise AssertionError("Zeroed cell bound accepted")
    result = dict(record=2563, active_families=active,
                  scope="order-1 midpoint jet arithmetic plus cell2700 correction summand; "
                        "Lean acceptance separate",
                  independent_factor_method="logarithmic differentiation",
                  corrupted_factor_rejected=factor_rejected,
                  zeroed_radius_rejected=radius_rejected,
                  changed_rounded_rejected=rounded_rejected,
                  zeroed_cell_bound_rejected=bound_rejected,
                  signed_aggregate=signed, cell2700_summand=assembly,
                  membership_claim=False, full_grid_certificate=False,
                  rh_claim=False,
                  source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  assembly_sha256=hashlib.sha256(assembly_path.read_bytes()).hexdigest())
    if args.log:
        assert args.mirror
        from generate_firstjet_midpoint_2563 import render
        assert source == render()
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$", log, re.M)
        assert footers and not re.search(r"^error:", log, re.M)
        assert not re.search(r"^warning: .*2563\.lean:", log, re.M)
        expected = {"fjmidExpError2563", "fjmidSum_eq2563", "fjmidSum_norm2563",
                    "fjmidCharge2563", "firstJetMidpointUpper_le2563",
                    "weightedPhysicalFirstJetMidpoint_le2563",
                    "correctionSecondCell2700Summand_le_2563"}
        matches = re.findall(
            r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2563)' depends on axioms:\s*\[([^]]*)\]", log)
        audits = {name_: [v.strip() for v in ax.split(",")] for name_, ax in matches}
        assert set(audits) == expected
        assert all(v == ["propext", "Classical.choice", "Quot.sound"] for v in audits.values())
        pending = ["ConnesWeilRH", "ConnesWeilRH.Dev.C1RouteAFirstJetMidpoint2563",
                   "ConnesWeilRH.Dev.C1RouteACorrectionSecondCell2700_2563"]
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
        result.update(status="BUILD_AXIOM_SOURCE_FIRST_JET_CELL2700_PASS",
                      build_footer=footers[-1], audits=audits,
                      project_sources_checked=len(hashes), project_source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
    (ROOT / "results/2563_firstjet_midpoint_readback.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("FIRST_JET_CELL2700_READBACK_PASS", active, signed["first_jet_upper_display"],
          assembly["piece_sum_display"], assembly["cell_bound"], flush=True)
