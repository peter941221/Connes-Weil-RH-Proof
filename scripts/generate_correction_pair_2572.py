"""Regenerate the cell2701-minus correction-second chain at the correction pair.

Record 2572: the composer of record 2570 parameterized to the adjacent grid
cell 2701 -- the first cell-index generalization of the correction-pair
machinery, and the step that turns the single-cell 2570/2571 certificates
into a batch lane. The chain reuses the committed 2570 correction boxes and
center node verbatim and reuses the committed 2570 shared endpoint module at
position 2701 as the cell's left endpoint (adjacent cells share edge data);
it emits five new modules: renamed 2701 midpoint derivative leaves, the 2543
midpoint render at the 2701 midpoint (5403/2), the 2565 first-jet generator
derived to the 2701 midpoint position, the 2542 shared render at position
2702 (batch-owned), and the assembly clone with the 2548 edge-def bridging
replaced by direct grid-literal norm_num bridges.

Fidelity is enforced the 2570 way: (1) every generator clone is derived by
token substitution validated by the 2567 remainder law; (2) with --selfcheck
the derived renderers run at the BASE pair and must reproduce the committed
2558/2565 modules byte for byte; (3) in correction mode every exact signed
sum must match the 2572 external repricing of
price_cell2701_minus_correction_2572.py.
"""
from fractions import Fraction as Q
from math import ceil, hypot
import hashlib
import json
import re
import sys

from format_lean_source_2553 import wrap_source
from generate_complex_exp_node_2541 import ROOT, CAPTURE
from generate_correction_pair_2570 import (
    CHARGE_Q,
    CENTER,
    CENTER_SWAPS,
    ERROR_DEF,
    centers_of,
    chunked,
    derive_generator,
    emit,
    finalize_correction,
    read_dev,
    read_text,
    rename,
)
from price_boundary_precision_2547 import precision_evaluate
from price_cell2700_minus_2565 import scalar_defs

RECORD = 2572
PILOT = ROOT / "results/2572_cell2701_minus_correction_repricing.json"
PRIOR_PILOT = ROOT / "results/2569_cell2700_minus_correction_repricing.json"

SIGMA = Q(-1, 2)
R = Q(65536001, 10 ** 7)
STEP = 2 * R / 10240
X_MID = -R + Q(5403, 2) * STEP
X_LEFT = -R + 2701 * STEP
X_RIGHT = -R + 2702 * STEP

MODULES = dict(
    deriv="C1RouteACorrMidpointDerivatives2701Minus2572",
    mid="C1RouteACorrMidpointBounds2701Minus2572",
    jet="C1RouteACorrFirstJetMidpointMinus2572",
    n0r="C1RouteACorrSharedN02702Minus2572",
    asm="C1RouteACorrectionSecondCell2701MinusCorr2572")

# the left endpoint of cell 2701 IS the right endpoint of cell 2700: the
# committed 2570 module is reused, never regenerated.
N0L_MODULE = "C1RouteACorrSharedN02701Minus2570"

LIT_LEFT = "(-stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240))"
LIT_RIGHT = "(-stripRadius2303 + (2702 : ℝ) * (2 * stripRadius2303 / 10240))"
LIT_MID = "(-stripRadius2303 + ((5403 : ℝ) / 2) * (2 * stripRadius2303 / 10240))"


# --------------------------------------------------------------------------
# modules 1+2: renamed derivative leaves and the 2543 midpoint render
# --------------------------------------------------------------------------

def derivatives_module():
    source = rename(read_dev("C1RouteABatchC02701MinusMidpoint2558"),
                    "batchC02701MinusMidpoint", 2558, "corrC02701MinusMidpoint",
                    RECORD)
    assert "batchC02701MinusMidpoint" not in source
    return source


def midpoint_bounds_module(selfcheck):
    """2543 render through the 2558 composer's rename chain, at cell 2701."""
    gen_path = ROOT / "scripts/generate_signed_midpoint_2543.py"
    raw = rename(read_dev("C1RouteABatchC02701MinusMidpoint2558"),
                 "batchC02701MinusMidpoint", 2558, "midpoint", 2543)
    namespace = derive_generator(gen_path, [] if selfcheck else CENTER_SWAPS)
    source, upper, charge = namespace["render"](source=raw, sigma=SIGMA)
    source = source.replace("C1RouteAMidpointDerivatives2543",
                            "C1RouteABatchC02701MinusMidpoint2558" if selfcheck
                            else MODULES["deriv"])
    if selfcheck:
        source = rename(source, "midpoint", 2543, "batchC02701MinusMidpoint", 2558)
        source = rename(source, "signedMidpoint", 2543,
                        "batchC02701MinusSignedMidpoint", 2558)
        source = source.replace("weightedPhysical_second_midpoint_le2543",
                                "batchC02701MinusPhysicalSecond2558")
        return wrap_source(source), upper, charge
    source = rename(source, "midpoint", 2543, "corrC02701MinusMidpoint", RECORD)
    source = rename(source, "signedMidpoint", 2543,
                    "corrC02701MinusSignedMidpoint", RECORD)
    source = source.replace("weightedPhysical_second_midpoint_le2543",
                            "corrC02701MinusPhysicalSecond2572")
    return wrap_source(finalize_correction(source)), upper, charge


# --------------------------------------------------------------------------
# module 3: the 2565 first-jet generator derived to the 2701 midpoint
# --------------------------------------------------------------------------

MID_POSITION = "corrC02701MinusMidpointPosition2572"
POSITION_SWAPS = [
    ("edgeMidpointPosition2548", MID_POSITION),
    ("import ConnesWeilRH.Dev.C1RouteABoundaryMidpoint2548",
     f"import ConnesWeilRH.Dev.{MODULES['mid']}"),
]


def finalize_jet(source):
    # runtime-dragged sections can carry cell-2700 position tokens the
    # source-level swaps cannot reach (the AGENTS 2bk trap); strip them here
    for old, new in POSITION_SWAPS:
        source = source.replace(old, new)
    source = finalize_correction(source)
    assert "edgeMidpointPosition2548" not in source, "position token survived"
    assert "C1RouteABoundaryMidpoint2548" not in source, "2548 import survived"
    return source


def firstjet_module(selfcheck):
    gen_path = ROOT / "scripts/generate_firstjet_midpoint_minus_2565.py"
    if selfcheck:
        namespace = derive_generator(gen_path, [])
        return namespace["build_parts"]()
    substitutions = CENTER_SWAPS + [
        ("GRID_INDEX = Q(5401, 2)", "GRID_INDEX = Q(5403, 2)"),
    ] + POSITION_SWAPS + [
        ('PREFIX = "fjmin"', 'PREFIX = "fjcm"'),
        ("RECORD = 2565", f"RECORD = {RECORD}"),
        ('TARGET = "C1RouteAFirstJetMidpointMinus2565"',
         f'TARGET = "{MODULES["jet"]}"'),
        ("firstJetMidpointMinus_triangle", "firstJetCorrMinus_triangle"),
        ("firstJetMidpointMinusUpper_le", "firstJetCorrMinusUpper_le"),
    ]
    namespace = derive_generator(gen_path, substitutions)
    state = namespace["build_parts"]()
    state["output"] = finalize_jet(state["output"])
    return state


# --------------------------------------------------------------------------
# module 4: the 2542 shared render at position 2702 (batch-owned)
# --------------------------------------------------------------------------

def shared_2702_module(selfcheck):
    gen_path = ROOT / "scripts/generate_adaptive_nodes_2542.py"
    tag = "N02702Minus"
    owner = ("batchN02702Minus", 2558, "C1RouteABatchN02702Minus2558")
    namespace = derive_generator(gen_path, [] if selfcheck else CENTER_SWAPS)
    source, info = namespace["render"](2702, -1, shared_node=True,
                                       shared_owner=owner)
    if selfcheck:
        source = rename(source, "adaptive" + tag, 2542,
                        "batchValueN02702Minus", 2558)
        return wrap_source(source), info
    source = rename(source, "adaptive" + tag, 2542, "corrSharedN02702Minus",
                    RECORD)
    return wrap_source(finalize_correction(source)), info


# --------------------------------------------------------------------------
# exact arithmetic for the assembly literals
# --------------------------------------------------------------------------

def third_leaves():
    vals = {}
    for part, pattern in (
            ("Left", r"batchC02701MinusLeftP\d{3}NormUpper2558"),
            ("Right", r"batchC02701MinusRightP\d{3}NormUpper2558"),
            ("Fourth", r"batchC02701MinusFourthP\d{3}Upper2558")):
        vals.update(scalar_defs(read_dev(
            f"C1RouteABatchC02701Minus{part}Bounds2558"
            if part != "Fourth" else
            "C1RouteABatchC02701MinusFourth2558"), pattern))
    assert len(vals) == 90, len(vals)
    half = STEP / 2
    return [max(vals[f"batchC02701MinusLeftP{i:03d}NormUpper2558"],
                vals[f"batchC02701MinusRightP{i:03d}NormUpper2558"])
            + vals[f"batchC02701MinusFourthP{i:03d}Upper2558"] * half
            for i in range(30)]


def committed_n0l_upper():
    vals = scalar_defs(read_dev(N0L_MODULE), r"corrSharedN02701MinusUpper2570")
    assert list(vals) == ["corrSharedN02701MinusUpper2570"], list(vals)
    return vals["corrSharedN02701MinusUpper2570"]


# --------------------------------------------------------------------------
# module 5: assembly clone of the committed 2570 module with direct
# grid-literal bridges replacing the 2548 edge-def machinery
# --------------------------------------------------------------------------

ASM_SWAPS = [
    # order-critical pairs go through placeholders: the 2701 kernel position
    # is BOTH the 2700 cell's right endpoint (source token) and the 2701
    # cell's left endpoint (target token)
    ("kernelN02700MinusPosition2555", "@@KL@@"),
    ("kernelN02701MinusPosition2555", "@@KR@@"),
    ("corrSharedN02700MinusSigned_le2570", "@@SL@@"),
    ("corrSharedN02701MinusSigned_le2570", "@@SR@@"),
    ("corrSharedN02700MinusPosition2570", "@@PL@@"),
    ("corrSharedN02701MinusPosition2570", "@@PR@@"),
    ("corrSharedN02700MinusUpper2570", "@@UL@@"),
    ("corrSharedN02701MinusUpper2570", "@@UR@@"),
    # batch leaf tokens: the whole 2700-minus family renames to 2701-minus
    ("batchC02700Minus", "batchC02701Minus"),
    # midpoint / jet / own-definition names
    ("corrC02700MinusSignedMidpointUpper_le2570",
     "corrC02701MinusSignedMidpointUpper_le2572"),
    ("corrC02700MinusSignedMidpointUpper2570",
     "corrC02701MinusSignedMidpointUpper2572"),
    ("corrC02700MinusMidpointPosition2570", MID_POSITION),
    ("firstJetCorrMinusUpper_le2570", "firstJetCorrMinusUpper_le2572"),
    ("fjcmUpper2570", "fjcmUpper2572"),
    ("corrSecondCell2700MinusSummand_le_2570",
     "corrSecondCell2701MinusSummand_le_2572"),
    ("corrSecondCell2700MinusUpper2570", "corrSecondCell2701MinusUpper2572"),
    ("corrThirdL1Sum_eq_2570", "corrThirdL1Sum_eq_2572"),
    ("corrThirdL1Cell2570", "corrThirdL1Cell2572"),
    ("corrThirdL1Sum2570", "corrThirdL1Sum2572"),
    ("corrThirdL1Upper2570", "corrThirdL1Upper2572"),
    ("corrThirdAggregate_bound2570", "corrThirdAggregate_bound2572"),
    ("corrThirdAggregate2570", "corrThirdAggregate2572"),
    ("corrCurvature_bound2570", "corrCurvature_bound2572"),
    # placeholder resolution
    ("@@KL@@", "kernelN02701MinusPosition2555"),
    ("@@KR@@", "batchN02702MinusPosition2558"),
    ("@@SL@@", "corrSharedN02701MinusSigned_le2570"),
    ("@@SR@@", "corrSharedN02702MinusSigned_le2572"),
    ("@@PL@@", "corrSharedN02701MinusPosition2570"),
    ("@@PR@@", "corrSharedN02702MinusPosition2572"),
    ("@@UL@@", "corrSharedN02701MinusUpper2570"),
    ("@@UR@@", "corrSharedN02702MinusUpper2572"),
]

BRIDGE_LEFT = (
    "  have hkl : kernelN02701MinusPosition2555 =\n"
    "      " + LIT_LEFT + " := by\n"
    "    norm_num [kernelN02701MinusPosition2555, stripRadius2303]\n"
    "  have hkr : batchN02702MinusPosition2558 =\n"
    "      " + LIT_RIGHT + " := by\n"
    "    norm_num [batchN02702MinusPosition2558, stripRadius2303]\n"
    "  rw [hkl, hkr] at hC")

BRIDGE_RIGHT = (
    "  have hsl : corrSharedN02701MinusPosition2570 =\n"
    "      " + LIT_LEFT + " := by\n"
    "    norm_num [corrSharedN02701MinusPosition2570, stripRadius2303]\n"
    "  have hsr : corrSharedN02702MinusPosition2572 =\n"
    "      " + LIT_RIGHT + " := by\n"
    "    norm_num [corrSharedN02702MinusPosition2572, stripRadius2303]\n"
    "  rw [hsl] at hJ0l\n"
    "  rw [hsr] at hJ0r\n"
    "  have hm : " + MID_POSITION + " =\n"
    "      " + LIT_MID + " := by\n"
    "    norm_num [" + MID_POSITION + ", stripRadius2303]\n"
    "  rw [hm] at hJ1")

WIDTH_OLD = ("  have hwidth : 0 ≤ ((edgeRightPosition2548 - edgeLeftPosition2548) / 2) := by\n"
             "    norm_num [edgeRightPosition2548, edgeLeftPosition2548]\n"
             "  have hC2 : signedCurvatureUpper2539 (-1 / 2) " + CENTER + " " + ERROR_DEF + """
      nodeModulation2541 edgeLeftPosition2548 edgeRightPosition2548 ≤
      corrC02701MinusSignedMidpointUpper2572 +
        corrThirdL1Sum2572 * ((edgeRightPosition2548 - edgeLeftPosition2548) / 2) :=""")

WIDTH_NEW = ("  have hwidth : 0 ≤\n"
             "      ((" + LIT_RIGHT + " -\n"
             "        " + LIT_LEFT + ") / 2) := by\n"
             "    norm_num [stripRadius2303]\n"
             "  have hC2 : signedCurvatureUpper2539 (-1 / 2) " + CENTER + " " + ERROR_DEF + """
      nodeModulation2541
      """ + LIT_LEFT + "\n"
             "      " + LIT_RIGHT + " ≤\n"
             "      corrC02701MinusSignedMidpointUpper2572 +\n"
             "        corrThirdL1Sum2572 * ((" + LIT_RIGHT + " -\n"
             "          " + LIT_LEFT + ") / 2) :=")

FINAL_NORM_OLD = ("""  norm_num [corrSecondCell2701MinusUpper2572, stripRadius2303,
    corrC02701MinusSignedMidpointUpper2572, corrThirdL1Upper2572, fjcmUpper2572,
    corrSharedN02701MinusUpper2570, corrSharedN02702MinusUpper2572, edgeLeftPosition2548,
    edgeRightPosition2548, edgeMidpointPosition2548]""")

FINAL_NORM_NEW = ("""  norm_num [corrSecondCell2701MinusUpper2572, stripRadius2303,
    corrC02701MinusSignedMidpointUpper2572, corrThirdL1Upper2572, fjcmUpper2572,
    corrSharedN02701MinusUpper2570, corrSharedN02702MinusUpper2572]""")

ASM_IMPORTS = "\n".join([
    "import ConnesWeilRH.Dev.C1RouteACorrectionSecondStrip2562",
    "import ConnesWeilRH.Dev.C1RouteABatchC02701MinusAssembly2558",
    "import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570",
    f"import ConnesWeilRH.Dev.{MODULES['mid']}",
    f"import ConnesWeilRH.Dev.{MODULES['jet']}",
    f"import ConnesWeilRH.Dev.{N0L_MODULE}",
    f"import ConnesWeilRH.Dev.{MODULES['n0r']}",
])


def patch(body, old, new):
    assert body.count(old) == 1, f"patch anchor not unique: {old[:60]!r}"
    return body.replace(old, new)


def build_assembly(mid_upper, l1_sum, jet_upper, n0l_upper, n0r_upper):
    step = 2 * R / 10240
    half = step / 2
    curvature = mid_upper + l1_sum * half
    pieces = (step * curvature,
              2 * abs(SIGMA) * step * (jet_upper + curvature * half),
              SIGMA ** 2 * (half * (n0l_upper + n0r_upper) + curvature * (step ** 3 / 12)))
    total = sum(pieces)
    bound = Q(ceil(total * 10 ** 12), 10 ** 12)
    assert bound >= total
    pilot = json.loads(read_text(PILOT))
    pilot_sum = pilot["correction_repricing"]["displays"]["piece_sum"]
    pilot_bound = Q(pilot["correction_repricing"]["exact"]["cell_bound"])
    assert abs(float(total) - pilot_sum) <= 1e-6, (float(total), pilot_sum)
    assert bound >= pilot_bound and bound - pilot_bound < Q(1, 10 ** 6), \
        (float(bound), float(pilot_bound))

    text = read_dev("C1RouteACorrectionSecondCell2700MinusCorr2570")
    body = text[text.index("namespace ConnesWeilRH.Dev"):]
    for old, new in ASM_SWAPS:
        body = body.replace(old, new)
    # numeric grid literals: placeholder first so the 2700->2701 rewrite
    # cannot collide with the original 2701 tokens
    for old, new in (
            ("(-stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240))", "@@L@@"),
            ("(-stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240))", "@@R@@"),
            ("(-stripRadius2303 + ((5401 : ℝ) / 2) * (2 * stripRadius2303 / 10240))", "@@M@@"),
            ("@@L@@", LIT_LEFT),
            ("@@R@@", LIT_RIGHT),
            ("@@M@@", LIT_MID)):
        body = body.replace(old, new)
    # proof patches: replace the 2548 edge-def bridging with direct
    # grid-literal norm_num bridges
    body = patch(body,
                 "  have hkl : kernelN02701MinusPosition2555 = edgeLeftPosition2548 := by\n"
                 "    norm_num [kernelN02701MinusPosition2555, edgeLeftPosition2548]\n"
                 "  have hkr : batchN02702MinusPosition2558 = edgeRightPosition2548 := by\n"
                 "    norm_num [batchN02702MinusPosition2558, edgeRightPosition2548]\n"
                 "  rw [hkl, hkr] at hC",
                 BRIDGE_LEFT)
    body = patch(body,
                 "  have hsl : corrSharedN02701MinusPosition2570 = edgeLeftPosition2548 := by\n"
                 "    norm_num [corrSharedN02701MinusPosition2570, edgeLeftPosition2548]\n"
                 "  have hsr : corrSharedN02702MinusPosition2572 = edgeRightPosition2548 := by\n"
                 "    norm_num [corrSharedN02702MinusPosition2572, edgeRightPosition2548]\n"
                 "  rw [hsl] at hJ0l\n"
                 "  rw [hsr] at hJ0r\n"
                 "  rw [edgeLeftGrid2548, edgeRightGrid2548, edgeMidpointGrid2548]",
                 BRIDGE_RIGHT)
    body = patch(body, WIDTH_OLD, WIDTH_NEW)
    body = patch(body, FINAL_NORM_OLD, FINAL_NORM_NEW)
    # cell-bound and L1 literals
    body = re.sub(r"(noncomputable def corrSecondCell2701MinusUpper2572 : ℝ :=\n)[^\n]+",
                  r"\1  ((" + str(bound.numerator) + " : ℝ) / " + str(bound.denominator) + ")",
                  body)
    aggregate_definition = body[body.index("noncomputable def corrThirdAggregate2572"):
                                body.index("theorem corrThirdAggregate_bound2572")]
    body, literal_count = re.subn(
                  r"noncomputable def corrThirdL1Upper2572 : ℝ :=\n(.*?)(?=\n\n(?:noncomputable def|theorem))",
                  "noncomputable def corrThirdL1Upper2572 : ℝ :=\n    " + chunked(l1_sum),
                  body, flags=re.S)
    assert literal_count == 1
    assert aggregate_definition in body, "literal replacement removed aggregate definition"
    body = body.replace(
        "  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570, correctionCoefficientError2570,",
        "  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,\n"
        "    correctionCoefficientError2570,")

    # hygiene: no 2548 edge machinery, no unresolved placeholders, no
    # 2700-flavored cell tokens survive
    assert "@@" not in body, "unresolved placeholder"
    for banned in ("edgeLeft", "edgeRight", "edgeMidpoint", "2548",
                   "C02700", "2700Minus", "(2700 : ℝ)", "(5401 : ℝ)",
                   "MinusCorr2570"):
        assert banned not in body, f"banned token {banned!r} survived"
    # every renamed batch leaf token must exist in the committed 2701 chain
    # (the P-scalars live in the Bounds/Fourth leaf modules, the aggregate
    # defs in the Assembly module, the midpoint defs in Midpoint)
    batch_src = "".join(read_dev(name) for name in (
        "C1RouteABatchC02701MinusAssembly2558",
        "C1RouteABatchC02701MinusMidpoint2558",
        "C1RouteABatchC02701MinusLeftBounds2558",
        "C1RouteABatchC02701MinusRightBounds2558",
        "C1RouteABatchC02701MinusFourth2558"))
    for token in set(re.findall(r"batchC02701Minus\w+2558", body)):
        assert token in batch_src, f"renamed token {token} not in committed 2701 chain"

    header = ASM_IMPORTS + """

/-!
Correction-pair single-cell certificate at production cell 2701, sigma=-1/2
(record 2572): the 2570 assembly parameterized to the adjacent grid cell --
the first cell-index generalization of the correction-pair machinery. The
left endpoint reuses the committed 2570 shared module at position 2701; the
right endpoint is the 2542 render at the batch-owned position 2702; the
2548 edge-def bridging of the 2700 module is replaced by direct grid-literal
norm_num bridges. Generated by scripts/generate_correction_pair_2572.py; the
exact aggregates cross-check the 2572 external repricing bitwise. Family
centers and errors stay explicit at the boxes; actual coefficients enter
only through the membership premise of the 2562 consumer theorems.
-/

namespace ConnesWeilRH.Dev"""
    out = header + body[body.index("\n\nopen"):]
    return wrap_source(out), bound, total


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "correction"
    selfcheck = mode == "selfcheck"
    key = "ideal_base_coefficient" if selfcheck else "ideal_correction_coefficient"

    mid_source, mid_upper, mid_charge = midpoint_bounds_module(selfcheck)
    jet_state = firstjet_module(selfcheck)
    n0r_source, n0r_info = shared_2702_module(selfcheck)

    if selfcheck:
        assert jet_state["output"] == read_dev("C1RouteAFirstJetMidpointMinus2565"), \
            "firstjet selfcheck mismatch"
        assert mid_source == read_dev("C1RouteABatchC02701MinusMidpointBounds2558"), \
            "midpoint bounds selfcheck mismatch"
        assert n0r_source == read_dev("C1RouteABatchValueN02702Minus2558"), \
            "shared n0r selfcheck mismatch"
        print("SELFCHECK midpoint/firstjet/shared2702 byte-equal to committed modules",
              flush=True)
        return

    jet_source = jet_state["output"]
    emit(MODULES["deriv"], derivatives_module())
    emit(MODULES["mid"], mid_source)
    emit(MODULES["jet"], jet_source)
    emit(MODULES["n0r"], n0r_source)

    # exact cross-checks against the 2572 pilot (and the committed 2569
    # pilot at the shared position 2701)
    pilot = json.loads(read_text(PILOT))
    corr_disp = pilot["correction_repricing"]["displays"]
    prior = json.loads(read_text(PRIOR_PILOT))
    centers = centers_of(key)
    fams_raw = json.loads(read_text(CAPTURE))["owner_capture"]["families_hex"]
    fams = [(Q.from_float(float.fromhex(v[0])) ** 2, Q.from_float(float.fromhex(v[1])))
            for v in fams_raw]
    from routea_derivative_pricing_2543 import multiplier
    from generate_complex_exp_node_2541 import rounded, add, mul, up as cup

    def aggregate(order, x):
        total, charge = (Q(0), Q(0)), Q(0)
        for family, c in zip(fams, centers):
            radius, theta = family
            center, error, _ = precision_evaluate(radius, theta, x, SIGMA, 160)
            if center == (Q(0), Q(0)):
                continue
            factor = (Q(1), Q(0)) if order == 0 else \
                multiplier(order, radius, theta, SIGMA, x)
            out = rounded(mul(factor, center))
            fam_radius = cup(sum(abs(v) for v in factor) * error + Q(1, 2 ** 99))
            total = add(total, mul(c, out))
            charge += sum(abs(v) for v in c) * fam_radius
        return total, charge

    checks = {}
    for name, order, x, pilot_key in (("j1", 1, X_MID, "j1_total"),
                                      ("mid", 2, X_MID, "mid_total"),
                                      ("n0l", 0, X_LEFT, "n0l_total"),
                                      ("n0r", 0, X_RIGHT, "n0r_total")):
        total, _ = aggregate(order, x)
        delta = abs(hypot(float(total[0]), float(total[1])) - corr_disp[pilot_key])
        checks[name] = delta
        assert delta < 1e-9, (name, delta)
    shared_total, _ = aggregate(0, X_LEFT)
    prior_n0r = prior["correction_repricing"]["displays"]["n0r_total"]
    checks["n0l_vs_2569"] = abs(hypot(float(shared_total[0]), float(shared_total[1]))
                                - prior_n0r)
    assert checks["n0l_vs_2569"] < 1e-9, checks["n0l_vs_2569"]
    print("PILOT_CROSSCHECK", json.dumps(checks), flush=True)

    # assembly literals
    l1 = third_leaves()
    l1_sum = sum((abs(c[0]) + abs(c[1]) + CHARGE_Q) * t
                 for c, t in zip(centers, l1))
    pilot_l1 = corr_disp["third_aggregate"]
    assert abs(float(l1_sum) - pilot_l1) < 1e-9, (float(l1_sum), pilot_l1)
    assembly, bound, total = build_assembly(mid_upper, l1_sum,
                                            jet_state["upper"],
                                            committed_n0l_upper(),
                                            Q(n0r_info["upper"]))
    emit(MODULES["asm"], assembly)
    result = dict(
        record=RECORD, mode=mode,
        reused_modules=dict(center="C1RouteACorrectionCenterNode2570",
                            boxes="C1RouteACorrectionCoefficientBoxes2570",
                            n0l=N0L_MODULE),
        mid_upper=str(mid_upper), mid_charge=str(mid_charge),
        jet_upper=str(jet_state["upper"]), jet_charge=str(jet_state["charge"]),
        n0l_upper=str(committed_n0l_upper()),
        n0r_upper=str(n0r_info["upper"]),
        third_l1_sum=str(l1_sum), third_l1_display=float(l1_sum),
        cell_bound=str(bound), cell_bound_display=float(bound),
        exact_total_display=float(total),
        modules=MODULES,
        source_sha256={f"ConnesWeilRH/Dev/{name}.lean": hashlib.sha256(
            (ROOT / f"ConnesWeilRH/Dev/{name}.lean").read_bytes()).hexdigest()
            for name in MODULES.values()})
    (ROOT / f"results/{RECORD}_generation_readback.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("READBACK", json.dumps({k: result[k] for k in (
        "mid_upper", "jet_upper", "n0l_upper", "n0r_upper", "third_l1_display")}),
        flush=True)


if __name__ == "__main__":
    main()
