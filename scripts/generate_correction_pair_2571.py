"""Regenerate the cell2700-plus correction-second chain at the correction pair.

Record 2571 stage B: the sigma=+1/2 twin of the 2570 minus regeneration.
The committed plus certificate (2563) rests on the coarse 2551 boundary
envelope, whose statement is instantiated at the base pair only; stage A
gave the plus sign the fine 2558-style aggregate chain at cell 2700, and
this composer emits the correction-pair modules over the shared 2570
correction boxes and center node (1e-28): plus midpoint derivative leaves
(renamed stage-A copies), the plus midpoint lane, the plus first-jet lane
(the 2565 generator derived to the plus sign under the 2567 remainder law),
two shared endpoint aggregates, and the assembly in the 2565 shape.

Fidelity gates mirror 2570: (1) every generator clone derives by token
substitution validated by the remainder law; (2) --selfcheck reproduces
committed base-pair modules byte for byte (the stage-A plus MidpointBounds
through the 2558 rename chain, the 2556 shared Plus endpoints, and the
minus 2565 first-jet module for the shared slicing machinery); (3) in
correction mode every exact signed sum matches the 2571 plus repricing
bitwise; (4) sign hygiene: no (-1/2) literal and no Minus token survives
in any emitted module.
"""
from fractions import Fraction as Q
from math import ceil, hypot
import hashlib
import json
import re
import sys

from generate_complex_exp_node_2541 import ROOT, CAPTURE, real, pair as complex_pair, add, mul
from price_boundary_precision_2547 import precision_evaluate
from format_lean_source_2553 import wrap_source

from generate_correction_pair_2570 import (
    CENTER, BOX, ERROR_DEF, CHARGE_Q, CENTER_SWAPS, RUNTIME_TOKEN_SWAPS,
    CORRECTION_IMPORTS, finalize_correction, derive_generator, rename,
    read_text, read_dev, centers_of, chunked, emit)

RECORD = 2571
PILOT = ROOT / "results/2571_cell2700_plus_correction_repricing.json"

SIGMA = Q(1, 2)
R = Q(65536001, 10 ** 7)
STEP = 2 * R / 10240
X_MID = -R + Q(5401, 2) * STEP
X_LEFT = -R + 2700 * STEP
X_RIGHT = -R + 2701 * STEP

MODULES = dict(
    deriv="C1RouteACorrPlusMidpointDerivatives2571",
    mid="C1RouteACorrMidpointBounds2700Plus2571",
    jet="C1RouteACorrFirstJetMidpointPlus2571",
    n0l="C1RouteACorrSharedN02700Plus2571",
    n0r="C1RouteACorrSharedN02701Plus2571",
    asm="C1RouteACorrectionSecondCell2700PlusCorr2571")

STAGE_A = [f"C1RouteABatchC02700Plus{part}2558" for part in
           ("Midpoint", "LeftBounds", "RightBounds", "MidpointBounds",
            "Fourth", "Assembly", "Integral")]


# --------------------------------------------------------------------------
# derived renderers (2567 remainder-validated generator clones)
# --------------------------------------------------------------------------

def derivatives_module():
    """Renamed copy of the coefficient-independent plus midpoint leaves."""
    source = rename(read_dev("C1RouteABatchC02700PlusMidpoint2558"),
                    "batchC02700PlusMidpoint", 2558, "corrC02700PlusMidpoint",
                    RECORD)
    assert "batchC02700PlusMidpoint" not in source
    return source


def midpoint_bounds_module(selfcheck):
    """2543 render over the stage-A plus leaves, at 2571."""
    gen_path = ROOT / "scripts/generate_signed_midpoint_2543.py"
    raw = rename(read_dev("C1RouteABatchC02700PlusMidpoint2558"),
                 "batchC02700PlusMidpoint", 2558, "midpoint", 2543)
    namespace = derive_generator(gen_path, [] if selfcheck else CENTER_SWAPS)
    source, upper, charge = namespace["render"](source=raw, sigma=SIGMA)
    source = source.replace("C1RouteAMidpointDerivatives2543",
                            "C1RouteABatchC02700PlusMidpoint2558" if selfcheck
                            else MODULES["deriv"])
    if selfcheck:
        source = rename(source, "midpoint", 2543, "batchC02700PlusMidpoint", 2558)
        source = rename(source, "signedMidpoint", 2543,
                        "batchC02700PlusSignedMidpoint", 2558)
        source = source.replace("weightedPhysical_second_midpoint_le2543",
                                "batchC02700PlusPhysicalSecond2558")
        assert "(-1/2)" not in source
        return wrap_source(source), upper, charge
    source = rename(source, "midpoint", 2543, "corrC02700PlusMidpoint", RECORD)
    source = rename(source, "signedMidpoint", 2543,
                    "corrC02700PlusSignedMidpoint", RECORD)
    source = source.replace("weightedPhysical_second_midpoint_le2543",
                            "corrC02700PlusPhysicalSecond2571")
    source = finalize_correction(source)
    assert "(-1/2)" not in source
    return wrap_source(source), upper, charge


# the 2565 generator derived to the plus sign: the sigma constant, the Lean
# sigma literal, the prefix/record/target, the exported lemma names, and the
# slice-section sign rewrites. The sliced 2541 statement is natively plus
# (its (1/2) literals only needed flipping FOR the minus module), so the
# slice sign rewrite becomes inert and the weightedPhysical rewrites keep
# the (1/2) spelling.
FIRSTJET_SWAPS = CENTER_SWAPS + [
    ("SIGMA = Q(-1, 2)", "SIGMA = Q(1, 2)"),
    ('LEAN_SIGMA = "(-1/2)"', 'LEAN_SIGMA = "(1/2)"'),
    ('PREFIX = "fjmin"', 'PREFIX = "fjcp"'),
    ("RECORD = 2565", f"RECORD = {RECORD}"),
    ('TARGET = "C1RouteAFirstJetMidpointMinus2565"',
     f'TARGET = "{MODULES["jet"]}"'),
    ("firstJetMidpointMinus_triangle", "firstJetCorrPlus_triangle"),
    ("firstJetMidpointMinusUpper_le", "firstJetCorrPlusUpper_le"),
    ("weightedPhysicalFirstJetMidpointMinus_le", "weightedPhysicalCorrPlusFirstJet_le"),
    ('body = body.replace("(1/2)", "(-1/2)")',
     'body = body.replace("(1/2)", "(1/2)")'),
    ("weightedPhysical2539 (-1/2) coefficients nodeModulation2541 edgeMidpointPosition2548",
     "weightedPhysical2539 (1/2) coefficients nodeModulation2541 edgeMidpointPosition2548"),
    ("iteratedDeriv 1 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)",
     "iteratedDeriv 1 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)"),
]


def firstjet_module(selfcheck):
    """2565 first-jet generator clone derived to the plus sign."""
    gen_path = ROOT / "scripts/generate_firstjet_midpoint_minus_2565.py"
    if selfcheck:
        namespace = derive_generator(gen_path, [])
        return namespace["build_parts"]()
    namespace = derive_generator(gen_path, FIRSTJET_SWAPS)
    state = namespace["build_parts"]()
    output = state["output"] = finalize_correction(state["output"])
    assert "(-1/2)" not in output and "Minus" not in output and "fjmin" not in output
    assert "(1/2)" in output
    return state


def shared_module(index, selfcheck):
    """2542 shared render at the plus sign, at 2571."""
    gen_path = ROOT / "scripts/generate_adaptive_nodes_2542.py"
    tag = f"N{index:05d}Plus"
    owner = ("kernel" + tag, 2555, "C1RouteAKernel" + tag + "2555")
    namespace = derive_generator(gen_path, [] if selfcheck else CENTER_SWAPS)
    source, info = namespace["render"](index, 1, shared_node=True,
                                       shared_owner=owner)
    if selfcheck:
        source = rename(source, "adaptive" + tag, 2542, "shared" + tag, 2556)
        return wrap_source(source), info
    source = rename(source, "adaptive" + tag, 2542, "corrShared" + tag, RECORD)
    return wrap_source(finalize_correction(source)), info


# --------------------------------------------------------------------------
# exact arithmetic for the assembly literals
# --------------------------------------------------------------------------

def third_leaves():
    """Plus per-family third envelopes from the stage-A modules."""
    from price_cell2700_minus_2565 import scalar_defs
    vals = {}
    for part, pattern in (
            ("Left", r"batchC02700PlusLeftP\d{3}NormUpper2558"),
            ("Right", r"batchC02700PlusRightP\d{3}NormUpper2558"),
            ("Fourth", r"batchC02700PlusFourthP\d{3}Upper2558")):
        vals.update(scalar_defs(read_dev(
            f"C1RouteABatchC02700Plus{part}Bounds2558"
            if part != "Fourth" else
            "C1RouteABatchC02700PlusFourth2558"), pattern))
    assert len(vals) == 90, len(vals)
    half = STEP / 2
    return [max(vals[f"batchC02700PlusLeftP{i:03d}NormUpper2558"],
                vals[f"batchC02700PlusRightP{i:03d}NormUpper2558"])
            + vals[f"batchC02700PlusFourthP{i:03d}Upper2558"] * half
            for i in range(30)]


# --------------------------------------------------------------------------
# assembly module: textual clone of the 2565 assembly with sign/name swaps
# --------------------------------------------------------------------------

# order matters: the (: ℝ) sigma spelling must be swapped before the bare
# spelling, and the per-family leaves swap by prefix so the ninety explicit
# P000..P029 tokens all move at once.
SIGMA_SWAPS = [
    ("(-1 / 2 : ℝ)", "(1 / 2 : ℝ)"),
    ("(-1 / 2)", "(1 / 2)"),
]

ASM_NAMES = [
    ("correctionSecondCell2700MinusSummand_le_2565",
     "corrSecondCell2700PlusSummand_le_2571"),
    ("correctionSecondCell2700MinusUpper2565", "corrSecondCell2700PlusUpper2571"),
    ("correctionThirdL1Sum_eq_2565", "corrThirdL1Sum_eq_2571"),
    ("correctionThirdL1Cell2565", "corrThirdL1Cell2571"),
    ("correctionThirdL1Sum2565", "corrThirdL1Sum2571"),
    ("correctionThirdL1Upper2565", "corrThirdL1Upper2571"),
    ("batchC02700MinusCurvature_bound2558", "corrCurvature_bound2571"),
    ("batchC02700MinusThirdAggregate2558", "corrThirdAggregate2571"),
    ("batchC02700MinusSignedMidpointUpper2558",
     "corrC02700PlusSignedMidpointUpper2571"),
    ("batchC02700MinusThirdCell", "batchC02700PlusThirdCell"),
    ("batchC02700MinusLeft", "batchC02700PlusLeft"),
    ("batchC02700MinusRight", "batchC02700PlusRight"),
    ("batchC02700MinusFourth", "batchC02700PlusFourth"),
    ("kernelN02700MinusPosition2555", "kernelN02700PlusPosition2555"),
    ("kernelN02701MinusPosition2555", "kernelN02701PlusPosition2555"),
    ("firstJetMidpointMinusUpper_le2565", "firstJetCorrPlusUpper_le2571"),
    ("fjminUpper2565", "fjcpUpper2571"),
    ("sharedN02700MinusSigned_le2556", "corrSharedN02700PlusSigned_le2571"),
    ("sharedN02701MinusSigned_le2556", "corrSharedN02701PlusSigned_le2571"),
    ("sharedN02700MinusPosition2556", "corrSharedN02700PlusPosition2571"),
    ("sharedN02701MinusPosition2556", "corrSharedN02701PlusPosition2571"),
    ("sharedN02700MinusUpper2556", "corrSharedN02700PlusUpper2571"),
    ("sharedN02701MinusUpper2556", "corrSharedN02701PlusUpper2571"),
    ("baseCoefficientCenter2540", CENTER),
    ("baseCoefficientError2540", ERROR_DEF),
    ("baseCoefficientBox2540", BOX),
]

ASM_IMPORTS = "\n".join([
    "import ConnesWeilRH.Dev.C1RouteACorrectionSecondStrip2562",
    "import ConnesWeilRH.Dev.C1RouteABoundaryLeft2548",
    "import ConnesWeilRH.Dev.C1RouteABoundaryRight2548",
    "import ConnesWeilRH.Dev.C1RouteABoundaryMidpoint2548",
    "import ConnesWeilRH.Dev.C1RouteABatchC02700PlusAssembly2558",
    "import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570",
    "import ConnesWeilRH.Dev.C1RouteACorrMidpointBounds2700Plus2571",
    "import ConnesWeilRH.Dev.C1RouteACorrFirstJetMidpointPlus2571",
    "import ConnesWeilRH.Dev.C1RouteACorrSharedN02700Plus2571",
    "import ConnesWeilRH.Dev.C1RouteACorrSharedN02701Plus2571",
])

ASM_INSERT = """
noncomputable def corrThirdAggregate2571 : ℝ :=
  ∑ i : Fin 30, (‖""" + CENTER + """ i‖ + """ + ERROR_DEF + """ i) *
      batchC02700PlusThirdCell2558 i

theorem corrThirdAggregate_bound2571 :
    signedThirdCellUpper2539 (1/2) """ + CENTER + " " + ERROR_DEF + """
      nodeModulation2541 kernelN02700PlusPosition2555 kernelN02701PlusPosition2555 ≤
          corrThirdAggregate2571 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (batchC02700PlusThirdCell_bound2558 i)
    (add_nonneg (norm_nonneg _) (by norm_num [""" + ERROR_DEF + """]))

theorem corrCurvature_bound2571 :
    signedCurvatureUpper2539 (1/2) """ + CENTER + " " + ERROR_DEF + """
      nodeModulation2541 kernelN02700PlusPosition2555 kernelN02701PlusPosition2555 ≤
        corrC02700PlusSignedMidpointUpper2571 + corrThirdAggregate2571 *
          ((kernelN02701PlusPosition2555 - kernelN02700PlusPosition2555) / 2) := by
  have hm : (kernelN02700PlusPosition2555 + kernelN02701PlusPosition2555) / 2 =
      corrC02700PlusMidpointPosition2571 := by
    norm_num [kernelN02700PlusPosition2555, kernelN02701PlusPosition2555,
        corrC02700PlusMidpointPosition2571]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add corrC02700PlusSignedMidpointUpper_le2571
  apply mul_le_mul_of_nonneg_right corrThirdAggregate_bound2571
  norm_num [kernelN02701PlusPosition2555, kernelN02700PlusPosition2555]
"""


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
    assert abs(float(total) - pilot_sum) <= 1e-9, (float(total), pilot_sum)
    assert bound >= pilot_bound and bound - pilot_bound < Q(1, 10 ** 6), \
        (float(bound), float(pilot_bound))

    text = read_dev("C1RouteACorrectionSecondCell2700Minus_2565")
    body = text[text.index("namespace ConnesWeilRH.Dev"):]
    for old, new in SIGMA_SWAPS:
        body = body.replace(old, new)
    assert "(-1 / 2" not in body
    for old, new in ASM_NAMES:
        body = body.replace(old, new)
    assert "Minus" not in body, "minus token survived the plus clone"
    # swap the two numeric literals
    body = re.sub(r"(noncomputable def corrSecondCell2700PlusUpper2571 : ℝ :=\n)[^\n]+",
                  r"\1  ((" + str(bound.numerator) + " : ℝ) / " + str(bound.denominator) + ")",
                  body)
    body = re.sub(r"noncomputable def corrThirdL1Upper2571 : ℝ :=\n(.*?)(?=\n\ntheorem)",
                  "noncomputable def corrThirdL1Upper2571 : ℝ :=\n    " + chunked(l1_sum),
                  body, flags=re.S)
    # insert the aggregate/curvature sections before the L1 sum theorem
    body = body.replace("theorem corrThirdL1Sum_eq_2571",
                        ASM_INSERT + "\ntheorem corrThirdL1Sum_eq_2571", 1)
    header = ASM_IMPORTS + """

/-!
Correction-pair single-cell certificate at production cell 2700, sigma=+1/2
(record 2571, stage B): the 2565 assembly shape regenerated over the
record-2338 ideal_correction_coefficient centers with the 1e-28 error of
records 2568/2569, replacing the coarse 2551 envelope of the committed plus
certificate 2563 with the stage-A fine plus aggregate chain. Generated by
scripts/generate_correction_pair_2571.py; the exact aggregates cross-check
the 2571 plus repricing bitwise. Family centers and errors stay explicit at
the boxes; actual coefficients enter only through the membership premise of
the 2562 consumer theorems.
-/

namespace ConnesWeilRH.Dev"""
    out = header + body[body.index("\n\nopen"):] if "\n\nopen" in body else header + body
    return out, bound, total


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "correction"
    selfcheck = mode == "selfcheck"
    key = "ideal_base_coefficient" if selfcheck else "ideal_correction_coefficient"

    mid_source, mid_upper, mid_charge = midpoint_bounds_module(selfcheck)
    jet_state = firstjet_module(selfcheck)
    n0l_source, n0l_info = shared_module(2700, selfcheck)
    n0r_source, n0r_info = shared_module(2701, selfcheck)

    if selfcheck:
        assert jet_state["output"] == read_dev("C1RouteAFirstJetMidpointMinus2565"), \
            "firstjet slicing selfcheck mismatch"
        assert mid_source == read_dev("C1RouteABatchC02700PlusMidpointBounds2558"), \
            "plus midpoint bounds selfcheck mismatch"
        assert n0l_source == read_dev("C1RouteASharedN02700Plus2556"), \
            "shared n0l plus selfcheck mismatch"
        assert n0r_source == read_dev("C1RouteASharedN02701Plus2556"), \
            "shared n0r plus selfcheck mismatch"
        print("SELFCHECK midpoint/firstjet-machinery/shared byte-equal to "
              "committed base-pair modules", flush=True)
        return

    jet_source = jet_state["output"]
    emit(MODULES["deriv"], derivatives_module())
    emit(MODULES["mid"], mid_source)
    emit(MODULES["jet"], jet_source)
    emit(MODULES["n0l"], n0l_source)
    emit(MODULES["n0r"], n0r_source)

    # exact cross-checks against the 2571 plus repricing
    pilot = json.loads(read_text(PILOT))
    corr_disp = pilot["correction_repricing"]["displays"]
    centers = centers_of(key)
    fams_raw = json.loads(read_text(CAPTURE))["owner_capture"]["families_hex"]
    fams = [(Q.from_float(float.fromhex(v[0])) ** 2, Q.from_float(float.fromhex(v[1])))
            for v in fams_raw]
    from routea_derivative_pricing_2543 import multiplier
    from generate_complex_exp_node_2541 import rounded, up as cup

    def aggregate(order, x):
        total, charge = (Q(0), Q(0)), Q(0)
        for family, c in zip(fams, centers):
            radius, theta = family
            center, error, _ = precision_evaluate(radius, theta, x, SIGMA, 160)
            if center == (Q(0), Q(0)):
                continue
            factor = (Q(1), Q(0)) if order == 0 else multiplier(order, radius, theta, SIGMA, x)
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
    print("PILOT_CROSSCHECK", json.dumps(checks), flush=True)

    # assembly literals
    l1 = third_leaves()
    l1_sum = sum((abs(c[0]) + abs(c[1]) + CHARGE_Q) * t
                 for c, t in zip(centers, l1))
    pilot_l1 = pilot["correction_repricing"]["displays"]["third_aggregate"]
    assert abs(float(l1_sum) - pilot_l1) < 1e-9, (float(l1_sum), pilot_l1)
    assembly, bound, total = build_assembly(mid_upper, l1_sum,
                                            jet_state["upper"],
                                            Q(n0l_info["upper"]),
                                            Q(n0r_info["upper"]))
    emit(MODULES["asm"], assembly)
    result = dict(
        record=RECORD, mode=mode, sigma="1/2",
        mid_upper=str(mid_upper), mid_charge=str(mid_charge),
        jet_upper=str(jet_state["upper"]), jet_charge=str(jet_state["charge"]),
        n0l_upper=str(n0l_info["upper"]), n0r_upper=str(n0r_info["upper"]),
        third_l1_sum=str(l1_sum), third_l1_display=float(l1_sum),
        cell_bound=str(bound), cell_bound_display=float(bound),
        exact_total_display=float(total),
        modules=MODULES,
        stage_a_modules=STAGE_A,
        source_sha256={f"ConnesWeilRH/Dev/{name}.lean": hashlib.sha256(
            (ROOT / f"ConnesWeilRH/Dev/{name}.lean").read_bytes()).hexdigest()
            for name in list(MODULES.values())})
    (ROOT / f"results/{RECORD}_generation_readback.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("READBACK", json.dumps({k: result[k] for k in (
        "mid_upper", "jet_upper", "n0l_upper", "n0r_upper", "third_l1_display")}),
        flush=True)


if __name__ == "__main__":
    main()
