"""Generate exact rational scalar exponential certificates for actual panel 094."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH/Dev"
COORDINATE_BITS = 320
RADIUS_BITS = 400
SCALING_STEPS = 20


def round_down(value, bits):
    scaled = Fraction(value) * 2 ** bits
    return Fraction(scaled.numerator // scaled.denominator, 2 ** bits)


def round_up(value, bits):
    return -round_down(-Fraction(value), bits)


def compact_scalar(argument):
    argument = Fraction(argument)
    scaled = argument / 2 ** SCALING_STEPS
    if abs(scaled) > Fraction(1, 1000):
        raise ValueError("scaled exponent exceeds the proved tiny-argument regime")
    center = Fraction(1)
    for index in range(19):
        center = round_down(1 + scaled * center / (19 - index), COORDINATE_BITS)
    radius = Fraction(1, 10 ** 78) + 19 * Fraction(1, 2 ** 319)
    states = [(center, radius)]
    for _ in range(SCALING_STEPS):
        radius = round_up(radius * (2 * abs(center) + radius) + Fraction(1, 2 ** 319), RADIUS_BITS)
        center = round_down(center * center, COORDINATE_BITS)
        states.append((center, radius))
    return states


def rational_expr(value):
    value = Fraction(value)
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def get_data():
    path = ROOT / "results/2275_gap_owner_audit.json"
    witness_path = ROOT / "results/2351_moment_matrix_witness.json"
    capture = json.loads(path.read_text())["owner_capture"]
    width = Fraction(float.fromhex(capture["families_hex"][0][0]))
    modulation = Fraction(float.fromhex(capture["families_hex"][0][1]))
    node_real, node_imag = map(lambda value: Fraction(float.fromhex(value)), capture["nodes_hex"][0])
    if node_imag + modulation != 0:
        raise ValueError("actual (0,0) phase does not cancel")
    radius = width ** 2
    witness = json.loads(witness_path.read_text())
    if radius != Fraction(witness["support_radii_exact"][0]):
        raise ValueError("physical radius does not match the committed owner witness")
    beta = node_real * radius
    center, half_width, cut = Fraction(9, 200), Fraction(1, 200), Fraction(9, 10)
    if -cut + (2 * 94 + 1) * half_width != center:
        raise ValueError("panel center differs from the committed partition")
    phase = -30 / (1 - center ** 2) + beta * center
    growth = 2 * (abs(beta) + 60 * (abs(center) + half_width) /
                  (1 - (abs(center) + half_width) ** 2) ** 2) * half_width
    edge = -30 / (1 - cut ** 2) + abs(beta)
    return {"radius": radius, "beta": beta, "phase": phase, "growth": growth, "edge": edge,
            "capture_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "witness_sha256": hashlib.sha256(witness_path.read_bytes()).hexdigest()}


def owner_source(data):
    definitions = "\n".join(f"def moment{label}2620 : ℚ := {rational_expr(data[key])}"
                            for label, key in (("Radius", "radius"), ("Beta", "beta"),
                                               ("PanelPhase", "phase"), ("PanelGrowth", "growth"),
                                               ("EdgeArgument", "edge")))
    return f"""import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

{definitions}

theorem momentRadius_owner2620 :
    (momentRadius2620 : ℝ) = storedWidth 0 ^ 2 := by
  norm_num [momentRadius2620, storedWidth]

theorem momentBeta_owner2620 :
    (momentBeta2620 : ℝ) = (capturedNodes2584 0).re * (storedWidth 0 ^ 2) := by
  norm_num [momentBeta2620, capturedNodes2584, storedWidth]

theorem momentPanelPhase_owner2620 :
    (momentPanelPhase2620 : ℝ) = momentPhase2619
      ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 200) 0 := by
  norm_num [momentPanelPhase2620, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2620 :
    (momentPanelGrowth2620 : ℝ) = 2 * momentPhaseSlopeUpper2619
      ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2620, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

theorem momentEdgeArgument_owner2620 :
    (momentEdgeArgument2620 : ℝ) = -30 / (1 - (9 / 10 : ℝ) ^ 2) +
      |(capturedNodes2584 0).re * (storedWidth 0 ^ 2)| := by
  norm_num [momentEdgeArgument2620, capturedNodes2584, storedWidth]

end ConnesWeilRH.Dev
"""


def scalar_source(label, argument_name, argument, expression, owner_theorem, digits):
    center, radius = compact_scalar(argument)[-1]
    prefix = f"momentScalar{label}2620"
    return f"""import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def {prefix}Input : RatPair2542 := ({argument_name} / (2 : ℚ) ^ 20, 0)

def {prefix}Expected : RatState2542 :=
  (({rational_expr(center)}, 0), {rational_expr(radius)})

theorem {prefix}_replay :
    compactExp2620 {prefix}Input 20 = {prefix}Expected := by
  decide +kernel

theorem {prefix}_error :
    |Real.exp ({expression}) - ({prefix}Expected.1.1 : ℝ)| ≤
      ({prefix}Expected.2 : ℝ) := by
  have hsmall : |(({argument_name} / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [{argument_name}]
  have h := compactExp_real_error2620 {argument_name} 20 hsmall
  change |Real.exp ({argument_name} : ℝ) -
    ((compactExp2620 {prefix}Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 {prefix}Input 20).2 : ℝ) at h
  rw [{prefix}_replay] at h
  simpa only [{owner_theorem}] using h

theorem {prefix}_radius_le :
    ({prefix}Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ {digits} := by
  norm_num [{prefix}Expected]

end ConnesWeilRH.Dev
"""


def generated_sources(data):
    beta = "((capturedNodes2584 0).re * (storedWidth 0 ^ 2))"
    cases = (
        ("Amplitude", "momentPanelPhase2620", "phase", f"momentPhase2619 {beta} (9 / 200) 0", "momentPanelPhase_owner2620", 80),
        ("Growth", "momentPanelGrowth2620", "growth", f"2 * momentPhaseSlopeUpper2619 {beta} (9 / 200) (1 / 200) * (1 / 200)", "momentPanelGrowth_owner2620", 70),
        ("Edge", "momentEdgeArgument2620", "edge", f"-30 / (1 - (9 / 10 : ℝ) ^ 2) + |{beta}|", "momentEdgeArgument_owner2620", 90),
    )
    sources = {"C1RouteAMomentScalarOwner2620.lean": owner_source(data)}
    for label, argument_name, key, expression, owner_theorem, digits in cases:
        sources[f"C1RouteAMomentScalar{label}2620Panel094.lean"] = scalar_source(
            label, argument_name, data[key], expression, owner_theorem, digits)
    engine_theorems = ("expHorner2541_error_tiny2620", "embedPair_round_error2620",
                       "hornerRat_error2620", "initialState_error2620", "squareState_error2620",
                       "compactExp_error2620", "compactExp_real_error2620")
    owner_theorems = ("momentRadius_owner2620", "momentBeta_owner2620", "momentPanelPhase_owner2620",
                      "momentPanelGrowth_owner2620", "momentEdgeArgument_owner2620")
    audit = [f"import ConnesWeilRH.Dev.C1RouteAMomentScalar{case[0]}2620Panel094" for case in cases]
    audit.append("import ConnesWeilRH.Dev.C1RouteAMomentActualEdge2620")
    audit += [""] + [f"#print axioms ConnesWeilRH.Dev.{name}" for name in engine_theorems + owner_theorems]
    for label, *_ in cases:
        audit += [f"#print axioms ConnesWeilRH.Dev.momentScalar{label}2620_{suffix}"
                  for suffix in ("replay", "error", "radius_le")]
    audit.append("#print axioms ConnesWeilRH.Dev.actualMomentEntry000_bothEdgeCharge_le2620")
    sources["C1RouteAMomentScalarAudit2620.lean"] = "\n".join(audit) + "\n"
    return sources


def main():
    data = get_data()
    for filename, source in generated_sources(data).items():
        (DEV / filename).write_text(source, encoding="utf-8", newline="\n")
    payload = {"record": 2620, "panel": 94, "center_exact": "9/200", "half_width_exact": "1/200",
               "coordinate_bits": COORDINATE_BITS, "radius_bits": RADIUS_BITS,
               "scaling_steps": SCALING_STEPS,
               "capture_sha256": data["capture_sha256"], "witness_sha256": data["witness_sha256"],
               "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "scalars": {key: {"argument_exact": str(data[key]),
                                 "center_exact": str(compact_scalar(data[key])[-1][0]),
                                 "radius_exact": str(compact_scalar(data[key])[-1][1])}
                           for key in ("phase", "growth", "edge")},
               "lean_verified": False, "polynomial_table_lean_verified": False,
               "actual_entry_containment_lean_verified": False, "producer_go": False, "rh_claim": False}
    (ROOT / "results/2620_moment_scalar_payload.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("generated five scalar-owner/replay/audit modules", flush=True)


if __name__ == "__main__":
    main()
