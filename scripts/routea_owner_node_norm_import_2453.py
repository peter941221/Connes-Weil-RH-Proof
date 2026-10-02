"""2453: 11-position containment import and norm-bridge certificates.

Extends the 2452 point door to the position axis: at the nine exact
binary64 positions of the 2445/2449 endpoint certificate plus the two
strip endpoints ±1/2, emits per-family bump/phase rectangles (delta =
2^-200 outward margins, zero box at outside-support families) and proves
in Lean, per position and channel, the 30-family sum containment

    (sumFinset familyRectangles).Mem (correctedPhysical capCoef capMod pos)

through the 2437 factor interface and the 2436 owner consumer - the
2452 proof shape, now at 11 positions including both strip endpoints.

The per-position node-norm bounds N = max|re| + max|im| of the composed
sum rectangles are computed exactly, recorded in the artifact, and bound
by the independent pin check (which recomposes them from the parsed
literals with the same interval semantics).  The general Lean consumer
for these bounds, `norm_le_of_rect_mem_2453`, ships in the committed
bridge module; the Lean-side corner evaluation that would attach N to
the sumFinset term inside Lean hit a simp expansion loop and is
registered as the open implementation seam (record 2453).

Also emits a single-position probe module (p05) used to validate the
proof shapes with a fast focused build before the full build.

Scope: finite point-box import at 11 positions; no strip norm, no
continuum/quadrature transfer, no producer GO, no RH claim.
"""
import hashlib
import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
CERT = ROOT / "results/2445_routea_family_endpoint_certificate.json"
LEAN_OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerNodeNormImport2453.lean"
AUDIT_OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerNodeNormImport2453Audit.lean"
PROBE_OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerNodeNormImport2453Probe.lean"
PROBE_AUDIT_OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerNodeNormImport2453ProbeAudit.lean"
ARTIFACT_OUT = ROOT / "results/2453_owner_node_norm_import.json"

DPS_WORK = 90
DELTA = Fraction(1, 2 ** 200)
EXTRA_POSITIONS = (Fraction(-1, 2), Fraction(1, 2))


def load_owner():
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = [(Fraction(float.fromhex(width)), Fraction(float.fromhex(modulation)))
                for width, modulation in capture["families_hex"]]
    base = [(Fraction(float.fromhex(re_)), Fraction(float.fromhex(im_)))
            for re_, im_ in capture["base_hex"]]
    corr = [(Fraction(float.fromhex(re_)), Fraction(float.fromhex(im_)))
            for re_, im_ in capture["corr_hex"]]
    return families, base, corr, capture


def load_positions():
    cert = json.loads(CERT.read_text())
    seen = []
    for row in cert["rows"]:
        fr = Fraction.from_float(row["position"]) if row["position"] != 0.0 \
            else Fraction(0)
        if fr not in seen:
            seen.append(fr)
    seen.extend(EXTRA_POSITIONS)
    seen.sort()
    return seen


def mpf_to_fraction(v):
    sign, man, exp, _bc = mp.mpf(v)._mpf_
    if man == 0:
        return Fraction(0)
    f = Fraction(man) * (Fraction(2) ** exp)
    return -f if sign else f


def mp_fraction(fr):
    return mp.mpf(fr.numerator) / mp.mpf(fr.denominator)


def exact_exp(fraction):
    mp.mp.dps = DPS_WORK
    approx = mp.exp(mp.mpf(fraction.numerator) / mp.mpf(fraction.denominator))
    return mpf_to_fraction(approx)


def exact_cos_sin(fraction):
    mp.mp.dps = DPS_WORK
    x = mp.mpf(fraction.numerator) / mp.mpf(fraction.denominator)
    return mpf_to_fraction(mp.cos(x)), mpf_to_fraction(mp.sin(x))


def interval_mul(a, b):
    corners = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(corners), max(corners)


def interval_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def interval_sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def point_interval(x):
    return x, x


def composed_hull(coef_re, coef_im, bump_box, phase_boxes):
    coef_re_i, coef_im_i = point_interval(coef_re), point_interval(coef_im)
    phase_re_i, phase_im_i = phase_boxes
    rr = interval_sub(interval_mul(coef_re_i, interval_mul(bump_box, phase_re_i)),
                      interval_mul(coef_im_i, interval_mul(bump_box, phase_im_i)))
    ii = interval_add(interval_mul(coef_re_i, interval_mul(bump_box, phase_im_i)),
                      interval_mul(coef_im_i, interval_mul(bump_box, phase_re_i)))
    return rr, ii


def reference_term(coef_re, coef_im, bump, cos_v, sin_v):
    re_val = coef_re * bump * cos_v - coef_im * bump * sin_v
    im_val = coef_re * bump * sin_v + coef_im * bump * cos_v
    return re_val, im_val


def build_position_boxes(families, pos):
    """Per family: bump box (zero box outside support) and phase boxes."""
    bumps, phases = [], []
    for width, modulation in families:
        radius = width * width
        if abs(pos) >= radius:
            bumps.append((Fraction(0) - DELTA, Fraction(0) + DELTA))
        else:
            quotient = 1 - (pos / radius) ** 2
            bump = exact_exp(Fraction(-30) / quotient)
            bumps.append((bump - DELTA, bump + DELTA))
        cos_v, sin_v = exact_cos_sin(modulation * pos)
        phases.append(((cos_v - DELTA, cos_v + DELTA),
                       (sin_v - DELTA, sin_v + DELTA)))
    return bumps, phases


def real_literal(fr):
    num = f"({fr.numerator} : ℚ)" if fr.denominator == 1 \
        else f"({fr.numerator} : ℚ) / {fr.denominator}"
    return f"({num} : ℝ)"


def complex_literal(re_, im_):
    return f"⟨{real_literal(re_)}, {real_literal(im_)}⟩"


def position_tag(index):
    return f"p{index:02d}"


def position_block(tag, pos, bumps, phases):
    """Lean declarations for one position (shared rects, both channels)."""
    bump_lines = ",\n    ".join(
        "{{ reLo := {lo}, reHi := {hi}, imLo := ((0 : ℚ) : ℝ),"
        " imHi := ((0 : ℚ) : ℝ) }}".format(lo=real_literal(lo), hi=real_literal(hi))
        for lo, hi in bumps)
    phase_lines = ",\n    ".join(
        "{{ reLo := {rl}, reHi := {rh}, imLo := {il}, imHi := {ih} }}".format(
            rl=real_literal(re_box[0]), rh=real_literal(re_box[1]),
            il=real_literal(im_box[0]), ih=real_literal(im_box[1]))
        for re_box, im_box in phases)

    parts = []
    parts.append(f"noncomputable def pos2453{tag} : ℝ := {real_literal(pos)}")
    parts.append(
        f"noncomputable def bumpRect2453{tag} : Fin 30 → ComplexRect2427 :=\n"
        f"  ![{bump_lines}]")
    parts.append(
        f"noncomputable def phaseRect2453{tag} : Fin 30 → ComplexRect2427 :=\n"
        f"  ![{phase_lines}]")
    parts.append(
        f"noncomputable def bumpValue2453{tag} (k : Fin 30)\n"
        f"    (h : (bumpRect2453{tag} k).Mem\n"
        f"      (widthBump (storedWidth k ^ 2) pos2453{tag} : ℂ)) :\n"
        f"    DirectedComplexValue2433 :=\n"
        f"  ⟨(widthBump (storedWidth k ^ 2) pos2453{tag} : ℂ),"
        f" bumpRect2453{tag} k, h⟩")
    parts.append(
        f"noncomputable def phaseValue2453{tag} (k : Fin 30)\n"
        f"    (h : (phaseRect2453{tag} k).Mem\n"
        f"      (Complex.exp (capMod2453 k * pos2453{tag} * Complex.I))) :\n"
        f"    DirectedComplexValue2433 :=\n"
        f"  ⟨Complex.exp (capMod2453 k * pos2453{tag} * Complex.I),"
        f" phaseRect2453{tag} k, h⟩")
    for channel in ("base", "corr"):
        cap = "capBaseCoef2453" if channel == "base" else "capCorrCoef2453"
        coef = "baseCoefValue2453" if channel == "base" else "corrCoefValue2453"
        ch = channel.capitalize()
        parts.append(
            f"theorem familyRect2453{ch}{tag}_mem (k : Fin 30)\n"
            f"    (hBump : (bumpRect2453{tag} k).Mem\n"
            f"      (widthBump (storedWidth k ^ 2) pos2453{tag} : ℂ))\n"
            f"    (hPhase : (phaseRect2453{tag} k).Mem\n"
            f"      (Complex.exp (capMod2453 k * pos2453{tag} * Complex.I))) :\n"
            f"    ((({coef} k).product (bumpValue2453{tag} k hBump)).product\n"
            f"      (phaseValue2453{tag} k hPhase)).rectangle.Mem\n"
            f"      (externalFamilyValue2344 ({cap} k) (capMod2453 k)\n"
            f"        (storedWidth k ^ 2) pos2453{tag}) :=\n"
            f"  externalFamilyValue_mem_of_factor_cert2437 _ _ _ _ (by\n"
            f"    simp only [DirectedComplexValue2433.product, {coef},\n"
            f"      bumpValue2453{tag}, phaseValue2453{tag}]\n"
            f"    rw [externalFamilyValue2344_eq_familyTerm, Complex.ofReal_mul])")
        parts.append(
            f"theorem correctedPhysical_mem_pos2453{ch}{tag}\n"
            f"    (hBump : ∀ k : Fin 30, (bumpRect2453{tag} k).Mem\n"
            f"      (widthBump (storedWidth k ^ 2) pos2453{tag} : ℂ))\n"
            f"    (hPhase : ∀ k : Fin 30, (phaseRect2453{tag} k).Mem\n"
            f"      (Complex.exp (capMod2453 k * pos2453{tag} * Complex.I))) :\n"
            f"    (ComplexRect2427.sumFinset\n"
            f"      (fun k => ((({coef} k).product (bumpValue2453{tag} k (hBump k))).product\n"
            f"        (phaseValue2453{tag} k (hPhase k))).rectangle)"
            f" Finset.univ).Mem\n"
            f"      (correctedPhysical {cap} capMod2453 pos2453{tag}) :=\n"
            f"  correctedPhysical_mem_of_family_rect2436 {cap} capMod2453\n"
            f"    pos2453{tag} _\n"
            f"    (fun k => familyRect2453{ch}{tag}_mem k (hBump k) (hPhase k))")
    return "\n\n".join(parts)


def coef_defs(base, corr, families):
    coef_lines_b = ",\n    ".join(complex_literal(re_, im_) for re_, im_ in base)
    coef_lines_c = ",\n    ".join(complex_literal(re_, im_) for re_, im_ in corr)
    mod_lines = ",\n    ".join(real_literal(mod) for _, mod in families)
    return f"""noncomputable def capBaseCoef2453 : Fin 30 → ℂ :=
  ![{coef_lines_b}]

noncomputable def capCorrCoef2453 : Fin 30 → ℂ :=
  ![{coef_lines_c}]

noncomputable def capMod2453 : Fin 30 → ℝ :=
  ![{mod_lines}]

noncomputable def baseCoefValue2453 (k : Fin 30) : DirectedComplexValue2433 :=
  ⟨capBaseCoef2453 k, ComplexRect2427.point (capBaseCoef2453 k),
    ComplexRect2427.point_mem _⟩

noncomputable def corrCoefValue2453 (k : Fin 30) : DirectedComplexValue2433 :=
  ⟨capCorrCoef2453 k, ComplexRect2427.point (capCorrCoef2453 k),
    ComplexRect2427.point_mem _⟩"""


def module_text(header, body):
    return f"""{header}

set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

{body}

end ConnesWeilRH.Dev
"""


HEADER = """import ConnesWeilRH.Dev.C1RouteAOwnerTermInterface
import ConnesWeilRH.Dev.C1RouteANormBridge2453

/-  2453: containment import of the captured owner (2275) at 11
positions (nine exact binary64 certificate positions and the strip
endpoints ±1/2).  The coefficient/modulation literals are exact dyadic
bindings of the capture; the rectangle literals are bound to
`results/2453_owner_node_norm_import.json` by the independent pin
check, which also certifies the per-position node-norm bounds recorded
there.  The bump and phase containment fields are the 2333 hypothesis
class.  The exact-rational literals are machine-generated; the long-line
linter is disabled for this file only.  -/"""

PROBE_HEADER = """import ConnesWeilRH.Dev.C1RouteAOwnerTermInterface
import ConnesWeilRH.Dev.C1RouteANormBridge2453

/-  2453 probe: single-position (p05) shape validation for the import
module.  Scaffolding, not part of the committed record.  -/"""


def main():
    families, base, corr, capture = load_owner()
    positions = load_positions()
    assert len(positions) == 11, f"expected 11 positions, got {len(positions)}"

    checks, failures = [], []
    blocks = []
    sum_records = {}
    for idx, pos in enumerate(positions):
        tag = position_tag(idx)
        bumps, phases = build_position_boxes(families, pos)
        for channel, coefficients in (("base", base), ("corr", corr)):
            re_box, im_box = point_interval(Fraction(0)), point_interval(Fraction(0))
            for k in range(30):
                coef_re, coef_im = coefficients[k]
                rr, ii = composed_hull(coef_re, coef_im, bumps[k], phases[k])
                radius = families[k][0] * families[k][0]
                if abs(pos) >= radius:
                    bump = Fraction(0)
                else:
                    bump = exact_exp(Fraction(-30) /
                                     (1 - (pos / radius) ** 2))
                cos_v, sin_v = exact_cos_sin(families[k][1] * pos)
                re_ref, im_ref = reference_term(coef_re, coef_im, bump,
                                                cos_v, sin_v)
                ok = rr[0] <= re_ref <= rr[1] and ii[0] <= im_ref <= ii[1]
                checks.append({"channel": channel, "family": k, "tag": tag,
                               "contains_reference": ok,
                               "margin_re": float(min(re_ref - rr[0],
                                                      rr[1] - re_ref)),
                               "margin_im": float(min(im_ref - ii[0],
                                                      ii[1] - im_ref))})
                if not ok:
                    failures.append(f"{channel}[{k}]@{tag}")
                re_box = interval_add(re_box, rr)
                im_box = interval_add(im_box, ii)
            mre = max(abs(re_box[0]), abs(re_box[1]))
            mim = max(abs(im_box[0]), abs(im_box[1]))
            sum_records[f"{channel}_{tag}"] = {
                "re": [str(re_box[0]), str(re_box[1])],
                "im": [str(im_box[0]), str(im_box[1])],
                "N": str(mre + mim),
            }
        blocks.append(position_block(tag, pos, bumps, phases))

    full_body = coef_defs(base, corr, families) + "\n\n" + \
        "\n\n".join(blocks)
    LEAN_OUT.write_text(module_text(HEADER, full_body), encoding="utf-8")

    audit_names = []
    for idx in range(11):
        tag = position_tag(idx)
        for channel in ("Base", "Corr"):
            audit_names.append(f"correctedPhysical_mem_pos2453{channel}{tag}")
    audit_body = "\n".join(f"#print axioms {name}" for name in audit_names)
    AUDIT_OUT.write_text(module_text(
        "import ConnesWeilRH.Dev.C1RouteAOwnerNodeNormImport2453", audit_body),
        encoding="utf-8")

    probe_idx = 5
    probe_body = coef_defs(base, corr, families) + "\n\n" + \
        blocks[probe_idx]
    PROBE_OUT.write_text(module_text(PROBE_HEADER, probe_body), encoding="utf-8")
    probe_names = [f"correctedPhysical_mem_pos2453{ch}p{probe_idx:02d}"
                   for ch in ("Base", "Corr")]
    PROBE_AUDIT_OUT.write_text(module_text(
        "import ConnesWeilRH.Dev.C1RouteAOwnerNodeNormImport2453Probe",
        "\n".join(f"#print axioms {name}" for name in probe_names)),
        encoding="utf-8")

    artifact = {
        "record": 2453,
        "verdict": "OWNER-NODE-NORM-IMPORT-CERTIFICATES-COMPLETE" if not failures
        else "OWNER-NODE-NORM-IMPORT-CONTAINMENT-FAILURES",
        "scope": ("containment import at 11 positions (9 exact binary64 "
                  "certificate positions + strip endpoints +-1/2) through "
                  "the 2433/2437/2436 door; node-norm bounds N recorded and "
                  "pin-certified; the 2453 bridge is the committed Lean "
                  "consumer; no strip norm, no quadrature import, no "
                  "producer GO, no RH claim"),
        "positions": [str(p) for p in positions],
        "position_count": len(positions),
        "capture_md5s": {"base": capture["base_md5"],
                         "corr": capture["corr_md5"]},
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "certificate_sha256": hashlib.sha256(CERT.read_bytes()).hexdigest(),
        "producer_source_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "lean_module_sha256": hashlib.sha256(
            LEAN_OUT.read_bytes()).hexdigest(),
        "delta": f"{DELTA.numerator}/{DELTA.denominator}",
        "dps_work": DPS_WORK,
        "containment_checks": checks,
        "containment_failures": failures,
        "sum_boxes_and_bounds": sum_records,
        "producer_go": False,
        "rh_claim": False,
    }
    ARTIFACT_OUT.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")

    print(json.dumps({
        "verdict": artifact["verdict"],
        "positions": len(positions),
        "families_checked": len(checks),
        "failures": failures,
        "lean_module_bytes": LEAN_OUT.stat().st_size,
    }, indent=2))


if __name__ == "__main__":
    main()
