"""Generate the real-exponential amplitude pin layer of entry (0, 3) (record 2657).

Each panel of the record-2624 GO route needs a certified two-sided pin for

    amp_k = exp(beta * center_k - 30 / (1 - center_k^2))

and the 46 vacuous-VAR cut-adjacent panels additionally need a pin for

    sup_k = exp(beta * half + 30 / (1 - center_k^2) - 30 / (1 - (|center_k|+half)^2)),

the supremum of the normalized local phase real part used by the
monotone-integral budget channel.  Both pins are instances of the
certified record-2620 real-exponential ball:

    compactExp_real_error2620 (argument : Q) (index) (hsmall) :
      |Real.exp(argument) - Re(chain)| <= radius,

so this record emits NO new engine - only per-panel literal pins of the
kernel-evaluated chain (python twin asserts the same inequality at 200
dps before emission).

Index: 20.  |argument| <= 285.2 gives |arg/2^20| <= 2.8e-4 <= 1/1000,
and the radius inflates by at most 2^20 * 1e-78 ~ 1.3e-72 relative -
four orders tighter than the 1e-51 assembly requirement.

Known behavior (asserted, not avoided): for |argument| >= ~220 the
320-bit fixed-point rounding underflows the stored value to zero and
the pin degrades to absolute looseness ~1.2e-96; the budget terms of
those panels are ~1e-89, five orders below the enclosure target, so
the degradation is immaterial.  All def/theorem names carry P{TAG}
(AGENTS 2co umbrella-collision law).

Scope: pin layer only.  No rotation pins (record 2658), no interval
assembly, no containment claim, no Producer GO, no SourceRH, no RH.
"""

import hashlib
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from offdiagonal_residual_pricing_2624 import (
    HALF_WIDTH, column_parameters, panel_center)

RECORD = 2657
INDEX = 20
ROUNDING_2620 = F(1, 2 ** 319)
TAIL_2620 = F(1, 10 ** 78)


def round_down(bits: int, q: F) -> F:
    return F(math.floor(q * (1 << bits))) / (1 << bits)


def round_up(bits: int, q: F) -> F:
    return -round_down(bits, -q)


def pair_round(a):
    return (round_down(320, a[0]), round_down(320, a[1]))


def pair_mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def horner19(z):
    cur = (F(1), F(0))
    for n in range(19):
        scale = F(1, 19 - n)
        cur = pair_round((
            F(1) + scale * z[0] * cur[0] - scale * z[1] * cur[1],
            scale * z[0] * cur[1] + scale * z[1] * cur[0]))
    return cur


def initial_state(z):
    return (horner19(z), TAIL_2620 + 19 * ROUNDING_2620)


def square_state(state):
    value, radius = state
    magnitude = abs(value[0]) + abs(value[1])
    return (
        pair_round(pair_mul(value, value)),
        round_up(400, radius * (2 * magnitude + radius) + ROUNDING_2620))


def compact_ball(z, index):
    state = initial_state(z)
    for _ in range(index):
        state = square_state(state)
    return state


def horner_trace(z):
    """Return the exact stored Horner states, including state zero."""
    states = [(F(1), F(0))]
    cur = states[0]
    for n in range(19):
        scale = F(1, 19 - n)
        cur = pair_round((
            F(1) + scale * z[0] * cur[0] - scale * z[1] * cur[1],
            scale * z[0] * cur[1] + scale * z[1] * cur[0]))
        states.append(cur)
    return states


def compact_trace(z, index):
    """Return the exact state after initialisation and each squaring."""
    hs = horner_trace(z)
    states = [(hs[-1], TAIL_2620 + 19 * ROUNDING_2620)]
    for _ in range(index):
        states.append(square_state(states[-1]))
    return hs, states


def q(value: F) -> str:
    assert value.denominator > 0
    return f"({value.numerator} / {value.denominator})"


MODULE_TEMPLATE = """import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel @@TAG@@ of entry (0, 3) (record @@RECORD@@)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^@@INDEX@@ * 1e-78 @@SUPNOTE@@
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel @@TAG@@. -/
def ampArg@@RECORD@@P@@TAG@@ : ℚ := @@N@@

/-- Stored center of the certified ball for `exp (ampArg@@RECORD@@P@@TAG@@)`. -/
def ampValue@@RECORD@@P@@TAG@@ : ℚ := @@V@@

/-- Stored radius of the certified ball for `exp (ampArg@@RECORD@@P@@TAG@@)`. -/
def ampRadius@@RECORD@@P@@TAG@@ : ℚ := @@R@@

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain@@RECORD@@P@@TAG@@ :
    compactExp2620 (ampArg@@RECORD@@P@@TAG@@ / (2 : ℚ) ^ @@INDEX@@, 0) @@INDEX@@
      = ((ampValue@@RECORD@@P@@TAG@@, 0), ampRadius@@RECORD@@P@@TAG@@) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin@@RECORD@@P@@TAG@@ :
    |Real.exp ((ampArg@@RECORD@@P@@TAG@@ : ℝ)) - (ampValue@@RECORD@@P@@TAG@@ : ℝ)|
      ≤ (ampRadius@@RECORD@@P@@TAG@@ : ℝ) := by
  have harg : ampArg@@RECORD@@P@@TAG@@ = @@N@@ := rfl
  have hsmall : |((ampArg@@RECORD@@P@@TAG@@ / (2 : ℚ) ^ @@INDEX@@ : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg@@RECORD@@P@@TAG@@ @@INDEX@@ hsmall
  rw [ampChain@@RECORD@@P@@TAG@@] at h
  simpa [embedPair2542] using h
@@SUPBLOCK@@
end ConnesWeilRH.Dev
"""

SUP_TEMPLATE = """
/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel @@TAG@@ (vacuous-VAR budget channel). -/
def supArg@@RECORD@@P@@TAG@@ : ℚ := @@SN@@

/-- Stored center of the certified ball for `exp (supArg@@RECORD@@P@@TAG@@)`. -/
def supValue@@RECORD@@P@@TAG@@ : ℚ := @@SV@@

/-- Stored radius of the certified ball for `exp (supArg@@RECORD@@P@@TAG@@)`. -/
def supRadius@@RECORD@@P@@TAG@@ : ℚ := @@SR@@

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain@@RECORD@@P@@TAG@@ :
    compactExp2620 (supArg@@RECORD@@P@@TAG@@ / (2 : ℚ) ^ @@INDEX@@, 0) @@INDEX@@
      = ((supValue@@RECORD@@P@@TAG@@, 0), supRadius@@RECORD@@P@@TAG@@) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin@@RECORD@@P@@TAG@@ :
    |Real.exp ((supArg@@RECORD@@P@@TAG@@ : ℝ)) - (supValue@@RECORD@@P@@TAG@@ : ℝ)|
      ≤ (supRadius@@RECORD@@P@@TAG@@ : ℝ) := by
  have harg : supArg@@RECORD@@P@@TAG@@ = @@SN@@ := rfl
  have hsmall : |((supArg@@RECORD@@P@@TAG@@ / (2 : ℚ) ^ @@INDEX@@ : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg@@RECORD@@P@@TAG@@ @@INDEX@@ hsmall
  rw [supChain@@RECORD@@P@@TAG@@] at h
  simpa [embedPair2542] using h
"""


def check_argument(argument: F, value: F, radius: F, tag: str, label: str) -> None:
    """Assert the pin at 200 dps before emission (the Lean theorem re-proves it)."""
    with mp.workdps(200):
        x = mp.mpf(argument.numerator) / mp.mpf(argument.denominator)
        v = mp.mpf(value.numerator) / mp.mpf(value.denominator)
        r = mp.mpf(radius.numerator) / mp.mpf(radius.denominator)
        diff = abs(mp.e ** x - v)
        assert diff <= r, f"{label} P{tag}: |exp-v| = {mp.nstr(diff, 12)} > r = {mp.nstr(r, 12)}"


def build_pin(argument: F, tag: str, label: str):
    # the Lean chain reduces internally: compactExp2620 (argument / 2^INDEX, 0) INDEX
    reduced = argument / (1 << INDEX)
    value_pair, radius = compact_ball((reduced, F(0)), INDEX)
    value = value_pair[0]
    check_argument(argument, value, radius, tag, label)
    return value, radius


def main():
    capture = json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    params = column_parameters(capture, 3)
    beta = params["beta"]
    analytic = json.loads(
        (ROOT / "results/2656_panel_analytic.json").read_text())
    vacuous = {p["panel"] for p in analytic["panels"] if F(p["var"]) >= 1}
    reports = []
    for index in range(190):
        tag = f"{index:03d}"
        center = panel_center(index)
        n_amp = beta * center - 30 / (1 - center * center)
        amp_value, amp_radius = build_pin(n_amp, tag, "amp")

        sup_block = ""
        n_sup = None
        if index in vacuous:
            bound = abs(center) + HALF_WIDTH
            n_sup = (beta * HALF_WIDTH + 30 / (1 - center * center)
                     - 30 / (1 - bound * bound))
            sup_value, sup_radius = build_pin(n_sup, tag, "sup")
            sup_block = (SUP_TEMPLATE
                         .replace("@@SN@@", q(n_sup))
                         .replace("@@SV@@", q(sup_value))
                         .replace("@@SR@@", q(sup_radius))
                         .replace("@@RECORD@@", str(RECORD))
                         .replace("@@TAG@@", tag)
                         .replace("@@INDEX@@", str(INDEX)))
            sup_note = f"supRe pin radius for panel {tag} likewise"
        else:
            sup_note = "no supRe pin (non-vacuous panel)"

        module = (MODULE_TEMPLATE
                  .replace("@@TAG@@", tag)
                  .replace("@@RECORD@@", str(RECORD))
                  .replace("@@INDEX@@", str(INDEX))
                  .replace("@@N@@", q(n_amp))
                  .replace("@@V@@", q(amp_value))
                  .replace("@@R@@", q(amp_radius))
                  .replace("@@SUPNOTE@@",
                           f"({sup_note})" if index in vacuous else sup_note)
                  .replace("@@SUPBLOCK@@", sup_block))
        out = ROOT / f"ConnesWeilRH/Dev/C1RouteAAmpPin{RECORD}P{tag}.lean"
        out.write_text(module, encoding="utf-8", newline="\n")
        reports.append(dict(
            panel=index, tag=tag, vacuous=index in vacuous,
            amp_arg=str(n_amp), amp_value=str(amp_value),
            amp_radius=str(amp_radius),
            underflowed=amp_value == 0,
            sup_arg=(str(n_sup) if index in vacuous else None)))

    imports = "\n".join(
        f"import ConnesWeilRH.Dev.C1RouteAAmpPin{RECORD}P{index:03d}"
        for index in range(190))
    umbrella = f"""{imports}

namespace ConnesWeilRH.Dev

/-!
# Real-exponential amplitude pin layer of entry (0, 3) (record {RECORD})

Umbrella module: imports all {190} per-panel pin modules emitted by
scripts/generate_amp_pins_2657.py.  The analytic-integral pilot at panel 109
does not replace this distinct amplitude pin.  Pin layer only; no rotation
pins, no assembly, no containment.
-/

end ConnesWeilRH.Dev
"""
    (ROOT / f"ConnesWeilRH/Dev/C1RouteAAmpPins{RECORD}.lean").write_text(
        umbrella, encoding="utf-8", newline="\n")

    audit_names = []
    for index in range(190):
        tag = f"{index:03d}"
        audit_names.extend((
            f"ampChain{RECORD}P{tag}",
            f"ampPin{RECORD}P{tag}",
        ))
        if index in vacuous:
            audit_names.extend((
                f"supChain{RECORD}P{tag}",
                f"supPin{RECORD}P{tag}",
            ))
    audit = "import ConnesWeilRH.Dev.C1RouteAAmpPins2657\n\n" + "\n".join(
        f"#print axioms ConnesWeilRH.Dev.{name}" for name in audit_names
    ) + "\n"
    (ROOT / f"ConnesWeilRH/Dev/C1RouteAAmpPinAudit{RECORD}.lean").write_text(
        audit, encoding="utf-8", newline="\n")

    underflow = sum(1 for r in reports if r["underflowed"])
    payload = dict(
        record=RECORD, entry=[0, 3], index=INDEX, panel_count=190,
        emitted=190,
        vacuous_count=len(vacuous), sup_pins=len(vacuous),
        underflowed_panels=underflow,
        engine="compactExp_real_error2620 (existing, record 2620)",
        generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        umbrella_module=f"C1RouteAAmpPins{RECORD}.lean",
        audit_module=f"C1RouteAAmpPinAudit{RECORD}.lean",
        audited_theorems=len(audit_names),
        panels=reports)
    (ROOT / f"results/{RECORD}_amp_pins.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"wrote {190} pin modules ({underflow} underflowed, "
          f"{payload['sup_pins']} supRe pins) + umbrella")


if __name__ == "__main__":
    main()
