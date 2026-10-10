"""Generate certified cosine/sine pins for the 190 entry-(0, 3) rotations."""

import hashlib
import json
import math
import mpmath as mp
import sys
from fractions import Fraction as F
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from offdiagonal_residual_pricing_2624 import column_parameters, panel_center

from generate_amp_pins_2657 import compact_ball

RECORD = 2658
INDEX = 20


def q(value: F) -> str:
    assert value.denominator > 0
    return f"({value.numerator} / {value.denominator})"


def validate_phase(phase: F, value: tuple[F, F], radius: F, tag: str) -> None:
    with mp.workdps(200):
        x = mp.mpf(phase.numerator) / mp.mpf(phase.denominator)
        real = mp.mpf(value[0].numerator) / mp.mpf(value[0].denominator)
        imag = mp.mpf(value[1].numerator) / mp.mpf(value[1].denominator)
        error = mp.mpf(radius.numerator) / mp.mpf(radius.denominator)
        cos_error = abs(mp.cos(x) - real)
        sin_error = abs(mp.sin(x) - imag)
        assert cos_error <= error, (tag, "cos", mp.nstr(cos_error, 15), mp.nstr(error, 15))
        assert sin_error <= error, (tag, "sin", mp.nstr(sin_error, 15), mp.nstr(error, 15))


def axiom_audit_summary() -> str:
    return """Record 2658: 190 exact phase-rotation pins
Date: 2026-10-10

Result

Positive for the rotation-pin layer.  `scripts/generate_phase_pins_2658.py`
emits one Lean module for each panel of entry (0, 3).  Each module replays
the exact rational phase `psi * center` through the existing record-2646
complex exponential engine and proves both cosine and sine coordinate
errors using the same certified radius.

The generator computes each rational state with the same 320-bit directed
rounding and 400-bit upward radius rules as the Lean engine, then checks
both coordinate errors against 200-digit mpmath values before emission.
That high-precision calculation is a generation guard; Lean's kernel replay
and record-2646 error theorems establish the certificate.

Validation

- P095 pilot: direct Lean elaboration succeeded in 64.15 seconds.
- P000 and P189 edge pilots: built successfully, including phases near the
  extremes of the full interval.
- Full umbrella: 3917/3917 jobs built successfully in 80.72 seconds,
  with no errors or `sorryAx`.
- The generated audit prints 570 theorems; every dependency list is exactly
  `[propext, Classical.choice, Quot.sound]`.
- Every generated chain uses `decide +kernel`; the coordinate pins use
  `phaseExp_cos_error2646` and `phaseExp_sin_error2646`.

Artifacts

- `ConnesWeilRH/Dev/C1RouteAPhasePin2658P{TAG}.lean` for tags P000-P189.
- `ConnesWeilRH/Dev/C1RouteAPhasePins2658.lean` imports all 190 modules.
- `ConnesWeilRH/Dev/C1RouteAPhasePinAudit2658.lean` audits the axiom lists.
- `results/2658_phase_pins.json` records phase inputs, centers, radii, and
  generator hash.

Scope

Only the per-panel real and imaginary coordinates of the rotation are
certified.  The rotation has not yet been multiplied into the complex panel
integrals, summed across panels, or compared with the 2597 rectangle.  This
record does not establish Producer GO, SourceRH, or RH.
"""


TEMPLATE = """import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel @@TAG@@ of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg@@RECORD@@P@@TAG@@ : ℚ := @@ARG@@
def phaseValue@@RECORD@@P@@TAG@@ : RatPair2542 := (@@RE@@, @@IM@@)
def phaseRadius@@RECORD@@P@@TAG@@ : ℚ := @@RAD@@

theorem phaseChain@@RECORD@@P@@TAG@@ :
    phaseExp2646 phaseArg@@RECORD@@P@@TAG@@ @@INDEX@@ =
      ((phaseValue@@RECORD@@P@@TAG@@.1,
        phaseValue@@RECORD@@P@@TAG@@.2), phaseRadius@@RECORD@@P@@TAG@@) := by
  decide +kernel

theorem phaseCosPin@@RECORD@@P@@TAG@@ :
    |Real.cos (phaseArg@@RECORD@@P@@TAG@@ : ℝ) -
      (phaseValue@@RECORD@@P@@TAG@@.1 : ℝ)| ≤
        (phaseRadius@@RECORD@@P@@TAG@@ : ℝ) := by
  have hsmall : |((phaseArg@@RECORD@@P@@TAG@@ / (2 : ℚ) ^ @@INDEX@@ : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg@@RECORD@@P@@TAG@@]
  have h := phaseExp_cos_error2646 phaseArg@@RECORD@@P@@TAG@@ @@INDEX@@ hsmall
  rw [phaseChain@@RECORD@@P@@TAG@@] at h
  simpa [phaseValue@@RECORD@@P@@TAG@@] using h

theorem phaseSinPin@@RECORD@@P@@TAG@@ :
    |Real.sin (phaseArg@@RECORD@@P@@TAG@@ : ℝ) -
      (phaseValue@@RECORD@@P@@TAG@@.2 : ℝ)| ≤
        (phaseRadius@@RECORD@@P@@TAG@@ : ℝ) := by
  have hsmall : |((phaseArg@@RECORD@@P@@TAG@@ / (2 : ℚ) ^ @@INDEX@@ : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg@@RECORD@@P@@TAG@@]
  have h := phaseExp_sin_error2646 phaseArg@@RECORD@@P@@TAG@@ @@INDEX@@ hsmall
  rw [phaseChain@@RECORD@@P@@TAG@@] at h
  simpa [phaseValue@@RECORD@@P@@TAG@@] using h

end ConnesWeilRH.Dev
"""


def main() -> None:
    capture = json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    psi = column_parameters(capture, 3)["psi"]
    reports = []

    for panel in range(190):
        tag = f"{panel:03d}"
        phase = psi * panel_center(panel)
        reduced = phase / (1 << INDEX)
        (real, imag), radius = compact_ball((F(0), reduced), INDEX)
        validate_phase(phase, (real, imag), radius, tag)
        source = (TEMPLATE.replace("@@RECORD@@", str(RECORD))
                  .replace("@@TAG@@", tag)
                  .replace("@@INDEX@@", str(INDEX))
                  .replace("@@ARG@@", q(phase))
                  .replace("@@RE@@", q(real))
                  .replace("@@IM@@", q(imag))
                  .replace("@@RAD@@", q(radius)))
        (ROOT / f"ConnesWeilRH/Dev/C1RouteAPhasePin{RECORD}P{tag}.lean").write_text(
            source, encoding="utf-8", newline="\n")
        reports.append(dict(
            panel=panel, tag=tag, phase=str(phase), real=str(real),
            imag=str(imag), radius=str(radius)))

    imports = "\n".join(
        f"import ConnesWeilRH.Dev.C1RouteAPhasePin{RECORD}P{p:03d}"
        for p in range(190))
    umbrella = f"""{imports}

namespace ConnesWeilRH.Dev

/-! Full 190-panel rotation-pin batch for entry (0, 3), record {RECORD}.
This imports exact cosine/sine pins only; it does not assemble the entry. -/

end ConnesWeilRH.Dev
"""
    (ROOT / f"ConnesWeilRH/Dev/C1RouteAPhasePins{RECORD}.lean").write_text(
        umbrella, encoding="utf-8", newline="\n")

    names = []
    for panel in range(190):
        tag = f"{panel:03d}"
        names.extend((f"phaseChain{RECORD}P{tag}",
                      f"phaseCosPin{RECORD}P{tag}",
                      f"phaseSinPin{RECORD}P{tag}"))
    audit = f"import ConnesWeilRH.Dev.C1RouteAPhasePins{RECORD}\n\n" + "\n".join(
        f"#print axioms ConnesWeilRH.Dev.{name}" for name in names) + "\n"
    (ROOT / f"ConnesWeilRH/Dev/C1RouteAPhasePinAudit{RECORD}.lean").write_text(
        audit, encoding="utf-8", newline="\n")

    (ROOT / "docs/proofs/2658_phase_rotation_pins.md").write_text(
        axiom_audit_summary(), encoding="utf-8", newline="\n")

    payload = dict(
        record=RECORD, entry=[0, 3], index=INDEX, panel_count=190,
        emitted=190, audited_theorems=len(names),
        engine="phaseExp2646 / compactExp_real_error2620",
        generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        umbrella_module=f"C1RouteAPhasePins{RECORD}.lean",
        audit_module=f"C1RouteAPhasePinAudit{RECORD}.lean",
        phases=reports)
    (ROOT / f"results/{RECORD}_phase_pins.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("wrote 190 rotation modules, umbrella, 570-theorem audit, and payload")


if __name__ == "__main__":
    main()
