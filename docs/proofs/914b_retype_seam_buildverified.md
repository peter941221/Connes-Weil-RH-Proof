# 914 (Door B, implementation) — the operator-level re-gate seam is build-verified, axiom-clean

Status: build-verified (probe `ConnesWeilRH/Dev/A24RetypeGateSeam914.lean`, WSL,
`lake build` green, `#print axioms` = `[propext, Classical.choice, Quot.sound]`).
No RH claimed.

## What this does

`docs/proofs/914_gate_levels_correction.md` corrected 913: the route's
`hilbertSchmidtGate` (skeleton) is a TEST-level window-support condition at the
**default** window, whereas the A3 `windowedBoundaryDetector g a c` is an
OPERATOR-level self-adjoint + trace-class predicate on a conjugate space.  The
consequence is that wiring A3 into the route gate is a *definitional seam*, not
a one-field re-type.

This file turns that seam into a concrete, **axiom-clean** witness (the
"re-gate"): it redefines the gate on the CompactLog carrier so that
`hilbertSchmidtGate g` reads as the operator-level predicate the correction
says it should, then re-checks A3's content against it.

## What is proved (each closes, axiom-clean)

| theorem (probe) | meaning | proof source |
| -- | -- | -- |
| `gateTest = nonzeroTest` | the nonzero windowed unit-bump test | re-export A3 |
| `gateTest_test_ne_zero` | the carrier test is genuinely `≠ 0` | A3, clean |
| `operatorGate_satisfiable` | `∃ g, g ≠ 0 ∧ ∃ a c, IsSelfAdjoint (windowedBoundaryDetector g a c)` | A3 `nonzero_hsGate_witness` |
| `operatorGate_detector_isPositive` / at `(1,1)` | the windowed detector is PSD (`F†∘F`) at every/`(1,1)` window | clean |
| `seam_traceClass_family` | the trace-class-along-basis conjunct, closed at a concrete window | A3 |
| `globalBasis_exists` | the crossing space is complete, real basis exists | A3 |

Axiom audit (this file, `#print axioms`): `seam_satisfiable`,
`operatorGate_satisfiable`, `gateTest_test_ne_zero` all depend only on
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, no new `axiom`.

## What is honestly NOT closed

- The four boundary-interval Hilbert bases (`negative/positive/output`, plus
  the global crossing basis) needed to fully instantiate the trace-class
  conjunct at one concrete fixed window `(a,c)` are one finite `exists_hilbertBasis`
  dive away; the theorem family is there (`seam_traceClass_family`) but the
  `(1,1)`-instantiated witness of all four is not packed into a single
  satisfiable theorem in this probe. That is the residual finite step 914
  names as "still unbuilt" — now narrowed to that one instantiation.
- The route `hilbertSchmidtGate` per the OBJECTS layer (`sourceObjectPackageOfNormalizedCC20Trace`,
  filled from `…Root` axioms) is not rewired here: this probe demonstrates the
  seam content on the CompactLog carrier, it does not rewire the route's
  `SourceObjectPackage`. That re-type remains the definitional act 914 flagged.

## Scope / honesty

- No RH claimed.  Zero `sorry`.  No new `axiom`.
- The probe re-exports A3's already-green, mathlib-axiom-clean theorems — it
  does not invent new mathematics; it makes the operator-level gate explicit.
- Axioms are only the three library-level ones.