# 914 — Correction to 913: the gate formalizes at two different levels; the seam is definitional, not a lift

Status: self-attack on 913. No RH claimed. No `sorry`, no new axiom.

## Why this file exists

913 argued the B-lane does not re-hit the A-lane generic-λ wall, and cited A3
(`A3NonZeroCompactLogGateProbe`) as a concrete witness "of the gate". Sweeping
the seam forward (per the 913 "Next steps" step 1) surfaced a factual
over-claim in that wording:

**The A3 witness and the route's `hilbertSchmidtGate` are different predicates
at different levels.** Mapping one onto the other is a *definitional seam*, not
a one-field re-type — and that seam is the real, still-open B-lane step.
This file does not claim it is built.

## The two gates are genuinely different

| | carrier | predicate | nature |
| -- | -- | -- | -- |
| **Route `hilbertSchmidtGate`** (skeleton) | test `g : TestFunction` | `supportInWindow g I ∧ fourierSupportInWindow g I` | test-level support/window set inclusion, at the **default window** |
| **A3 witness** | operator | `IsSelfAdjoint (windowedBoundaryDetector g a c)` ∧ HS-trace-class-along | operator-level self-adjoint + trace-class |

Where each lives in the code:

- `Dev/UnconditionalSkeleton.lean:178-188` defines
  `normalizedCoreTraceClassFromTheorems g = supportInWindow …`
  and `normalizedCoreCyclicLegalFromTheorems g = fourierSupportInWindow …`,
  so (`:277-282`) `hilbertSchmidtGate g = theSupportInWindow g ∧ theFourierSupportInWindow g`
  at `normalizedCoreSourceWindowWitnessFromTheorems = defaultWindow`
  (`:110-112`).
- `Dev/A3NonNonComparableLogGateProbe.lean` builds a nonzero `CompactLogTest` and
  proves the **operator** `windowedBoundaryDetector g a c` on
  `cc20GlobalLogCrossingL2` is self-adjoint (`hsGate_selfAdjoint_witness`) and
  HS-trace-class-along-basis (`hsGate_traceClass_witness`).

These do not identify: the route gate is a **support-set-in-window** test on
the function `g`, the A3 gate is a **trace-class operator** on a Hilbert space.
The word `hilbertSchmidtGate` names two different statements.

Plus a data-level mismatch on the window parameter: the skeleton's predicate
is at `defaultWindow`, while A3's operator is over boundary windows `(a,c)`;
these are not the same `Window` (ConcreteWindow/`defaultWindow in the skeleton
vs the boundary-intervals `a,c` in A3).

## What 913 got right (keep)

- `hilbertSchmidtGate = traceClass ∧ cyclicLegal` is an **atomic conjunction**
  (AnalyticCore:8177), not an infinite `Summable ‖factor λ‖²`. So the B-lane
  route's gate is **not** the A-lane generic-λ spectral wall *on its face*.
- A3 supplies concrete, axiom-clean content of the *operator-level* kind.

## What 913 overstated (this correction)

913 implied A3 was "the witness" for the route's `hilbertSchmidtGate`. Wrong:
A3 is the witness for an operator-level predicate the route does not yet use.
The route's gate is a window-support test, filled in the skeleton by the
`…Root` (axiom) machinery; feeding the operator-level trace-class truth in
means **re-defining** the route's `hilbertSchmidtGate` to the operator-level
predicate (and choosing the window/basis), i.e. re-building the seam — exactly
the "re-type" 913's step 1 named as open, not done.

## Honest consequence

913's *negative* (B does not collide with the infinite-λ0 wall) stands. Its
*positive* ("A3 is the concrete gate witness") was a level-confusion: A3
proves the operator truth, the route needs a test-level window truth or a
deliberate operator-level re-definition of the gate. That re-definition —
reify ing the route `hilbertSchmidtGate` = "windowed boundary detector is
self-adjoint ∧ trace-class at the chosen carrier + window" — is exactly the
still-unbuilt, finite, axiom-clean target the 913 roadmap names as step 1.

So, restated precisely: B-lane remaining work = one **definitional + carrier
seam** (route gate := operator-level trace-class gate, at A3's carrier/window),
not the A-lane infrastructure. It remains unwritten; zero claim of closure.

No new axiom. No `sorry`. Only the finite self-attack; prior syntax/`#print
axioms` claims in 912/849/A3 stand on their own.