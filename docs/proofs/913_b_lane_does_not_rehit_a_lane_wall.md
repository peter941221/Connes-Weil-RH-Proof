# 913 — Convergence crux: the B-lane `fullWeilPositivity` gate is NOT the A-lane generic-λ `hfactor` wall

Status: structural verdict (source-governed), no new probe. No RH claimed.

## Question this answers

After 911 closed the A-lane to one wall (generic-λ `hfactor`) and 912 reduced
the B-lane to the single `fullWeilPositivity` slot, the open question was:

> Does the B-lane exit (a constructive `FullWeilPositivity` at a concrete `g`)
> silently collapse back onto the A-lane's generic-λ `hfactor` Summable wall —
> i.e. are the two "different" lanes really one wall in two disguises?

## Verdict

**No.** By construction the operative B-lane gate — `hilbertSchmidtGate` — is
`traceClass ∧ cyclicLegal`, a finite conjunction of two Props on the archimedean
test, and there is a concrete axiom-clean witness (A3) satisfying both. It does
not quantify over a generic scale λ, so it cannot be the infinite spectral
`Summable ‖sourceProlateHilbertSchmidtFactor λ‖²` wall. The B-lane's true
remaining door is the finite canonical-Weil sign decision (842/847/847b), and
(optionally) the seam that re-types the A3 compact carrier onto the route's
specific archimedean `Test`.

## Evidence 1 — the gate is an atomic conjunction, not a summability

```lean
-- Source/AnalyticCore.lean:8177-8186
def hilbertSchmidtGate
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    A.Test → Prop :=
  fun g => T.traceClass g ∧ T.cyclicLegal g
```

`traceClass` and `cyclicLegal` are Props on the single test `A.Test`. There is
no `λ : ℝ`, no `Summable`, no operator-norm `≤ 1`, no prolate family. The field
the route actually consumes is a total version of this:

```
-- Source/Objects.lean (inside CC20TraceObjectPackage)
sourceHilbertSchmidtGate : ∀ g : archimedeanSymbols.Test,
    archimedeanSymbols.hilbertSchmidtGate g
```

So "the gate" everywhere the route/Carrier touches it is "this test, taken
over all tests, satisfies traceClass ∧ cyclicLegal". It is orthogonal in kind
to "this scale λ has a Summable squares factor."

## Evidence 2 — a concrete witness satisfies both conjuncts (A3, axiom-clean)

`Dev/A3NonZeroCompactLogGateProbe.lean` builds a nonzero `CompactLogTest` and
proves, from mathlib axioms only:

| claim | conjunct covered | axiom status |
| `hsGate_selfAdjoint_witness` | self-adjoint (detector side) | clean |
| `hsGate_traceClass_witness` | `traceClass` (HS-trace-class-along-a-Hilbert-basis) | clean |
| `detector_isPositive` / `detector_re_inner_nonneg` | positive sign content | clean |

These hold on the concrete carrier `cc20GlobalLogCrossingL2`, whose built-in
`exists_hilbertBasis` closes the witness (global nonempty, `nonempty`). That is
precisely the shape of an `hilbertSchmidtGate` satisfier.

## Evidence 3 — the route's skeleton feeds this field from axioms, not from λ-analysis

`UnconditionalSkeleton.lean` builds its route data from
`sourceObjectPackageOfNormalizedCC20Trace`, where `sourceHilbertSchmidtGate` is
filled by the module's `...Root` axioms (Objects `sourceHilbertSchmidtGate` is
a field; the skeleton supplies it from `normalizedBridgesFromTheorems` +
`normalizedBaseFromTheorems`, an axiom-named base). It is *not* transported
from any unit-→ generic-λ scaling bridge. This is consistent with the 845
negative: there is no conjugation/transport from unit-λ.

## Where the two lanes genuinely diverge

| | PRIMARY blocker | character |
| -- | -- | -- |
| **A-lane** | `SourceProlateHilbertSchmidtFactor λ` Summable at generic λ | infinite, spectral, prolate-eigenbasis |
| **B-lane** | canonical-Weil ≤ 0 sign (finite per-value decomp.) | finite, sign-only, made positive |

A-lane is a series-convergence wall; B-lane is a finite sign wall. Only if one
feeds the *refuted* finite-vanishing carrier (`CC20FiniteVanishingWeilCriterion`
with its universal `≤ 0`) does B's slot become unsatisfiable — but 847b/848
show that is a choice of input, not a per-type impossibility:
`Exhaustion.FullWeilPositivity` is constructive (`Sort 1`) and not refuted.

## The real remaining steps for B (each finite, none the λ-earth)

1. (optional) re-type the A3 compact carrier onto the particular
   `archimedeanSymbols.Test` the route uses — a finite morphism like 536's
   `AmbientPrimeVisibleProbe` did for the rational/general rows, axiom-clean.
   This is the only part not yet built end-to-end onto a single concrete `g`.
2. decide the single positive canonical sign — supply/pick the constructive
   `FullWeilPositivity` (Exhaustion) as the `fullWeilPositivity` that feeds
   `FixedSPositiveTraceReadOff`; this is decision 842/847b, still the one.

No RH claimed. Zero `sorry`. Only library axioms (relies on the already-
`[propext, Classical.choice, Quot.sound]`-audited rows 849/912/A3); no new
axiom introduced in writing this verdict.