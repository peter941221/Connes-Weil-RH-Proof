import ConnesWeilRH.Dev.ConcreteP1SupportProbe
import ConnesWeilRH.Dev.L657DiagProbe
import ConnesWeilRH.Dev.R1Step4Probe982
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmeticBridge

/-!
# R1 step 5 — on-visible arithmetic normalization re-type seam (983)

`FixedLambdaFinitePrimeArithmeticCertificate.atomsWithSourceTest` demands a
`∀ n : ℕ` normalization (`SourceFinitePrimeArithmeticNormalizationForSourceTest`)
whose leaf requires `IsPrimePow n` at every `n` — the 653 wall (uninhabitable
at composites).

This probe builds the on-visible restriction of that arithmetic: a
`SourceVisibleFinitePrimeArithmeticData` whose `atVisibleIndex` is keyed by
`sourceTest.sourceAtomVisible n`, supplied directly by the reduce-lane object
`gd_reduce` (probe 982).  This is the infinite-to-finite re-type seam for the
`∀n` field: instead of a bare `∀n` normalization, the arithmetic is carried by
the concrete evaluate data at exactly the visible (finite) indices.

The membership guard `visible → n ∈ W0.globalPrimeIndexSet` uses only the
concrete carrier's exact support: on the additive `convolutionStar = +`, the
square `(f0 + f0)` is visible at `n` iff the bare bump `f0` is visible at `n`,
and `ConcreteP1SupportProbe.forward_mem` pins that to `n = 2`.

No `∀ n : ℕ` normalization is built anywhere in this probe.  RH NOT claimed.
Zero `sorry`.  No new `axiom`.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace R1Step5Probe983

open L657DiagProbe
open ConnesWeilRH.Source.Dev.R1StepTransformProbe982
open ConnesWeilRH.Source.CCM25Concrete
open ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest
open ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic
open ConnesWeilRH.Source.CCM25Concrete.PrimePowerTest
open ConnesWeilRH.Source.AnalyticCore
open ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer

/-- On the additive carrier `(f0 + f0) x = 2 • f0 x`, so the evaluation value
at the square is twice the bare value. -/
lemma valueAt_square_two (x : ℝ) :
    E0.valueAt (f0 + f0) x = 2 * E0.valueAt f0 x := by
  rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm,
      AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
  change ‖(f0 + f0) x‖ = 2 * ‖f0 x‖
  have h : (f0 + f0) x = (2 : ℂ) • f0 x := by
    change f0 x + f0 x = (2 : ℂ) • f0 x
    rw [smul_eq_mul]
    ring
  rw [h]
  rw [norm_smul]
  norm_num

/-- The square finite-prime term is twice the bare term (identical support). -/
lemma sourceFinitePrimeTerm_square_eq_two (n : ℕ) :
    E0.sourceFinitePrimeTerm n (f0 + f0) =
      2 * E0.sourceFinitePrimeTerm n f0 := by
  rw [AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt,
      AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt]
  rw [valueAt_square_two, valueAt_square_two]
  ring

/-- Square nonzero ↔ bare nonzero: the additive carrier lets the square and
the bump see the same support at every `n`. -/
lemma sourceFinitePrimeTerm_square_ne_zero_iff (n : ℕ) :
    E0.sourceFinitePrimeTerm n (f0 + f0) ≠ 0 ↔
      E0.sourceFinitePrimeTerm n f0 ≠ 0 := by
  constructor
  · intro h2 hz
    exact h2 (by rw [sourceFinitePrimeTerm_square_eq_two];
                 rw [hz, mul_zero])
  · intro hb hsq
    rw [sourceFinitePrimeTerm_square_eq_two] at hsq
    exact hb ((mul_eq_zero.mp hsq).resolve_left (by norm_num))

/-- Visible at the square of `W0` iff visible at the bare bump (additive). -/
lemma visible_square_iff_bare (n : ℕ) :
    W0.finitePrimeAtomVisible n (W0.convolutionStar f0 f0) ↔
      W0.finitePrimeAtomVisible n f0 := by
  unfold W0
  change E0.sourceFinitePrimeTerm n (f0 + f0) ≠ 0 ↔
    E0.sourceFinitePrimeTerm n f0 ≠ 0
  exact sourceFinitePrimeTerm_square_ne_zero_iff n

/-- The concrete source-test interface of the square. -/
noncomputable def sourceIface :
    PrimePowerTest.SourceTestEvaluationInterface W0 f0 f0 :=
  common0.toSourceTestEvaluationInterface

/-- Visible → membership: visible at the square → visible at the bare bump →
`forward_mem` pins `n = 2` → `2 ∈ globalPrimeIndexSet`. -/
lemma visible_mem (n : ℕ) (hn : sourceIface.sourceAtomVisible n) :
    n ∈ W0.globalPrimeIndexSet := by
  have hvis_sq : W0.finitePrimeAtomVisible n (W0.convolutionStar f0 f0) := by
    simpa [sourceIface, PrimePowerTest.SourceTestEvaluationInterface.sourceAtomVisible] using hn
  have hvis_ff : W0.finitePrimeAtomVisible n f0 :=
    (visible_square_iff_bare n).1 hvis_sq
  have hn2 : n = 2 := by
    have hterm : ConcreteP1SupportProbe.concreteEval.sourceFinitePrimeTerm n f0 ≠ 0 := by
      unfold W0 at hvis_ff
      exact hvis_ff
    exact ConcreteP1SupportProbe.forward_mem n hterm
  rw [hn2]
  simpa [globalSetTwo]

/-- On-visible arithmetic, keyed by the source-visible predicate.  A
hypothetical `∀n` normalization that agrees with the reduce-lane `gd_reduce` on
the visible indices is re-housed here over the FINITE support. -/
noncomputable def visibleFromReduce :
    SourceVisibleFinitePrimeArithmeticData W0 f0 f0 sourceIface where
  atVisibleIndex := fun n hn =>
    gd.atIndex n (visible_mem n hn)

/-- The on-visible arithmetic at the visible prime `2` agrees with the direct
on-`{2}` object: visible indices are exactly `{2}`. -/
lemma visibleFromReduce_at_two (h : sourceIface.sourceAtomVisible 2) :
    (visibleFromReduce.atVisibleIndex 2 h) =
      gd.atIndex 2 (by simpa [globalSetTwo]) := by
  rfl

#print axioms valueAt_square_two
#print axioms sourceFinitePrimeTerm_square_eq_two
#print axioms sourceFinitePrimeTerm_square_ne_zero_iff
#print axioms visible_square_iff_bare
#print axioms visible_mem
#print axioms visibleFromReduce
#print axioms visibleFromReduce_at_two

end R1Step5Probe983
end Dev
end Source
end ConnesWeilRH