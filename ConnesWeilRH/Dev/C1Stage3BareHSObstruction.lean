/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1PositiveTraceCutoffGrowth
import ConnesWeilRH.Dev.C1Stage3FrontierCrux
import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex

/-!
# C1 Stage-3 bare Hilbert--Schmidt obstruction

The Stage-3 frontier currently assumes that the whole-line convolution factor
`F_g = cc20GlobalLogConvolution g.involution.test` is Hilbert--Schmidt.  This
file closes that assumption in the only honest direction available here:
for every nonzero compact-log test, the assumption is contradictory.

The proof uses one fixed owner throughout:

```text
bare convolution
  -> finite output restriction/zero-extension
  -> cutoff positive square
  -> exact cutoff trace growth
```

The restriction and zero-extension are contractions, so a bare Hilbert--Schmidt
bound would give a uniform upper bound for every cutoff square.  The existing
cutoff readback gives a strictly growing lower bound, hence contradiction.

No RH statement is made here.  This is a diagnostic/obstruction theorem for
the bare FRONTIER-HS premise; a windowed or renormalized owner remains a
separate analytic problem.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3BareHSObstruction

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedCrossingOperatorBridge
open Dev.C1PositiveTraceCutoffAdapter
open Dev.C1PositiveTraceWindowProducer
open Dev.C1PositiveTraceCutoffGrowth
open C1Stage3FrontierCrux
open Dev.Wall14Plateau
open Filter
open scoped InnerProduct InnerProductSpace Topology BigOperators ENNReal Classical

noncomputable section

variable {nu : Type*}
variable (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)

/-! ## The finite cutoff postcomposition is a contraction -/

theorem norm_cutoffWindowPostcomp_le_one
    (g : CompactLogTest) (n : Nat) :
    ‖(fullBoundaryOutputZeroExtension (cutoffLower g n) (cutoffUpper g n)) ∘L
        globalL2ToKernelInterval (-cutoffUpper g n) (-cutoffLower g n) 0‖ ≤ 1 := by
  let a : ℝ := cutoffLower g n
  let c : ℝ := cutoffUpper g n
  let restriction := globalL2ToKernelInterval (-c) (-a) 0
  let extension := fullBoundaryOutputZeroExtension a c
  have hrestriction : ‖restriction‖ ≤ 1 := by
    rw [← ContinuousLinearMap.adjoint.norm_map]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    rw [norm_globalL2ToKernelInterval_adjoint_apply]
    simp
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖extension (restriction u)‖ ≤ 1 * ‖u‖
  have hextension : ‖extension (restriction u)‖ = ‖restriction u‖ := by
    simpa only [extension, fullBoundaryOutputZeroExtension]
      using norm_kernelIntervalL2ZeroExtension (-c) (-a) 0 (restriction u)
  rw [hextension]
  calc
    ‖restriction u‖ ≤ ‖restriction‖ * ‖u‖ := restriction.le_opNorm u
    _ ≤ 1 * ‖u‖ := by gcongr

/-! ## The cutoff operator has the same owner as a postcomposed bare factor -/

theorem cutoffPositiveBasisData_operator_eq_postcomp
    (g : CompactLogTest) (n : Nat) :
    (cutoffPositiveBasisData g globalBasis n).operator =
      ((fullBoundaryOutputZeroExtension (cutoffLower g n) (cutoffUpper g n)) ∘L
        globalL2ToKernelInterval (-cutoffUpper g n) (-cutoffLower g n) 0) ∘L
        stage3FamilyFactor g := by
  change fullBoundaryPositiveOperator g (cutoffLower g n) (cutoffUpper g n) = _
  unfold fullBoundaryPositiveOperator
  rw [fullBoundaryRootFactor_eq_globalConvolution g
    (cutoffLower g n) (cutoffUpper g n)
    (support_subset_cutoffWindow g n)]
  rfl

/-! ## Bare HS gives a uniform bound for every cutoff energy -/

theorem cutoffEnergy_le_bareHS_mass
    (g : CompactLogTest)
    (hHS : Summable (fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2))
    (n : Nat) :
    ∑' i, ‖(cutoffPositiveBasisData g globalBasis n).operator
        (globalBasis i)‖ ^ 2 ≤
      ∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 := by
  let bounded : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
    fullBoundaryOutputZeroExtension (cutoffLower g n) (cutoffUpper g n) ∘L
      globalL2ToKernelInterval (-cutoffUpper g n) (-cutoffLower g n) 0
  have hbounded : ‖bounded‖ ≤ 1 := by
    simpa only [bounded] using norm_cutoffWindowPostcomp_le_one g n
  have hpost : Summable (fun i =>
      ‖(bounded ∘L stage3FamilyFactor g) (globalBasis i)‖ ^ 2) :=
    summable_normSq_postcomp globalBasis (stage3FamilyFactor g) bounded hHS
  have hle : ∀ i,
      ‖(bounded ∘L stage3FamilyFactor g) (globalBasis i)‖ ^ 2 ≤
        ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 := by
    intro i
    rw [ContinuousLinearMap.comp_apply]
    calc
      ‖bounded (stage3FamilyFactor g (globalBasis i))‖ ^ 2 ≤
          (‖bounded‖ * ‖stage3FamilyFactor g (globalBasis i)‖) ^ 2 := by
        gcongr
        exact bounded.le_opNorm _
      _ ≤ (1 * ‖stage3FamilyFactor g (globalBasis i)‖) ^ 2 := by
        gcongr
      _ = ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 := by ring
  have hsum :
      (∑' i, ‖(bounded ∘L stage3FamilyFactor g) (globalBasis i)‖ ^ 2) ≤
        ∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 :=
    hpost.tsum_le_tsum hle hHS
  rw [cutoffPositiveBasisData_operator_eq_postcomp globalBasis g n]
  exact hsum

/-! ## The bare premise is impossible for every nonzero test -/

theorem not_bare_hilbertSchmidt_of_test_ne_zero
    (g : CompactLogTest)
    (hg : g.test ≠ 0) :
    ¬ Summable (fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) := by
  intro hHS
  let boundValue : ℝ := ∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2
  obtain ⟨n, hn⟩ :=
    cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero
      g globalBasis hg boundValue
  have henergy := cutoffEnergy_le_bareHS_mass globalBasis g hHS n
  have htraceMass :
      (ordinaryTraceAlong globalBasis
        (cutoffPositiveBasisData g globalBasis n).positiveComposition).re =
        ∑' i, ‖(cutoffPositiveBasisData g globalBasis n).operator
          (globalBasis i)‖ ^ 2 := by
    rw [BasisHilbertSchmidtData.ordinaryTrace_positiveComposition]
    norm_cast
  rw [htraceMass] at hn
  exact (not_lt_of_ge henergy) (by simpa [boundValue] using hn)

/-! ## The universal FRONTIER-HS premise is therefore false -/

theorem not_forall_bare_hilbertSchmidt :
    ¬ (∀ g : CompactLogTest,
      Summable (fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2)) := by
  intro hAll
  exact not_bare_hilbertSchmidt_of_test_ne_zero globalBasis
    Dev.Wall14Plateau.bumpPlateauTest Dev.Wall14Plateau.bumpPlateauTest_ne_zero
    (hAll Dev.Wall14Plateau.bumpPlateauTest)

/-! ## The bare FRONTIER-CRUX premise only survives at the zero test -/

/-- **Route-kill for the bare detector.** The per-test Hilbert–Schmidt premise of the concrete bare
FRONTIER-CRUX readback forces the test to be trivial.  This is the contrapositive content of
`not_bare_hilbertSchmidt_of_test_ne_zero`: for a fixed compact-log test, if its whole-line convolution
factor `stage3FamilyFactor g = cc20GlobalLogConvolution g.involution.test` is assumed Hilbert–Schmidt
(summable diagonal norm squares in an orthonormal basis), then the test must vanish identically.

Consequence: step②'s root axiom `C1Stage3FrontierCrux.frontierCrux_powerSpectrum_eq_weilValue` — whose
own premise is exactly this per-test summability — is only ever instantiated on the zero test, where both
the Hilbert–Schmidt mass and `qw g` are `0`.  Every **nontrivial** detector readback therefore has to pass
through a windowed or renormalized owner (the cutoff `C† K C` projection route), not the bare factor. -/
theorem hsPremise_forces_zero_test (g : CompactLogTest)
    (hHS : Summable fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) :
    g.test = 0 := by
  by_contra hgzero
  exact not_bare_hilbertSchmidt_of_test_ne_zero globalBasis g hgzero hHS

end
end C1Stage3BareHSObstruction
end Source
end ConnesWeilRH
