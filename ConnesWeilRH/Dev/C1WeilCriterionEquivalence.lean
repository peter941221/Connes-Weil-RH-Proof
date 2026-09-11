/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1SpectralQwAssembly
import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity

/-!
# C1WeilCriterionEquivalence - B0b: the surviving gate IS the classical Weil criterion

Record 1341 section 5 dissolved the moving-family surface and left exactly one
named obligation, `forall vanishing g, 0 <= C1SameOwnerWeil.qw g`.  Beat B0b
discharges the formal due diligence on that residue with reassembly only - no
new analysis enters anywhere in this file:

```text
part 1 (forward)   SourceRH  ==>  forall g, 0 <= qw g
    W3 split (C1SpectralQwAssembly) + W1 on-line nonnegativity +
    under SourceRH the off-line index set is empty, so the off-line
    residual is a tsum of zeroes.  The vanishing hypothesis is not even
    consumed: the forward leg holds for every test.

part 2 (reverse)   (forall vanishing g, 0 <= qw g)  ==>  SourceRH
    the committed capstone healthy_sourceRH_of_right_healthyDetectorData_
    and_spectral_nonneg, its detector premise discharged by the committed
    right-zero existence, and the sign premise converted through
    qw_eq_spectralWeilValue_centerTwo (assembly pattern of
    C1B5TargetSatisfiability sourceRH_of_all_vanishing_projectionContracts).

part 3 (trivialization)   the operator-family contract adds no strength:
    qw nonnegativity is equivalent to nonemptiness of a positive-trace
    operator limit family, realized by the CONSTANT rank-one family
    (c • id on the one-dimensional carrier, zero remainder).  This is the
    construction half of the 1341 equivalence claim
    (PositiveTraceOperatorLimitFamily <-> scalar 0 <= qw g), the repo
    IsTraceClassAlong being diagonal summability.
-/

namespace ConnesWeilRH
namespace Source
namespace C1WeilCriterionEquivalence

open CC20Concrete.PositiveTrace
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1SpectralWeil
open C1SpectralOnlineSplit
open C1SpectralSummability
open C1CenterTwoCriterionBridge
open C1SpectralQwAssembly
open C1PositiveTraceLimitBridge
open C1HealthyYoshidaSpectralNegativity
open Filter
open scoped InnerProduct InnerProductSpace Topology ComplexConjugate lp

noncomputable section

/-! ### Part 1 (forward): SourceRH kills the off-line block -/

/-- Under `SourceRH` every source zero sits on the critical line: the
conclusion unfolds through the standard bridge to `re = 1 / 2`. -/
theorem sourceZero_re_eq_half_of_sourceRH
    (hRH : RHDefinitionBridge.standard.SourceRH)
    (rho : sourceNontrivialZeroSet) : rho.1.re = 1 / 2 :=
  (RHDefinitionBridge.standard).sourceCriticalLine_to_mathlib rho.1
    (hRH rho.1 rho.2)

/-- `SourceRH` saturates the on-line index set. -/
theorem onLineZeroSet_eq_univ_of_sourceRH
    (hRH : RHDefinitionBridge.standard.SourceRH) :
    (onLineZeroSet : Set sourceNontrivialZeroSet) = Set.univ := by
  ext rho
  simp only [onLineZeroSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact sourceZero_re_eq_half_of_sourceRH hRH rho

/-- `SourceRH` makes the off-line index set empty. -/
theorem offLineZeroSet_eq_empty_of_sourceRH
    (hRH : RHDefinitionBridge.standard.SourceRH) :
    (offLineZeroSet : Set sourceNontrivialZeroSet) = ∅ := by
  rw [offLineZeroSet, onLineZeroSet_eq_univ_of_sourceRH hRH, Set.compl_univ]

/-- The off-line spectral residual vanishes identically under `SourceRH`:
every indicator term is an indicator of the empty set. -/
theorem offLineSpectralMass_eq_zero_of_sourceRH (g : CompactLogTest)
    (hRH : RHDefinitionBridge.standard.SourceRH) :
    offLineSpectralMass g = 0 := by
  have hterm : offLineSpectralTerm g = fun _ => 0 := by
    funext rho
    unfold offLineSpectralTerm
    rw [offLineZeroSet_eq_empty_of_sourceRH hRH]
    simp [Set.indicator]
  unfold offLineSpectralMass
  rw [hterm, tsum_zero]
  simp

/-- **Forward leg.**  `SourceRH` implies nonnegativity of the same-owner Weil
value of every compact-log test - a fortiori of every vanishing test, so the
gate class is vacuously signed under RH. -/
theorem qw_nonneg_of_sourceRH (g : CompactLogTest)
    (hRH : RHDefinitionBridge.standard.SourceRH) :
    0 ≤ C1SameOwnerWeil.qw g := by
  rw [qw_eq_onLineSpectralMass_add_offLineSpectralMass,
    offLineSpectralMass_eq_zero_of_sourceRH g hRH]
  linarith [onLineSpectralMass_nonnegative_of_summable g
    (spectralSummableProp g.convolutionSquare)]

/-! ### Part 2 (reverse): the Weil criterion implies SourceRH -/

/-- **Reverse leg.**  Nonnegativity of `qw` on the healthy triple-vanishing
class is precisely the premise of the committed capstone: the right-oriented
detector existence is already landed
(`exists_healthyDetectorData_of_sourceNontrivialZero_right`), and the sign
premise transfers through `qw_eq_spectralWeilValue_centerTwo`. -/
theorem sourceRH_of_all_vanishing_qw_nonneg
    (hqw : ∀ g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g →
        0 ≤ C1SameOwnerWeil.qw g) :
    RHDefinitionBridge.standard.SourceRH :=
  healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg
    (fun rho hright =>
      exists_healthyDetectorData_of_sourceNontrivialZero_right rho
        (by linarith) hright)
    (fun g hvanishing => by
      rw [← C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo g]
      exact hqw g hvanishing)

/-- **The committed Weil-criterion equivalence.**  The surviving gate of
record 1341 is equivalent to `SourceRH`; both legs are reassembly of landed
blocks.  The equivalence makes the asymmetry explicit: the forward leg needs
no vanishing hypothesis at all, while the reverse leg is exactly where the
classical analytic content is parked. -/
theorem weilCriterion_iff_sourceRH :
    (∀ g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g →
        0 ≤ C1SameOwnerWeil.qw g) ↔ RHDefinitionBridge.standard.SourceRH :=
  ⟨sourceRH_of_all_vanishing_qw_nonneg, fun hRH g _hg =>
    qw_nonneg_of_sourceRH g hRH⟩

/-! ### Part 3: the operator-family contract trivializes to the scalar -/

/-- The one-dimensional carrier `ℓ²(Unit, ℂ)` with its canonical Hilbert
basis.  As a type the carrier is `ℓ²(Unit, ℂ)` (isomorphic to `ℂ`); the
basis has the single vector `lp.single 2 () 1` as its only element. -/
def rankOneCarrierBasis : HilbertBasis Unit ℂ (ℓ²(Unit, ℂ)) :=
  HilbertBasis.ofRepr
    (LinearIsometryEquiv.refl ℂ (ℓ²(Unit, ℂ)))

theorem rankOneCarrierBasis_apply :
    (rankOneCarrierBasis () : ℓ²(Unit, ℂ)) = lp.single 2 () (1 : ℂ) := by
  rw [(HilbertBasis.repr_symm_single rankOneCarrierBasis ()).symm]
  show (LinearIsometryEquiv.refl ℂ (ℓ²(Unit, ℂ))).symm (lp.single 2 () 1)
      = lp.single 2 () 1
  rfl

/-- A nonnegative real scalar makes `r • id` positive on any complex Hilbert
space: symmetric (the scalar is real), with `reApplyInnerSelf = r * re ⟪x, x⟫`. -/
theorem isPositive_real_smul_id {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (r : ℝ) (hr : 0 ≤ r) :
    ((r : ℂ) • ContinuousLinearMap.id ℂ E).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · show ⟪(r : ℂ) • x, y⟫_ℂ = ⟪x, (r : ℂ) • y⟫_ℂ
    rw [inner_smul_left, inner_smul_right]
    simp
  · have hre : ((r : ℂ) • ContinuousLinearMap.id ℂ E).reApplyInnerSelf x
      = r * RCLike.re (⟪x, x⟫_ℂ) := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        inner_smul_left]
      simp
    rw [hre]
    exact mul_nonneg hr inner_self_nonneg

/-- **Trivialization, backward half.**  From scalar nonnegativity build the
constant rank-one positive-trace operator limit family: operator `qw(g) • id`
independent of `n`, zero remainder, constant readback.  This is the witness
that `PositiveTraceOperatorLimitFamily` carries no strength beyond
`0 <= qw g` (record 1341's equivalence claim, construction half). -/
theorem nonempty_positiveTraceOperatorLimitFamily_of_qw_nonneg
    {g : CompactLogTest} (hg : 0 ≤ C1SameOwnerWeil.qw g) :
    Nonempty (PositiveTraceOperatorLimitFamily (ι := Unit)
      (H := ℓ²(Unit, ℂ)) rankOneCarrierBasis g) := by
  set c := (C1SameOwnerWeil.qw g : ℂ) with hcdef
  set T : ℓ²(Unit, ℂ) →L[ℂ] ℓ²(Unit, ℂ) := c • ContinuousLinearMap.id ℂ _
    with hTdef
  have hpos : T.IsPositive := by
    rw [hTdef]
    exact isPositive_real_smul_id _ hg
  have hdiag : ∀ i : Unit,
      ⟪rankOneCarrierBasis i, T (rankOneCarrierBasis i)⟫_ℂ = c := by
    intro i
    cases i
    rw [rankOneCarrierBasis_apply, hTdef, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_smul_right]
    have he : ⟪(lp.single 2 () (1 : ℂ) : ℓ²(Unit, ℂ)),
        (lp.single 2 () (1 : ℂ) : ℓ²(Unit, ℂ))⟫_ℂ = 1 := by
      simp
    rw [he, mul_one]
  have hfun : (fun i : Unit =>
      ⟪rankOneCarrierBasis i, T (rankOneCarrierBasis i)⟫_ℂ) =
      fun _ => c := funext hdiag
  have htrace : (ordinaryTraceAlong rankOneCarrierBasis T).re =
      C1SameOwnerWeil.qw g := by
    unfold ordinaryTraceAlong
    rw [hfun, tsum_fintype (L := SummationFilter.unconditional _)]
    classical
    rw [show (∑ x : Unit, c) = c from by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit]
      simp, hcdef]
    simp
  refine ⟨⟨fun _ => T, fun _n => ?_, fun _n => hpos, fun _ => 0,
    tendsto_const_nhds, ?_⟩⟩
  · rw [IsTraceClassAlong, hfun]
    exact (hasSum_fintype _).summable
  · have hread : (fun (n : ℕ) =>
        (ordinaryTraceAlong rankOneCarrierBasis T).re - (0 : ℝ)) =
        fun _ => C1SameOwnerWeil.qw g := by
      funext n
      rw [htrace, sub_zero]
    rw [hread]
    exact tendsto_const_nhds

/-- **Trivialization, iff.**  Global `qw` nonnegativity is equivalent to
nonemptiness of the positive-trace operator limit family on the one-point
carrier; the forward implication is the landed consumer
`qw_nonnegative_of_positiveTraceOperatorLimitFamily`. -/
theorem qw_nonneg_iff_nonempty_family :
    (∀ g : CompactLogTest, 0 ≤ C1SameOwnerWeil.qw g) ↔
      ∀ g : CompactLogTest,
        Nonempty (PositiveTraceOperatorLimitFamily (ι := Unit)
          (H := ℓ²(Unit, ℂ)) rankOneCarrierBasis g) :=
  ⟨fun h g => nonempty_positiveTraceOperatorLimitFamily_of_qw_nonneg (h g),
   fun h g => Nonempty.elim (h g)
     qw_nonnegative_of_positiveTraceOperatorLimitFamily⟩

/-! ### Axiom-cleanliness audit -/

#print axioms sourceZero_re_eq_half_of_sourceRH
#print axioms onLineZeroSet_eq_univ_of_sourceRH
#print axioms offLineZeroSet_eq_empty_of_sourceRH
#print axioms offLineSpectralMass_eq_zero_of_sourceRH
#print axioms qw_nonneg_of_sourceRH
#print axioms sourceRH_of_all_vanishing_qw_nonneg
#print axioms weilCriterion_iff_sourceRH
#print axioms rankOneCarrierBasis
#print axioms isPositive_real_smul_id
#print axioms nonempty_positiveTraceOperatorLimitFamily_of_qw_nonneg
#print axioms qw_nonneg_iff_nonempty_family

end
end C1WeilCriterionEquivalence
end Source
end ConnesWeilRH
