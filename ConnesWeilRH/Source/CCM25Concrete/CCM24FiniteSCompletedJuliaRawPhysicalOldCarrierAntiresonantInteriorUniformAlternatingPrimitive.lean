/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDouglasFactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorInfiniteHorizonTail

/-!
# Uniform alternating primitives for the antiresonant quotient

Proof 647 gives strong decay of the terminal translated tail.  Strong decay
does not by itself produce a bounded quotient.  This module identifies the
missing quantitative object: the operator norms of the alternating
primitives

```text
C (I - U + U^2 - ... + (-U)^(N-1)).
```

If these primitives are uniformly bounded and the terminal tail tends to
zero, Douglas factorization gives a bounded factor through `I + U` with the
same bound.  Conversely, an existing factor bounds every primitive by twice
the factor norm.  The actual finite-S specialization includes the nonzero
ambient-loss scale and uses the complete coupled target without splitting
its physical branches.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorUniformAlternatingPrimitive

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSDouglasFactor
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorInfiniteHorizonTail
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSCausalMarkov
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Generic alternating-primitive criterion -/

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Complex E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace Complex F] [CompleteSpace F]

/-- Uniform operator-norm control of all finite alternating primitives. -/
def AntiresonantUniformAlternatingPrimitiveBound
    (U : E →L[Complex] E) (C : E →L[Complex] F) (bound : Real) : Prop :=
  0 ≤ bound ∧ ∀ N : Nat,
    ‖C ∘L finiteAntiresonantAlternatingPolynomial U N‖ ≤ bound

/-- A bounded right quotient of `C` by `I + U`. -/
structure AntiresonantAmbientFactorData
    (U : E →L[Complex] E) (C : E →L[Complex] F) (bound : Real) where
  bound_nonneg : 0 ≤ bound
  factor : E →L[Complex] F
  factor_norm_le : ‖factor‖ ≤ bound
  factorization :
    factor ∘L (ContinuousLinearMap.id Complex E + U) = C

/-- The alternating polynomial also telescopes in the left orientation. -/
theorem id_add_comp_finiteAntiresonantAlternatingPolynomial
    (U : E →L[Complex] E) (N : Nat) :
    (ContinuousLinearMap.id Complex E + U) ∘L
        finiteAntiresonantAlternatingPolynomial U N =
      ContinuousLinearMap.id Complex E - (-U) ^ N := by
  change (1 + U) * (∑ k ∈ Finset.range N, (-U) ^ k) =
    1 - (-U) ^ N
  simpa only [sub_neg_eq_add] using mul_neg_geom_sum (-U) N

/-- The completed primitive applied to `I + U` is the target minus its one
terminal orbit term. -/
theorem alternatingPrimitive_comp_id_add
    (U : E →L[Complex] E) (C : E →L[Complex] F) (N : Nat) :
    (C ∘L finiteAntiresonantAlternatingPolynomial U N) ∘L
        (ContinuousLinearMap.id Complex E + U) =
      C - C ∘L (-U) ^ N := by
  calc
    (C ∘L finiteAntiresonantAlternatingPolynomial U N) ∘L
          (ContinuousLinearMap.id Complex E + U) =
        C ∘L (finiteAntiresonantAlternatingPolynomial U N ∘L
          (ContinuousLinearMap.id Complex E + U)) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = C ∘L (ContinuousLinearMap.id Complex E - (-U) ^ N) := by
      rw [finiteAntiresonantAlternatingPolynomial_comp_id_add]
    _ = C - C ∘L (-U) ^ N := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        map_sub]

/-- A contraction keeps the terminal difference `I - (-U)^N` below two. -/
theorem norm_id_sub_neg_pow_le_two
    (U : E →L[Complex] E) (N : Nat) (hU : ‖U‖ ≤ 1) :
    ‖ContinuousLinearMap.id Complex E - (-U) ^ N‖ ≤ 2 := by
  have hneg : ‖-U‖ ≤ (1 : Real) := by
    simpa only [norm_neg] using hU
  have hpow : ‖(-U) ^ N‖ ≤ (1 : Real) := by
    induction N with
    | zero =>
        simpa only [pow_zero] using
          (ContinuousLinearMap.norm_id_le (𝕜 := Complex) (E := E))
    | succ N ih =>
        rw [pow_succ]
        calc
          ‖(-U) ^ N * -U‖ ≤ ‖(-U) ^ N‖ * ‖-U‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ 1 * 1 :=
            mul_le_mul ih hneg (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
  calc
    ‖ContinuousLinearMap.id Complex E - (-U) ^ N‖ ≤
        ‖ContinuousLinearMap.id Complex E‖ + ‖(-U) ^ N‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add ContinuousLinearMap.norm_id_le hpow
    _ = 2 := by norm_num

/-- A bounded quotient makes every alternating primitive uniformly bounded.
The factor two is the norm cost of `I - (-U)^N`. -/
theorem uniformAlternatingPrimitiveBound_of_factorData
    {U : E →L[Complex] E} {C : E →L[Complex] F} {bound : Real}
    (data : AntiresonantAmbientFactorData U C bound)
    (hU : ‖U‖ ≤ 1) :
    AntiresonantUniformAlternatingPrimitiveBound U C (2 * bound) := by
  refine ⟨mul_nonneg (by norm_num) data.bound_nonneg, ?_⟩
  intro N
  have heq :
      C ∘L finiteAntiresonantAlternatingPolynomial U N =
        data.factor ∘L
          (ContinuousLinearMap.id Complex E - (-U) ^ N) := by
    calc
      C ∘L finiteAntiresonantAlternatingPolynomial U N =
          (data.factor ∘L
              (ContinuousLinearMap.id Complex E + U)) ∘L
            finiteAntiresonantAlternatingPolynomial U N := by
        rw [data.factorization]
      _ = data.factor ∘L
            ((ContinuousLinearMap.id Complex E + U) ∘L
              finiteAntiresonantAlternatingPolynomial U N) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = data.factor ∘L
            (ContinuousLinearMap.id Complex E - (-U) ^ N) := by
        rw [id_add_comp_finiteAntiresonantAlternatingPolynomial]
  rw [heq]
  calc
    ‖data.factor ∘L
        (ContinuousLinearMap.id Complex E - (-U) ^ N)‖ ≤
      ‖data.factor‖ *
        ‖ContinuousLinearMap.id Complex E - (-U) ^ N‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ bound * 2 :=
      mul_le_mul data.factor_norm_le
        (norm_id_sub_neg_pow_le_two U N hU)
        (norm_nonneg _) data.bound_nonneg
    _ = 2 * bound := by ring

/-- Uniform primitive control plus terminal decay gives the exact Douglas
same-vector estimate. -/
theorem norm_le_of_uniformAlternatingPrimitiveBound
    {U : E →L[Complex] E} {C : E →L[Complex] F} {bound : Real}
    (hbound : AntiresonantUniformAlternatingPrimitiveBound U C bound)
    (hterminal : ∀ x : E,
      Tendsto (fun N : Nat => C (((-U) ^ N) x)) atTop (nhds 0))
    (x : E) :
    ‖C x‖ ≤ bound *
      ‖(ContinuousLinearMap.id Complex E + U) x‖ := by
  have hlimit : Tendsto
      (fun N : Nat => C x - C (((-U) ^ N) x))
      atTop (nhds (C x)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (hterminal x)
  have hsequence : Tendsto
      (fun N : Nat =>
        (C ∘L finiteAntiresonantAlternatingPolynomial U N)
          ((ContinuousLinearMap.id Complex E + U) x))
      atTop (nhds (C x)) := by
    apply hlimit.congr'
    filter_upwards with N
    have hpoint := DFunLike.congr_fun
      (alternatingPrimitive_comp_id_add U C N) x
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply] using hpoint.symm
  apply le_of_tendsto hsequence.norm
  filter_upwards with N
  calc
    ‖(C ∘L finiteAntiresonantAlternatingPolynomial U N)
        ((ContinuousLinearMap.id Complex E + U) x)‖ ≤
      ‖C ∘L finiteAntiresonantAlternatingPolynomial U N‖ *
        ‖(ContinuousLinearMap.id Complex E + U) x‖ :=
          (C ∘L finiteAntiresonantAlternatingPolynomial U N).le_opNorm _
    _ ≤ bound * ‖(ContinuousLinearMap.id Complex E + U) x‖ :=
      mul_le_mul_of_nonneg_right (hbound.2 N) (norm_nonneg _)

/-- Douglas constructs the quotient selected by a uniform alternating-
primitive bound. -/
noncomputable def factorDataOfUniformAlternatingPrimitiveBound
    {U : E →L[Complex] E} {C : E →L[Complex] F} {bound : Real}
    (hbound : AntiresonantUniformAlternatingPrimitiveBound U C bound)
    (hterminal : ∀ x : E,
      Tendsto (fun N : Nat => C (((-U) ^ N) x)) atTop (nhds 0)) :
    AntiresonantAmbientFactorData U C bound := by
  let witness := exists_factor_of_norm_le C
    (ContinuousLinearMap.id Complex E + U) bound hbound.1
    (norm_le_of_uniformAlternatingPrimitiveBound hbound hterminal)
  let factor := Classical.choose witness
  have factorSpec := Classical.choose_spec witness
  exact
    { bound_nonneg := hbound.1
      factor := factor
      factor_norm_le := factorSpec.1
      factorization := factorSpec.2 }

/-- Under terminal decay, existence of a bounded antiresonant quotient is
equivalent to existence of a uniformly bounded alternating primitive.  The
numerical bounds agree in the forward construction and differ by at most two
in the reverse construction. -/
theorem exists_factorData_iff_exists_uniformAlternatingPrimitiveBound
    (U : E →L[Complex] E) (C : E →L[Complex] F)
    (hU : ‖U‖ ≤ 1)
    (hterminal : ∀ x : E,
      Tendsto (fun N : Nat => C (((-U) ^ N) x)) atTop (nhds 0)) :
    (∃ bound : Real,
        Nonempty (AntiresonantAmbientFactorData U C bound)) ↔
      ∃ bound : Real,
        AntiresonantUniformAlternatingPrimitiveBound U C bound := by
  constructor
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨2 * bound,
      uniformAlternatingPrimitiveBound_of_factorData data hU⟩
  · rintro ⟨bound, hbound⟩
    exact ⟨bound,
      ⟨factorDataOfUniformAlternatingPrimitiveBound hbound hterminal⟩⟩

/-! ## Compact weak escape on the whole ambient carrier -/

/-- A compact operator sends every alternating positive-translation orbit
to zero in norm.  Unlike Proof 647's route-facing theorem, the input here is
an arbitrary ambient vector. -/
theorem compact_output_neg_cc20GlobalLogTranslation_pow_tendsto_zero
    {J : Type*}
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [CompleteSpace J]
    (K : finiteSCarrier →L[Complex] J) (hK : IsCompactOperator K)
    (a : Real) (ha : 0 < a) (u : finiteSCarrier) :
    Tendsto
      (fun N : Nat => K
        (((-(cc20GlobalLogTranslation a).toContinuousLinearMap) ^ N) u))
      atTop (nhds 0) := by
  let U := (cc20GlobalLogTranslation a).toContinuousLinearMap
  have hbounded : Bornology.IsBounded
      (Set.range (fun N : Nat => (U ^ N) u)) := by
    apply Metric.isBounded_range_iff.mpr
    refine ⟨2 * ‖u‖, ?_⟩
    intro M N
    rw [dist_eq_norm]
    calc
      ‖(U ^ M) u - (U ^ N) u‖ ≤
          ‖(U ^ M) u‖ + ‖(U ^ N) u‖ := norm_sub_le _ _
      _ = 2 * ‖u‖ := by
        rw [show ‖(U ^ M) u‖ = ‖u‖ by
          simpa only [U, cc20GlobalLogTranslation_pow_apply] using
            norm_cc20GlobalLogTranslation ((M : Real) * a) u,
          show ‖(U ^ N) u‖ = ‖u‖ by
            simpa only [U, cc20GlobalLogTranslation_pow_apply] using
              norm_cc20GlobalLogTranslation ((N : Real) * a) u]
        ring
  have hweak : ∀ v : finiteSCarrier,
      Tendsto (fun N => inner Complex v ((U ^ N) u))
        atTop (nhds 0) := by
    intro v
    simpa only [U] using
      inner_cc20GlobalLogTranslation_pow_tendsto_zero a ha u v
  have hpositive : Tendsto (fun N => K ((U ^ N) u))
      atTop (nhds 0) :=
    compact_output_tendsto_zero_of_inner_tendsto_zero K hK
      (fun N => (U ^ N) u) hbounded hweak
  rw [NormedAddGroup.tendsto_nhds_zero] at hpositive ⊢
  intro epsilon hepsilon
  filter_upwards [hpositive epsilon hepsilon] with N hN
  simp only [neg_cc20GlobalLogTranslation_pow_apply]
  rw [map_smul, norm_smul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  simpa only [U, cc20GlobalLogTranslation_pow_apply] using hN

/-! ## Actual complete coupled owner -/

/-- The actual complete coupled target has terminal decay on every ambient
input, not only after restriction to the new suffix frame. -/
theorem suffixActualBandCompleteCoupledAmbientTarget_unit_terminal_tendsto_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (u : finiteSCarrier) :
    Tendsto
      (fun N : Nat =>
        suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale p S
          (((-(cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap) ^ N) u))
      atTop (nhds 0) := by
  exact compact_output_neg_cc20GlobalLogTranslation_pow_tendsto_zero
    (suffixActualBandCompleteCoupledAmbientTarget
      owner unitSoninScale p S)
    (suffixActualBandCompleteCoupledAmbientTarget_unit_isCompactOperator
      owner p S)
    (Real.log p) (Real.log_pos (by exact_mod_cast p.property)) u

/-- Uniform bounds for the actual scaled finite-horizon readouts.  This is
the quantitative property absent from Proof 647. -/
def SuffixCompleteCoupledUniformFiniteHorizonReadoutBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (bound : Real) : Prop :=
  0 ≤ bound ∧ ∀ N : Nat,
    ‖suffixActualBandFiniteHorizonCoboundaryReadout
      owner unitSoninScale p S N‖ ≤ bound

/-- A full ambient factor through the actual adjoint loss.  It is stronger
than a factor defined only on the restricted new-frame column. -/
structure SuffixCompleteCoupledAmbientLossFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (bound : Real) where
  bound_nonneg : 0 ≤ bound
  factor : finiteSCarrier →L[Complex]
    sourceSoninCarrier unitSoninScale
  factor_norm_le : ‖factor‖ ≤ bound
  factorization :
    factor ∘L ((primeEulerAmbientLossFactor p)†) =
      suffixActualBandCompleteCoupledAmbientTarget
        owner unitSoninScale p S

/-- A uniform bound on the canonical finite-horizon readouts gives the
ambient same-vector domination with the same constant. -/
theorem norm_completeCoupledAmbientTarget_le_of_uniformFiniteHorizonReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime} {bound : Real}
    (hbound : SuffixCompleteCoupledUniformFiniteHorizonReadoutBound
      owner p S bound)
    (u : finiteSCarrier) :
    ‖suffixActualBandCompleteCoupledAmbientTarget
        owner unitSoninScale p S u‖ ≤
      bound * ‖((primeEulerAmbientLossFactor p)†) u‖ := by
  have htail :=
    suffixActualBandCompleteCoupledAmbientTarget_unit_terminal_tendsto_zero
      owner p S u
  have hlimit : Tendsto
      (fun N : Nat =>
        suffixActualBandCompleteCoupledAmbientTarget
            owner unitSoninScale p S u -
          suffixActualBandCompleteCoupledAmbientTarget
            owner unitSoninScale p S
            (((-(cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap) ^ N) u))
      atTop (nhds (suffixActualBandCompleteCoupledAmbientTarget
        owner unitSoninScale p S u)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub htail
  have hsequence : Tendsto
      (fun N : Nat =>
        suffixActualBandFiniteHorizonCoboundaryReadout
          owner unitSoninScale p S N
          (((primeEulerAmbientLossFactor p)†) u))
      atTop (nhds (suffixActualBandCompleteCoupledAmbientTarget
        owner unitSoninScale p S u)) := by
    apply hlimit.congr'
    filter_upwards with N
    have hpoint := DFunLike.congr_fun
      (suffixActualBandFiniteHorizonCoboundaryReadout_comp_lossAdjoint
        owner unitSoninScale p S N) u
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply] using hpoint.symm
  apply le_of_tendsto hsequence.norm
  filter_upwards with N
  calc
    ‖suffixActualBandFiniteHorizonCoboundaryReadout
        owner unitSoninScale p S N
        (((primeEulerAmbientLossFactor p)†) u)‖ ≤
      ‖suffixActualBandFiniteHorizonCoboundaryReadout
          owner unitSoninScale p S N‖ *
        ‖((primeEulerAmbientLossFactor p)†) u‖ :=
      (suffixActualBandFiniteHorizonCoboundaryReadout
        owner unitSoninScale p S N).le_opNorm _
    _ ≤ bound * ‖((primeEulerAmbientLossFactor p)†) u‖ :=
      mul_le_mul_of_nonneg_right (hbound.2 N) (norm_nonneg _)

/-- Douglas turns a uniform canonical-horizon bound into the actual complete
ambient loss factor without increasing the constant. -/
noncomputable def completeCoupledAmbientLossFactorDataOfUniformReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime} {bound : Real}
    (hbound : SuffixCompleteCoupledUniformFiniteHorizonReadoutBound
      owner p S bound) :
    SuffixCompleteCoupledAmbientLossFactorData owner p S bound := by
  let witness := exists_factor_of_norm_le
    (suffixActualBandCompleteCoupledAmbientTarget
      owner unitSoninScale p S)
    ((primeEulerAmbientLossFactor p)†) bound hbound.1
    (norm_completeCoupledAmbientTarget_le_of_uniformFiniteHorizonReadout
      hbound)
  let factor := Classical.choose witness
  have factorSpec := Classical.choose_spec witness
  exact
    { bound_nonneg := hbound.1
      factor := factor
      factor_norm_le := factorSpec.1
      factorization := factorSpec.2 }

/-- An ambient loss factor bounds every canonical finite-horizon readout by
twice its norm. -/
theorem uniformFiniteHorizonReadoutBound_of_ambientLossFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime} {bound : Real}
    (data : SuffixCompleteCoupledAmbientLossFactorData owner p S bound) :
    SuffixCompleteCoupledUniformFiniteHorizonReadoutBound
      owner p S (2 * bound) := by
  let scale : Real := primeEulerAmbientLossScale p
  let U := (cc20GlobalLogTranslation
    (Real.log p)).toContinuousLinearMap
  let C := suffixActualBandCompleteCoupledAmbientTarget
    owner unitSoninScale p S
  let unscaledFactor : finiteSCarrier →L[Complex]
      sourceSoninCarrier unitSoninScale :=
    (scale : Complex) • data.factor
  have hscale : 0 < scale := primeEulerAmbientLossScale_pos p
  have hfactorization :
      unscaledFactor ∘L
          (ContinuousLinearMap.id Complex finiteSCarrier + U) = C := by
    apply ContinuousLinearMap.ext
    intro u
    have hdata := DFunLike.congr_fun data.factorization u
    have hloss := DFunLike.congr_fun
      (primeEulerAmbientLossFactor_adjoint_eq_positiveTranslation p) u
    simp only [unscaledFactor, U, C, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply] at hdata hloss ⊢
    rw [hloss] at hdata
    simpa only [map_smul] using hdata
  have hunscaledNorm : ‖unscaledFactor‖ ≤ scale * bound := by
    simp only [unscaledFactor, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hscale]
    exact mul_le_mul_of_nonneg_left data.factor_norm_le hscale.le
  let genericData : AntiresonantAmbientFactorData U C (scale * bound) :=
    { bound_nonneg := mul_nonneg hscale.le data.bound_nonneg
      factor := unscaledFactor
      factor_norm_le := hunscaledNorm
      factorization := hfactorization }
  have hU : ‖U‖ ≤ 1 := by
    exact (cc20GlobalLogTranslation
      (Real.log p)).norm_toContinuousLinearMap_le
  have hgeneric :=
    uniformAlternatingPrimitiveBound_of_factorData genericData hU
  refine ⟨mul_nonneg (by norm_num) data.bound_nonneg, ?_⟩
  intro N
  unfold suffixActualBandFiniteHorizonCoboundaryReadout
  unfold finiteHorizonAntiresonantCoboundaryReadout
  change ‖((scale : Complex)⁻¹) •
      (C ∘L finiteAntiresonantAlternatingPolynomial U N)‖ ≤
    2 * bound
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hscale]
  calc
    scale⁻¹ *
        ‖C ∘L finiteAntiresonantAlternatingPolynomial U N‖ ≤
      scale⁻¹ * (2 * (scale * bound)) :=
        mul_le_mul_of_nonneg_left (hgeneric.2 N) (inv_nonneg.mpr hscale.le)
    _ = 2 * ((scale⁻¹ * scale) * bound) := by ring
    _ = 2 * bound := by
      rw [inv_mul_cancel₀ (ne_of_gt hscale), one_mul]

/-- At unit scale, existence of a full ambient antiresonant quotient is
equivalent to uniform boundedness of the canonical finite-horizon readouts.
The two constructions change the numerical bound by at most a factor two. -/
theorem exists_ambientLossFactorData_iff_exists_uniformFiniteHorizonReadoutBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    (∃ bound : Real,
        Nonempty (SuffixCompleteCoupledAmbientLossFactorData
          owner p S bound)) ↔
      ∃ bound : Real,
        SuffixCompleteCoupledUniformFiniteHorizonReadoutBound
          owner p S bound := by
  constructor
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨2 * bound,
      uniformFiniteHorizonReadoutBound_of_ambientLossFactorData data⟩
  · rintro ⟨bound, hbound⟩
    exact ⟨bound,
      ⟨completeCoupledAmbientLossFactorDataOfUniformReadout hbound⟩⟩

/-- The uniform canonical-horizon condition already gives the restricted
raw Bone 1 readout with the same norm bound. -/
theorem exists_rawColumnReadout_of_uniformFiniteHorizonReadoutBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime} {bound : Real}
    (hbound : SuffixCompleteCoupledUniformFiniteHorizonReadoutBound
      owner p S bound) :
    ∃ readout : finiteSCarrier →L[Complex]
        sourceSoninCarrier unitSoninScale,
      ‖readout‖ ≤ bound ∧
        readout ∘L newFrameAntiresonantColumn unitSoninScale p S =
          signedCompressedInteriorOwner owner unitSoninScale p S := by
  let data := completeCoupledAmbientLossFactorDataOfUniformReadout hbound
  refine ⟨data.factor, data.factor_norm_le, ?_⟩
  calc
    data.factor ∘L newFrameAntiresonantColumn unitSoninScale p S =
        (data.factor ∘L ((primeEulerAmbientLossFactor p)†)) ∘L
          newSuffixFrame unitSoninScale S := by
      rfl
    _ = suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale p S ∘L
        newSuffixFrame unitSoninScale S := by
      rw [data.factorization]
    _ = signedCompressedInteriorOwner owner unitSoninScale p S :=
      suffixActualBandCompleteCoupledAmbientTarget_comp_newFrame
        owner unitSoninScale p S

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorUniformAlternatingPrimitive
end CCM25Concrete
end Source
end ConnesWeilRH
