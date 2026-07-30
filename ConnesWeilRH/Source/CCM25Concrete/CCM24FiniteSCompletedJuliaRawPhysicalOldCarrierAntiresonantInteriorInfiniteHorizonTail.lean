/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFixedStepCompactness
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Infinite-horizon decay of the coupled terminal tail

The finite alternating readout from Proof 646 leaves one translated terminal
tail.  On the genuine whole-line `L2` carrier, positive translations tend
weakly to zero.  At unit Sonin scale the complete coupled ambient target is
compact, so it turns that weak decay into norm decay on every fixed source
vector.

Thus the explicit finite-horizon readouts converge strongly to the complete
signed interior owner.  This is qualitative pointwise convergence, not an
operator-norm estimate: the alternating readout bound still grows linearly in
the horizon, and no route-uniform Bone 1 factor follows.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorInfiniteHorizonTail

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactApproximateKernel
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFixedStepCompactness
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSwappedLocalPairRadialColumnBridge
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSCausalMarkov
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Whole-line translation powers -/

/-- Powers of one logarithmic translation are literal translations by the
summed displacement. -/
theorem cc20GlobalLogTranslation_pow_apply
    (b : Real) (N : Nat) (u : finiteSCarrier) :
    ((cc20GlobalLogTranslation b).toContinuousLinearMap ^ N) u =
      cc20GlobalLogTranslation ((N : Real) * b) u := by
  induction N with
  | zero =>
      simp only [pow_zero, ContinuousLinearMap.one_apply, Nat.cast_zero,
        zero_mul]
      exact (cc20GlobalLogTranslation_zero_apply u).symm
  | succ N ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih]
      change cc20GlobalLogTranslation b
          (cc20GlobalLogTranslation ((N : Real) * b) u) = _
      rw [cc20GlobalLogTranslation_add_apply]
      congr 1
      push_cast
      ring_nf

/-- The alternating powers differ from the positive translation orbit only
by a scalar of norm one. -/
theorem neg_cc20GlobalLogTranslation_pow_apply
    (b : Real) (N : Nat) (u : finiteSCarrier) :
    ((-(cc20GlobalLogTranslation b).toContinuousLinearMap) ^ N) u =
      ((-1 : Complex) ^ N) •
        cc20GlobalLogTranslation ((N : Real) * b) u := by
  induction N with
  | zero =>
      simp only [pow_zero, ContinuousLinearMap.one_apply, one_smul,
        Nat.cast_zero, zero_mul]
      exact (cc20GlobalLogTranslation_zero_apply u).symm
  | succ N ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih]
      simp only [ContinuousLinearMap.neg_apply, map_smul,
        pow_succ']
      rw [smul_neg, ← neg_smul]
      change (-((-1 : Complex) ^ N)) •
          cc20GlobalLogTranslation b
            (cc20GlobalLogTranslation ((N : Real) * b) u) = _
      rw [cc20GlobalLogTranslation_add_apply]
      congr 1
      · ring_nf
      · push_cast
        ring

/-! ## Weak escape of actual real-line translations -/

/-- Every whole-line `L2` vector admits an arbitrarily close continuous,
compactly supported representative. -/
private theorem exists_compactSupport_L2_approx
    (u : finiteSCarrier) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ f : Real → Complex,
      HasCompactSupport f ∧ Continuous f ∧
      ∃ hf : MemLp f 2 volume, ‖u - hf.toLp f‖ ≤ epsilon := by
  have hepsilonENN : ENNReal.ofReal epsilon ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr hepsilon
  obtain ⟨f, hfcompact, hferror, hfcontinuous, hfmem⟩ :=
    (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le
      (p := (2 : ENNReal)) ENNReal.ofNat_ne_top hepsilonENN
  refine ⟨f, hfcompact, hfcontinuous, hfmem, ?_⟩
  rw [← Lp.toLp_coeFn u (Lp.memLp u), ← dist_eq_norm,
    Lp.dist_edist, Lp.edist_toLp_toLp]
  exact ENNReal.toReal_le_of_le_ofReal (le_of_lt hepsilon) hferror

/-- Two compactly supported `L2` representatives have zero translated inner
product once their supports are separated. -/
private theorem eventually_inner_compactSupport_translation_eq_zero
    {f g : Real → Complex}
    (hfcompact : HasCompactSupport f) (hgcompact : HasCompactSupport g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (a : Real) (ha : 0 < a) :
    ∀ᶠ N : Nat in atTop,
      inner Complex (hg.toLp g)
        (cc20GlobalLogTranslation ((N : Real) * a) (hf.toLp f)) = 0 := by
  obtain ⟨Rf, hRf⟩ := hfcompact.isBounded.exists_norm_le
  obtain ⟨Rg, hRg⟩ := hgcompact.isBounded.exists_norm_le
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((Rf + Rg) / a)
  rw [eventually_atTop]
  refine ⟨N0, ?_⟩
  intro N hN
  have hlarge : Rf + Rg < (N : Real) * a := by
    apply (div_lt_iff₀ ha).mp
    exact hN0.trans_le (by exact_mod_cast hN)
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  have hfshift :=
    (measurePreserving_add_right volume ((N : Real) * a)).quasiMeasurePreserving.ae_eq
      hf.coeFn_toLp
  filter_upwards [hg.coeFn_toLp,
      cc20GlobalLogTranslation_coeFn ((N : Real) * a) (hf.toLp f),
      hfshift] with t hgat htranslation hfat
  have hfat' : (hf.toLp f : Real → Complex) (t + (N : Real) * a) =
      f (t + (N : Real) * a) := by
    simpa only [Function.comp_apply] using hfat
  rw [hgat, htranslation, hfat']
  by_cases hgzero : g t = 0
  · simp only [hgzero, inner_zero_left, Pi.zero_apply]
  by_cases hfzero : f (t + (N : Real) * a) = 0
  · simp only [hfzero, inner_zero_right, Pi.zero_apply]
  exfalso
  have hgtSupport : t ∈ tsupport g :=
    subset_tsupport g (by simpa only [Function.mem_support] using hgzero)
  have hftSupport : t + (N : Real) * a ∈ tsupport f :=
    subset_tsupport f (by simpa only [Function.mem_support] using hfzero)
  have hgt := hRg t hgtSupport
  have hft := hRf (t + (N : Real) * a) hftSupport
  rw [Real.norm_eq_abs] at hgt hft
  have hgtLower := (abs_le.mp hgt).1
  have hftUpper := (abs_le.mp hft).2
  linarith

/-- Matrix coefficients of the actual positive whole-line translations tend
to zero along every positive arithmetic displacement. -/
theorem inner_cc20GlobalLogTranslation_nat_mul_tendsto_zero
    (a : Real) (ha : 0 < a) (u v : finiteSCarrier) :
    Tendsto
      (fun N : Nat => inner Complex v
        (cc20GlobalLogTranslation ((N : Real) * a) u))
      atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro epsilon hepsilon
  let epsilon' := min epsilon 1
  let scale := ‖u‖ + ‖v‖ + 1
  let delta := epsilon' / (4 * scale)
  have hepsilon' : 0 < epsilon' := by
    exact lt_min hepsilon zero_lt_one
  have hscale : 0 < scale := by
    dsimp only [scale]
    positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hdeltaOne : delta ≤ 1 := by
    dsimp only [delta, epsilon', scale]
    have hepsilonOne : min epsilon 1 ≤ 1 := min_le_right _ _
    have hdenom : 1 ≤ 4 * (‖u‖ + ‖v‖ + 1) := by
      nlinarith [norm_nonneg u, norm_nonneg v]
    exact (div_le_one (by positivity)).2 (hepsilonOne.trans hdenom)
  obtain ⟨f, hfcompact, _hfcontinuous, hf, huf⟩ :=
    exists_compactSupport_L2_approx u hdelta
  obtain ⟨g, hgcompact, _hgcontinuous, hg, hvg⟩ :=
    exists_compactSupport_L2_approx v hdelta
  have hcompactZero := eventually_inner_compactSupport_translation_eq_zero
    hfcompact hgcompact hf hg a ha
  filter_upwards [hcompactZero] with N hzero
  let Uu := cc20GlobalLogTranslation ((N : Real) * a) u
  let Uf := cc20GlobalLogTranslation ((N : Real) * a) (hf.toLp f)
  have hUdiff : ‖Uu - Uf‖ ≤ delta := by
    calc
      ‖Uu - Uf‖ = ‖cc20GlobalLogTranslation ((N : Real) * a)
          (u - hf.toLp f)‖ := by
        congr 1
        exact map_sub _ _ _ |>.symm
      _ = ‖u - hf.toLp f‖ := norm_cc20GlobalLogTranslation _ _
      _ ≤ delta := huf
  have hgNorm : ‖hg.toLp g‖ ≤ ‖v‖ + 1 := by
    calc
      ‖hg.toLp g‖ ≤ ‖v‖ + ‖v - hg.toLp g‖ :=
        norm_le_norm_add_norm_sub _ _
      _ ≤ ‖v‖ + delta := by linarith
      _ ≤ ‖v‖ + 1 := by linarith
  have hfirst : ‖inner Complex (v - hg.toLp g) Uu‖ ≤ delta * ‖u‖ := by
    calc
      _ ≤ ‖v - hg.toLp g‖ * ‖Uu‖ := norm_inner_le_norm _ _
      _ ≤ delta * ‖Uu‖ :=
        mul_le_mul_of_nonneg_right hvg (norm_nonneg Uu)
      _ = delta * ‖u‖ := by
        rw [show ‖Uu‖ = ‖u‖ by
          exact norm_cc20GlobalLogTranslation _ _]
  have hsecond : ‖inner Complex (hg.toLp g) (Uu - Uf)‖ ≤
      (‖v‖ + 1) * delta := by
    calc
      _ ≤ ‖hg.toLp g‖ * ‖Uu - Uf‖ := norm_inner_le_norm _ _
      _ ≤ (‖v‖ + 1) * delta :=
        mul_le_mul hgNorm hUdiff (norm_nonneg _) (by positivity)
  have hdecompose :
      inner Complex v Uu =
        inner Complex (v - hg.toLp g) Uu +
          inner Complex (hg.toLp g) (Uu - Uf) := by
    have hzero' : inner Complex (hg.toLp g) Uf = 0 := by
      simpa only [Uf] using hzero
    rw [inner_sub_left, inner_sub_right, hzero', sub_zero]
    ring
  rw [hdecompose]
  calc
    ‖inner Complex (v - hg.toLp g) Uu +
        inner Complex (hg.toLp g) (Uu - Uf)‖ ≤
      ‖inner Complex (v - hg.toLp g) Uu‖ +
        ‖inner Complex (hg.toLp g) (Uu - Uf)‖ := norm_add_le _ _
    _ ≤ delta * ‖u‖ + (‖v‖ + 1) * delta :=
      add_le_add hfirst hsecond
    _ = epsilon' / 4 := by
      dsimp only [delta, scale]
      field_simp [ne_of_gt hscale]
      ring
    _ < epsilon := by
      have hepsilon'Le : epsilon' ≤ epsilon := min_le_left _ _
      nlinarith

/-- The same weak escape holds for powers of the positive translation
operator. -/
theorem inner_cc20GlobalLogTranslation_pow_tendsto_zero
    (a : Real) (ha : 0 < a) (u v : finiteSCarrier) :
    Tendsto
      (fun N : Nat => inner Complex v
        (((cc20GlobalLogTranslation a).toContinuousLinearMap ^ N) u))
      atTop (nhds 0) := by
  simpa only [cc20GlobalLogTranslation_pow_apply] using
    inner_cc20GlobalLogTranslation_nat_mul_tendsto_zero a ha u v

/-! ## Compact operators convert weak escape to norm escape -/

/-- A compact Hilbert-space operator sends every bounded sequence whose
matrix coefficients vanish to zero in norm. -/
theorem compact_output_tendsto_zero_of_inner_tendsto_zero
    {H J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [CompleteSpace H]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [CompleteSpace J]
    (K : H →L[Complex] J) (hK : IsCompactOperator K)
    (x : Nat → H) (hbounded : Bornology.IsBounded (Set.range x))
    (hweak : ∀ v : H,
      Tendsto (fun N => inner Complex v (x N)) atTop (nhds 0)) :
    Tendsto (fun N => K (x N)) atTop (nhds 0) := by
  obtain ⟨C, hCcompact, hKC⟩ :=
    hK.image_subset_compact_of_bounded hbounded
  apply hCcompact.tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards with N
    exact hKC ⟨x N, ⟨N, rfl⟩, rfl⟩
  · intro y _ hy
    obtain ⟨phi, hphiMono, hphi⟩ := hy.tendsto_subseq
    apply (inner_self_eq_zero (𝕜 := Complex) (x := y)).mp
    have htest := (hweak (K.adjoint y)).comp hphiMono.tendsto_atTop
    have htoZero :
        Tendsto (fun N => inner Complex y (K (x (phi N))))
          atTop (nhds 0) := by
      simpa only [ContinuousLinearMap.adjoint_inner_left] using htest
    have htoLimit :
        Tendsto (fun N => inner Complex y (K (x (phi N))))
          atTop (nhds (inner Complex y y)) := by
      simpa only [Function.comp_apply] using
        (tendsto_const_nhds.inner hphi)
    exact tendsto_nhds_unique htoLimit htoZero

/-! ## Actual unit-scale coupled tail -/

/-- At the route's unit Sonin scale, the complete ambient target is compact.
The physical cofactor remains coupled throughout. -/
theorem suffixActualBandCompleteCoupledAmbientTarget_unit_isCompactOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    IsCompactOperator
      (suffixActualBandCompleteCoupledAmbientTarget
        owner unitSoninScale p S) := by
  have hcofactor : IsCompactOperator
      (suffixActualBandCompleteSwappedLocalCofactor
        owner unitSoninScale p S) := by
    rw [suffixActualBandCompleteSwappedLocalCofactor_eq_neg_scalar_smul_completeBoundaryDefect]
    exact ((suffixActualBandCompleteBoundaryReverseIntertwiningDefect_unit_isCompactOperator
      owner p S).smul (primeSchurMarkovScalar p : Complex)).neg
  unfold suffixActualBandCompleteCoupledAmbientTarget
  have hright := hcofactor.comp_clm ((newSuffixFrame unitSoninScale S)†)
  have hleft := hright.clm_comp
    ((suffixEulerFrameTransition unitSoninScale p S)†)
  exact hleft.smul (-((primeSchurMarkovScalar p : Complex)⁻¹))

/-- The actual alternating terminal tail tends to zero in norm on every fixed
source vector.  This is strong, not operator-norm, convergence. -/
theorem suffixActualBandFiniteHorizonCoupledTail_unit_apply_tendsto_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier unitSoninScale) :
    Tendsto
      (fun N => suffixActualBandFiniteHorizonCoupledTail
        owner unitSoninScale p S N x)
      atTop (nhds 0) := by
  let U := (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
  let frameValue := newSuffixFrame unitSoninScale S x
  let target := suffixActualBandCompleteCoupledAmbientTarget
    owner unitSoninScale p S
  have hpLog : 0 < Real.log (p : Real) := by
    exact Real.log_pos (by exact_mod_cast p.property)
  have hbounded : Bornology.IsBounded
      (Set.range (fun N : Nat => (U ^ N) frameValue)) := by
    apply Metric.isBounded_range_iff.mpr
    refine ⟨2 * ‖frameValue‖, ?_⟩
    intro M N
    rw [dist_eq_norm]
    calc
      ‖(U ^ M) frameValue - (U ^ N) frameValue‖ ≤
          ‖(U ^ M) frameValue‖ + ‖(U ^ N) frameValue‖ := norm_sub_le _ _
      _ = 2 * ‖frameValue‖ := by
        rw [show ‖(U ^ M) frameValue‖ = ‖frameValue‖ by
          simpa only [U, cc20GlobalLogTranslation_pow_apply] using
            norm_cc20GlobalLogTranslation ((M : Real) * Real.log p) frameValue,
          show ‖(U ^ N) frameValue‖ = ‖frameValue‖ by
            simpa only [U, cc20GlobalLogTranslation_pow_apply] using
              norm_cc20GlobalLogTranslation ((N : Real) * Real.log p) frameValue]
        ring
  have hweak : ∀ v : finiteSCarrier,
      Tendsto (fun N => inner Complex v ((U ^ N) frameValue))
        atTop (nhds 0) := by
    intro v
    simpa only [U] using
      inner_cc20GlobalLogTranslation_pow_tendsto_zero
        (Real.log p) hpLog frameValue v
  have htarget : Tendsto (fun N => target ((U ^ N) frameValue))
      atTop (nhds 0) :=
    compact_output_tendsto_zero_of_inner_tendsto_zero target
      (suffixActualBandCompleteCoupledAmbientTarget_unit_isCompactOperator
        owner p S) (fun N => (U ^ N) frameValue) hbounded hweak
  rw [NormedAddGroup.tendsto_nhds_zero] at htarget ⊢
  intro epsilon hepsilon
  filter_upwards [htarget epsilon hepsilon] with N hN
  simp only [suffixActualBandFiniteHorizonCoupledTail,
    ContinuousLinearMap.comp_apply,
    neg_cc20GlobalLogTranslation_pow_apply]
  rw [map_smul, norm_smul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  simpa only [U, cc20GlobalLogTranslation_pow_apply] using hN

/-- Consequently the explicit finite-horizon readouts reconstruct the actual
signed interior strongly on every fixed source vector. -/
theorem finiteHorizonReadout_comp_rawColumn_unit_apply_tendsto_interior
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier unitSoninScale) :
    Tendsto
      (fun N =>
        (suffixActualBandFiniteHorizonCoboundaryReadout
            owner unitSoninScale p S N ∘L
          newFrameAntiresonantColumn unitSoninScale p S) x)
      atTop (nhds (signedCompressedInteriorOwner
        owner unitSoninScale p S x)) := by
  have htail :=
    suffixActualBandFiniteHorizonCoupledTail_unit_apply_tendsto_zero
      owner p S x
  have hendpoint (N : Nat) := DFunLike.congr_fun
    (suffixActualBandFiniteHorizonCoboundaryReadout_comp_rawColumn
      owner unitSoninScale p S N) x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply] at hendpoint ⊢
  have hlimit : Tendsto
      (fun N => signedCompressedInteriorOwner owner unitSoninScale p S x -
        suffixActualBandFiniteHorizonCoupledTail
          owner unitSoninScale p S N x)
      atTop (nhds (signedCompressedInteriorOwner
        owner unitSoninScale p S x)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub htail)
  exact hlimit.congr' (Filter.Eventually.of_forall fun N => (hendpoint N).symm)

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorInfiniteHorizonTail
end CCM25Concrete
end Source
end ConnesWeilRH
