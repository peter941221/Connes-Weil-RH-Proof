/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8P1BoundaryRootEnergyReduction
import ConnesWeilRH.Dev.C1G8R3SurvivorCoframeBridge
import ConnesWeilRH.Dev.C1G8R3RadialBoundaryGapSplit

/-!
# Boundary output factorization bridge: every G8 boundary leg on the source carrier

Map 042 bridge facts B2 and the B1/B2 assembly.  By structural induction over
the visible-prime suffix, every actual boundary output of
`suffixEulerBoundaryOutputMaps` — hence every summand of
`finiteEulerMetricCoframeBoundaryMaps` — factors as an ambient operator `M`
composed with the source inclusion and a purely source-side operator `N`.

Together with the exact pointwise split at the Sonin projection this gives,
for each boundary output `M ∘L J ∘L N`, the unconditional decomposition of the
boundary diagonal energy into

* IN (in-Sonin response) `J† C M J` after `N`, and
* OUT (leakage band) `(I - P) C M J` after `N`, which by the record-1494
  identity splits exactly into the radial-boundary leg `(I - E) C M J` and
  the internal-gap leg `(E - P) E C M J`, both with `M` inside.

The aggregate assembly feeds the record-1492 consumer unchanged: per-output
estimates of the three legs imply the exact `hBoundary` energy condition.
No estimate is claimed for any leg; RH is not touched.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSActualBandQuadraticCycle
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar
open Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
open Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open Source.CCM25Concrete.CCM24FiniteSTransportBounds
open Source.CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open Source.CCM25Concrete.SelectedWeilSquare
open Source.C1G8P1MetricChannels
open scoped ENNReal InnerProduct InnerProductSpace

local notation "Carrier" => finiteSCarrier

noncomputable local instance boundaryBridgeCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The head boundary output of the `p :: S` Schur step factors through the
source inclusion: its old frame is the polar frame at `p :: S`, whose Sonin
part is exactly the source inclusion composed with the Gram inverse-sqrt. -/
theorem suffixEulerBoundaryOutputMaps_cons_head_factorization
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ∃ (M : finiteSCarrier →L[ℂ] finiteSCarrier)
        (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda),
      ((suffixEulerAmbientProduct S)† ∘L
          (suffixEulerFrameSchurStep lambda p S).boundaryDagger) =
        M ∘L sourceInclusion lambda ∘L N := by
  refine ⟨(suffixEulerAmbientProduct S)† ∘L
      (ContinuousLinearMap.id ℂ finiteSCarrier -
        newSuffixFrame lambda S ∘L (newSuffixFrame lambda S)†) ∘L
      (normalizedPrimeEulerFrameTransport p)† ∘L
        parameterizedFiniteEulerFactor 1 (p :: S),
    parameterizedSoninGramInvSqrt lambda 1 (p :: S) (by norm_num), ?_⟩
  have hbd : (suffixEulerFrameSchurStep lambda p S).boundaryDagger =
      (ContinuousLinearMap.id ℂ finiteSCarrier -
        newSuffixFrame lambda S ∘L (newSuffixFrame lambda S)†) ∘L
      (normalizedPrimeEulerFrameTransport p)† ∘L oldSuffixFrame lambda p S :=
    rfl
  have hframe : oldSuffixFrame lambda p S =
      parameterizedFiniteEulerFactor 1 (p :: S) ∘L sourceInclusion lambda ∘L
        parameterizedSoninGramInvSqrt lambda 1 (p :: S) (by norm_num) := by
    unfold oldSuffixFrame parameterizedSoninPolarFrame
      Source.CCM25Concrete.CCM24FiniteSFrameGramCalculus.parameterizedSoninFrame
      sourceInclusion
    rfl
  apply ContinuousLinearMap.ext
  intro x
  simp only [hbd, hframe, ContinuousLinearMap.comp_apply]

/-- Bridge fact B1 (map 042 §3): every actual boundary output factors as an
ambient operator composed with the source inclusion and a source-side
operator. -/
theorem suffixEulerBoundaryOutputMaps_factorization
    (lambda : CCM24SoninScale) :
    ∀ (S : List CCM24VisiblePrime)
        (output : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier),
      output ∈ suffixEulerBoundaryOutputMaps lambda S →
      ∃ (M : finiteSCarrier →L[ℂ] finiteSCarrier)
          (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda),
        output = M ∘L sourceInclusion lambda ∘L N := by
  intro S
  induction S with
  | nil => intro output hmem; cases hmem
  | cons p S ih =>
      intro output hmem
      simp only [suffixEulerBoundaryOutputMaps, List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · exact suffixEulerBoundaryOutputMaps_cons_head_factorization lambda p S
      · obtain ⟨output', hmem', hout⟩ := List.mem_map.mp hmem'
        obtain ⟨M, N, hMN⟩ := ih output' hmem'
        exact ⟨M, N ∘L (suffixEulerFrameTransition lambda p S)†,
          by rw [← hout, hMN]; simp only [ContinuousLinearMap.comp_assoc]⟩

/-- Every summand of the actual metric coframe boundary maps factors the same
way, with the final Gram inverse-sqrt absorbed into the source side. -/
theorem finiteEulerMetricCoframeBoundaryMaps_factorization
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (output : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (hmem : output ∈ finiteEulerMetricCoframeBoundaryMaps lambda family) :
    ∃ (M : finiteSCarrier →L[ℂ] finiteSCarrier)
        (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda),
      output = M ∘L sourceInclusion lambda ∘L N := by
  unfold finiteEulerMetricCoframeBoundaryMaps at hmem
  obtain ⟨raw, hraw, hrawout⟩ := List.mem_map.mp hmem
  obtain ⟨M, N, hMN⟩ := suffixEulerBoundaryOutputMaps_factorization lambda
    family.visiblePrimes raw hraw
  refine ⟨M, N ∘L parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
    (by norm_num), ?_⟩
  rw [← hrawout, hMN]
  simp only [ContinuousLinearMap.comp_assoc]

/-- Bridge fact B2, IN/OUT form (map 042 §4): for any ambient factor `M` and
source-side factor `N`, the boundary diagonal energy at the composed leg
splits exactly into the in-Sonin response and the leakage band. -/
theorem g8AmbientSourceLeg_energy_normSq_split
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (M : finiteSCarrier →L[ℂ] finiteSCarrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (w : sourceSoninCarrier lambda) :
    ‖(rootConvolution owner ∘L M ∘L sourceInclusion lambda ∘L N) w‖ ^ 2 =
      ‖((sourceInclusion lambda)† ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) (N w)‖ ^ 2 +
        ‖((ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) (N w)‖ ^ 2 :=
  g8BridgeSoninCarrier_normSq_split lambda
    ((rootConvolution owner ∘L M ∘L sourceInclusion lambda) (N w))

/-- Bridge fact B2, OUT legs (map 042 §4): the leakage band of a composed
boundary leg carries the ambient factor `M` inside the record-1494 identity,
so it splits exactly into the radial-boundary leg and the internal-gap leg. -/
theorem g8AmbientSourceLeg_outLeg_pointwise_eq_boundary_add_gap
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (M : finiteSCarrier →L[ℂ] finiteSCarrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (w : sourceSoninCarrier lambda) :
    ((ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda) ∘L rootConvolution owner ∘L M ∘L
      sourceInclusion lambda ∘L N) w =
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
          radialSupportProjection lambda) ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) (N w) +
        ((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) (N w) := by
  have h := radialSoninComplement_comp_operator_comp_input_eq_boundary_add_gap
    lambda (sourceInclusion lambda) (rootConvolution owner ∘L M)
  have hpoint := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
    T (N w)) h
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply] at hpoint ⊢
  exact hpoint

/- The internal-gap output splits along the source Sonin projection.  The
remaining complementary input is the only part not covered by the generic
source-range B4 estimate. -/
theorem g8AmbientSourceLeg_gapLeg_pointwise_eq_sourceRange_add_complement
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (M : finiteSCarrier →L[ℂ] finiteSCarrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (w : sourceSoninCarrier lambda) :
    (((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
        radialSupportProjection lambda ∘L rootConvolution owner ∘L M ∘L
      sourceInclusion lambda ∘L N) w) =
      (((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L rootConvolution owner ∘L
        sourceSoninProjection lambda ∘L M ∘L sourceInclusion lambda ∘L N) w) +
      (((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L rootConvolution owner ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) ∘L M ∘L sourceInclusion lambda ∘L N) w) := by
  let D := (radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
    radialSupportProjection lambda ∘L rootConvolution owner
  let y := (M ∘L sourceInclusion lambda ∘L N) w
  have hy : y = sourceSoninProjection lambda y +
      (ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda) y := by
    simp only [y, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    abel
  have hD := congrArg D hy
  simpa only [D, y, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.map_add] using hD

/- The unresolved complement is exactly the source-projection commutator of
the ambient factor with the inclusion. -/
theorem sourceSoninComplement_comp_ambientFactor_comp_sourceInclusion_eq_commutator
    (lambda : CCM24SoninScale) (M : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        M ∘L sourceInclusion lambda =
      (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        (M ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L M) ∘L sourceInclusion lambda := by
  have hPJ : sourceSoninProjection lambda ∘L sourceInclusion lambda =
      sourceInclusion lambda := by
    exact sourceSoninProjection_comp_sourceInclusion_eq_self lambda
  have hP2 : sourceSoninProjection lambda ∘L sourceSoninProjection lambda =
      sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  apply ContinuousLinearMap.ext
  intro x
  have hPJx := DFunLike.congr_fun hPJ x
  have hP2x := DFunLike.congr_fun hP2 (M (sourceInclusion lambda x))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub] at hPJx hP2x ⊢
  rw [hPJx, hP2x]
  abel

/- A source-range ambient factor contributes no complementary commutator.
This is the zero branch for the atomic estimates in the finite induction. -/
theorem sourceSoninComplement_comp_commutator_sourceRange_eq_zero
    (lambda : CCM24SoninScale) (M : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hM : sourceSoninProjection lambda ∘L M ∘L sourceInclusion lambda =
      M ∘L sourceInclusion lambda) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        (M ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L M) ∘L sourceInclusion lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hMpoint := DFunLike.congr_fun hM x
  have hJpoint := DFunLike.congr_fun
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda) x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub] at hMpoint hJpoint ⊢
  simp only [hJpoint, hMpoint, sub_self, map_zero,
    ContinuousLinearMap.zero_apply]

/- The orthogonal branch has an exact complementary-column normal form. -/
theorem sourceSoninComplement_comp_commutator_sourceOrthogonal_eq
    (lambda : CCM24SoninScale) (M : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hM : sourceSoninProjection lambda ∘L M ∘L sourceInclusion lambda = 0) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        (M ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L M) ∘L sourceInclusion lambda =
      (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        M ∘L sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro x
  have hMpoint := DFunLike.congr_fun hM x
  have hJpoint := DFunLike.congr_fun
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda) x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    at hMpoint hJpoint
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub] at hMpoint hJpoint ⊢
  rw [hJpoint, hMpoint]
  simp

/-- Leibniz rule for the source-projection commutator.  It is the induction
step for expanding a finite Euler boundary factor into atomic factors. -/
theorem ambientProduct_commutator_eq_leibniz_sum
    (lambda : CCM24SoninScale)
    (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
    A ∘L B ∘L sourceSoninProjection lambda -
        sourceSoninProjection lambda ∘L A ∘L B =
      A ∘L (B ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L B) +
        (A ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L A) ∘L B := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, map_sub]
  abel

/-- Hilbert--Schmidt induction consumer for the commutator Leibniz rule. -/
theorem ambientProduct_commutator_sourceBasis_normSq_summable_of_leibniz
    (lambda : CCM24SoninScale)
    (A B D : finiteSCarrier →L[ℂ] finiteSCarrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hleft : Summable fun i : ρ =>
      ‖(D ∘L A ∘L (B ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L B) ∘L sourceInclusion lambda ∘L N)
        (sourceBasis i)‖ ^ 2)
    (hright : Summable fun i : ρ =>
      ‖(D ∘L (A ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L A) ∘L B ∘L
        sourceInclusion lambda ∘L N) (sourceBasis i)‖ ^ 2) :
    Summable fun i : ρ =>
      ‖(D ∘L (A ∘L B ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L A ∘L B) ∘L
        sourceInclusion lambda ∘L N) (sourceBasis i)‖ ^ 2 := by
  have hsum := PositiveTrace.summable_normSq_add sourceBasis
    (D ∘L A ∘L (B ∘L sourceSoninProjection lambda -
      sourceSoninProjection lambda ∘L B) ∘L sourceInclusion lambda ∘L N)
    (D ∘L (A ∘L sourceSoninProjection lambda -
      sourceSoninProjection lambda ∘L A) ∘L B ∘L sourceInclusion lambda ∘L N)
    hleft hright
  have hEq :
      (D ∘L (A ∘L B ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L A ∘L B) ∘L
        sourceInclusion lambda ∘L N) =
      (D ∘L A ∘L (B ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L B) ∘L sourceInclusion lambda ∘L N) +
      (D ∘L (A ∘L sourceSoninProjection lambda -
          sourceSoninProjection lambda ∘L A) ∘L B ∘L
        sourceInclusion lambda ∘L N) := by
    rw [ambientProduct_commutator_eq_leibniz_sum]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      map_add]
  refine hsum.congr (fun i => ?_)
  exact congrArg (fun z : finiteSCarrier => ‖z‖ ^ 2)
    (DFunLike.congr_fun hEq (sourceBasis i)).symm

/-- Real algebra: from the exact split, the in-Sonin term is dominated by the
full term. -/
private theorem inLeg_le_of_split {a b c : ℝ} (hsplit : c = a + b)
    (hb : 0 ≤ b) : a ≤ c := by
  linarith

/-- Per-output necessity: the composed boundary energy controls the in-Sonin
response leg. -/
theorem g8AmbientSourceLeg_inLeg_normSq_summable_of_energy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (M : finiteSCarrier →L[ℂ] finiteSCarrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (henergy : Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L M ∘L sourceInclusion lambda ∘L N)
        (sourceBasis i)‖ ^ 2) :
    Summable fun i : ρ =>
      ‖((sourceInclusion lambda)† ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) (N (sourceBasis i))‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) henergy
  exact inLeg_le_of_split
    (g8AmbientSourceLeg_energy_normSq_split owner lambda M N (sourceBasis i))
    (sq_nonneg _)

/-- Per-output sufficiency: the three legs (in-Sonin, radial-boundary,
internal-gap) reproduce the composed boundary energy, with the two leakage
legs recombined by the record-1494 identity and the triangle inequality. -/
theorem g8AmbientSourceLeg_energy_normSq_summable_of_legs
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (M : finiteSCarrier →L[ℂ] finiteSCarrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hin : Summable fun i : ρ =>
      ‖((sourceInclusion lambda)† ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) (N (sourceBasis i))‖ ^ 2)
    (hrad : Summable fun i : ρ =>
      ‖((ContinuousLinearMap.id ℂ finiteSCarrier -
          radialSupportProjection lambda) ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) (N (sourceBasis i))‖ ^ 2)
    (hgap : Summable fun i : ρ =>
      ‖((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) (N (sourceBasis i))‖ ^ 2) :
    Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L M ∘L sourceInclusion lambda ∘L N)
        (sourceBasis i)‖ ^ 2 := by
  have hsplit := radialSoninComplement_comp_operator_comp_input_eq_boundary_add_gap
    lambda (sourceInclusion lambda) (rootConvolution owner ∘L M)
  have hadd := PositiveTrace.summable_normSq_add sourceBasis
    (((ContinuousLinearMap.id ℂ finiteSCarrier -
          radialSupportProjection lambda) ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) ∘L N)
    (((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
        radialSupportProjection lambda ∘L rootConvolution owner ∘L M ∘L
      sourceInclusion lambda) ∘L N) hrad hgap
  have hsplitN :
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda ∘L N) =
      (((ContinuousLinearMap.id ℂ finiteSCarrier -
            radialSupportProjection lambda) ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) ∘L N) +
      (((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda) ∘L N) := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      T (N x)) hsplit
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply] using hx
  have hout : Summable fun i : ρ =>
      ‖((ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) ∘L rootConvolution owner ∘L M ∘L
        sourceInclusion lambda ∘L N) (sourceBasis i)‖ ^ 2 := by
    refine hadd.congr (fun i => ?_)
    rw [congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      T (sourceBasis i)) hsplitN]
  exact (hin.add hout).congr (fun i =>
    (g8AmbientSourceLeg_energy_normSq_split owner lambda M N
      (sourceBasis i)).symm)

/-- The aggregate assembly feeding the record-1492 consumer unchanged: if
every actual boundary output admits a factorization whose three legs are
square-summable, then the exact `hBoundary` energy condition holds. -/
theorem g8MetricVisibleBoundary_root_energy_summable_of_legs
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hleg : ∀ output ∈ finiteEulerMetricCoframeBoundaryMaps lambda family,
      ∃ (M : finiteSCarrier →L[ℂ] finiteSCarrier)
          (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda),
        output = M ∘L sourceInclusion lambda ∘L N ∧
        ((Summable fun i : ρ =>
          ‖((sourceInclusion lambda)† ∘L rootConvolution owner ∘L M ∘L
            sourceInclusion lambda) (N (sourceBasis i))‖ ^ 2) ∧
        (Summable fun i : ρ =>
          ‖((ContinuousLinearMap.id ℂ finiteSCarrier -
              radialSupportProjection lambda) ∘L rootConvolution owner ∘L M ∘L
          sourceInclusion lambda) (N (sourceBasis i))‖ ^ 2) ∧
        Summable fun i : ρ =>
          ‖((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
              radialSupportProjection lambda ∘L rootConvolution owner ∘L M ∘L
          sourceInclusion lambda) (N (sourceBasis i))‖ ^ 2)) :
    Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L
          g8MetricVisibleBoundaryCoframe lambda family) (sourceBasis i)‖ ^ 2 := by
  refine g8MetricVisibleBoundary_root_energy_summable_of_each_output owner lambda
    family sourceBasis (fun output hmem => ?_)
  obtain ⟨M, N, hfac, hin, hrad, hgap⟩ := hleg output hmem
  rw [hfac]
  exact g8AmbientSourceLeg_energy_normSq_summable_of_legs owner lambda M N
    sourceBasis hin hrad hgap

end Dev
end ConnesWeilRH
