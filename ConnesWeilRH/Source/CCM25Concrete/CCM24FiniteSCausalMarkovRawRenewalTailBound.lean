/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawRenewalSupportSplit

/-!
# Raw renewal tail trace bound contract

Physical Gate 3U reduces exactly to a bound on the ordinary trace of the raw
source-band endpoint.  Proof 807 splits that complete physical renewal owner
into a compact-displacement part and a complementary tail at operator level:

```text
R_T = R_T^(<= B) + R_T^(> B)
```

This module records the trace-level consequence: taking the real ordinary trace
preserves the split exactly (using `ordinaryTraceAlong_add`), so the Gate bound
splits as a compact part plus a tail part.  A producer who supplies a uniform
tail-decay bound for `R^(> B)` therefore closes the canonical real Gate via the
already declared lower-factor persistence consumer, with compact root support
applied before any absolute value.

No new analytic claim is introduced here; this is a statement-planting contract
that fixes the exact tail-decay producer whose bound the compact support plus
trace split demands.  The genuinely missing analytic estimate is the tail
operator-norm / tail-trace decay of `R^(> B)`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawRenewalTailBound

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSForwardRenewal
open CCM24FiniteSGramResponse
open CCM24FiniteSMultiRenewal
open CCM24FiniteSPhysicalRenewalExpansion
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCausalMarkovRawRenewalBridge
open CCM24FiniteSCausalMarkovRawRenewalSupportSplit
open CCM24FiniteSSupportMajorant
open CCM24FiniteSTwoSidedIndexBridge
open CCM24FiniteSTwoSidedOperatorExpansion
open CCM24FiniteSTwoSidedRenewal
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The real ordinary trace of the complete physical renewal owner splits
exactly into the compact-displacement real trace plus the tail real trace, on
any source basis along which both pieces are trace class.  This is the
operator-level Proof 807 split read back onto the trace, before any absolute
value is taken. -/
theorem inverseLowerFactorPhysicalRenewalTrace_eq_support_add_tail
    {rho : Type*} (B : ℝ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hsupport : IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family))
    (htail : IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)) :
    (ordinaryTraceAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalResponse owner lambda family)).re =
      (ordinaryTraceAlong sourceBasis
        (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)).re +
        (ordinaryTraceAlong sourceBasis
          (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)).re := by
  rw [inverseLowerFactorPhysicalRenewalResponse_eq_support_add_tail]
  rw [ordinaryTraceAlong_add sourceBasis
    (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)
    (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)
    hsupport htail]
  norm_num

/-- Bounding the compact real trace and the tail real trace separately is
sufficient for the raw Gate endpoint: the absolute real trace is bounded by the
sum of the two piece bounds.  This is the exact triangle/assembly step that a
tail decay producer consumes. -/
theorem inverseLowerFactorPhysicalRenewalTrace_split_bound
    {rho : Type*} (B : ℝ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (boundSupport boundTail : ℝ)
    (hsupport : IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family))
    (htail : IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family))
    (hboundSupport : |(ordinaryTraceAlong sourceBasis
        (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)).re| ≤
        boundSupport)
    (hboundTail : |(ordinaryTraceAlong sourceBasis
        (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)).re| ≤
        boundTail) :
    |(ordinaryTraceAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalResponse owner lambda family)).re| ≤
        boundSupport + boundTail := by
  rw [inverseLowerFactorPhysicalRenewalTrace_eq_support_add_tail B owner lambda
    family sourceBasis hsupport htail]
  calc
    |((ordinaryTraceAlong sourceBasis
          (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)).re +
        (ordinaryTraceAlong sourceBasis
          (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)).re)| ≤
        |(ordinaryTraceAlong sourceBasis
            (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)).re| +
          |(ordinaryTraceAlong sourceBasis
            (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)).re| :=
      abs_add_le _ _
    _ ≤ boundSupport + boundTail := add_le_add hboundSupport hboundTail

/-- A producer for a tail trace-decay bound, uniform in the visible finite
family, closes the canonical real Gate exactly: the compact part is discarded
in favor of a single uniform tail bound applied to the whole Gate object with
compact root support before any absolute value.  This is the `(AA.32)` handoff
consumed through the already declared lower-factor persistence closure. -/
theorem canonicalRealGate3UAt_of_tailNormBound
    {rho : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (bound : ℝ)
    (hdecay :
      |(ordinaryTraceAlong sourceBasis
        (inverseLowerFactorPhysicalRenewalResponse owner lambda
          (canonicalFamily owner))).re| ≤ bound) :
    canonicalRealGate3UAt owner lambda sourceBasis bound := by
  rw [canonicalRealGate3UAt_iff_abs_inverseLowerFactorPhysicalRenewalTrace_le
    owner lambda sourceBasis bound]
  exact hdecay

/-! ## Operator-norm reduction of the raw renewal tail

The genuinely missing analytic estimate is a uniform decay of the tail operator
`R^(>B) = inverseLowerFactorPhysicalRenewalTailResponse`.  The operator-norm
side of that reduction is mechanical: each raw tail atom decomposes into a
signed raw coefficient times an index-independent-bounded unweighted kernel, and
the two-sided index bijection turns the coefficient-norm sum into the two-sided
tail raw total variation.  This section makes that reduction formal; what it
does **not** supply (and what the route still needs) is the decay of that tail
total variation in `B`.
-/

/-- Uniform operator-norm bound on the index-independent operator factor chain
of the paired physical renewal atom.  Each factor is a translation (isometric on
the carrier), an inclusion, an adjoint, an orthogonal projection, or a fixed
detector, so its norm is an index-independent constant.  The two translations
are dropped because each is norm-isometric (`norm_toContinuousLinearMap_le`). -/
theorem norm_finiteEulerPhysicalUnweightedRenewalAtom_le_const
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    ‖finiteEulerPhysicalUnweightedRenewalAtom owner lambda family forwardIndex
        renewalIndex‖ ≤
      ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
        ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
        ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖ := by
  -- Bound the unweighted atom's norm chain by peeling each `opNorm_comp_le`
  -- from the right.  The two translations are isometric, so their factor is 1.
  let tForward : finiteSCarrier →L[ℂ] finiteSCarrier :=
    (cc20GlobalLogTranslation
      (finiteEulerForwardDisplacement family.visiblePrimes forwardIndex)).toContinuousLinearMap
  let tRenewal : finiteSCarrier →L[ℂ] finiteSCarrier :=
    (cc20GlobalLogTranslation
      (finiteEulerRenewalDisplacement family.visiblePrimes renewalIndex)).toContinuousLinearMap
  let body : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
    detectorOperator owner ∘L (ContinuousLinearMap.id Complex finiteSCarrier -
        sourceSoninProjection lambda) ∘L tForward ∘L transportedSoninProjection lambda family
        ∘L tRenewal ∘L sourceInclusion lambda
  have hBody :
      ‖body‖ ≤ ‖detectorOperator owner‖ *
        ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
        ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖ := by
    rw [show body = detectorOperator owner ∘L
        (ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda) ∘L
        tForward ∘L transportedSoninProjection lambda family ∘L tRenewal ∘L
        sourceInclusion lambda by rfl]
    -- Peel `opNorm_comp_le` one factor at a time from the left, keeping every
    -- translation as an explicit norm factor; the final step drops the two
    -- (isometric, norm ≤ 1) translation factors with `nlinarith`.  Each
    -- hypothesis is a plain nonneg real norm.
    have hfwd : ‖tForward‖ ≤ 1 :=
      (cc20GlobalLogTranslation
        (finiteEulerForwardDisplacement family.visiblePrimes forwardIndex)).norm_toContinuousLinearMap_le
    have hren : ‖tRenewal‖ ≤ 1 :=
      (cc20GlobalLogTranslation
        (finiteEulerRenewalDisplacement family.visiblePrimes renewalIndex)).norm_toContinuousLinearMap_le
    calc
      ‖detectorOperator owner ∘L
          (ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda) ∘L
          tForward ∘L transportedSoninProjection lambda family ∘L tRenewal ∘L
          sourceInclusion lambda‖ ≤
          ‖detectorOperator owner‖ *
            ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda) ∘L
              tForward ∘L transportedSoninProjection lambda family ∘L tRenewal ∘L
              sourceInclusion lambda‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖detectorOperator owner‖ *
          (‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
            ‖tForward ∘L transportedSoninProjection lambda family ∘L tRenewal ∘L
              sourceInclusion lambda‖) := by
            exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ ‖detectorOperator owner‖ *
          (‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
            (‖tForward‖ *
              ‖transportedSoninProjection lambda family ∘L tRenewal ∘L sourceInclusion lambda‖)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ‖detectorOperator owner‖ *
          (‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
            (‖tForward‖ *
              (‖transportedSoninProjection lambda family‖ *
                ‖tRenewal ∘L sourceInclusion lambda‖))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ‖detectorOperator owner‖ *
          (‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
            (‖tForward‖ *
              (‖transportedSoninProjection lambda family‖ *
                (‖tRenewal‖ * ‖sourceInclusion lambda‖)))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ‖detectorOperator owner‖ *
          (‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
            (‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖)) := by
            -- Each factor is a nonneg norm and both translations have norm ≤ 1,
            -- so dropping the two translation factors cannot increase the nested
            -- product.  Peel the factors from the inside out with matching
            -- association.
            have hrenewal : ‖tRenewal‖ * ‖sourceInclusion lambda‖ ≤
                ‖sourceInclusion lambda‖ := by
              calc
                ‖tRenewal‖ * ‖sourceInclusion lambda‖ ≤ 1 * ‖sourceInclusion lambda‖ :=
                  mul_le_mul_of_nonneg_right hren (norm_nonneg _)
                _ = ‖sourceInclusion lambda‖ := by ring
            have hinner : ‖transportedSoninProjection lambda family‖ *
                (‖tRenewal‖ * ‖sourceInclusion lambda‖) ≤
                  ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖ :=
              mul_le_mul_of_nonneg_left hrenewal (norm_nonneg _)
            have hfwdOnly : ‖tForward‖ *
                (‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖) ≤
                  ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖ := by
              have hBC : 0 ≤ ‖transportedSoninProjection lambda family‖ *
                  ‖sourceInclusion lambda‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
              calc
                ‖tForward‖ * (‖transportedSoninProjection lambda family‖ *
                    ‖sourceInclusion lambda‖) ≤
                    1 * (‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖) :=
                  mul_le_mul_of_nonneg_right hfwd hBC
                _ = ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖ := by ring
            have hdrop :
                ‖tForward‖ *
                    (‖transportedSoninProjection lambda family‖ *
                      (‖tRenewal‖ * ‖sourceInclusion lambda‖)) ≤
                  ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖ := by
              calc
                ‖tForward‖ * (‖transportedSoninProjection lambda family‖ *
                    (‖tRenewal‖ * ‖sourceInclusion lambda‖)) ≤
                  ‖tForward‖ * (‖transportedSoninProjection lambda family‖ *
                    ‖sourceInclusion lambda‖) :=
                  mul_le_mul_of_nonneg_left hinner (norm_nonneg tForward)
                _ ≤ ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖ :=
                  hfwdOnly
            have hP : 0 ≤ ‖(ContinuousLinearMap.id Complex finiteSCarrier -
              sourceSoninProjection lambda)‖ := norm_nonneg _
            have hA : 0 ≤ ‖detectorOperator owner‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdrop hP) hA
          _ = ‖detectorOperator owner‖ * ‖(ContinuousLinearMap.id Complex finiteSCarrier -
              sourceSoninProjection lambda)‖ *
              ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖ := by
            ring
  -- The atom carries a leading `-(sourceInclusion)†`.  `neg_comp` is the simp
  -- rule `(-g) ∘SL f = -(g ∘SL f)`, so `norm_neg` then leaves the positive
  -- composite whose norm is controlled by `hBody`.
  change ‖-((sourceInclusion lambda)† ∘L body)‖ ≤
      ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
        ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
        ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖
  rw [norm_neg]
  calc
    ‖(sourceInclusion lambda)† ∘L body‖ ≤ ‖(sourceInclusion lambda)†‖ * ‖body‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(sourceInclusion lambda)†‖ * (‖detectorOperator owner‖ *
          ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
          ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖) := by
      exact mul_le_mul_of_nonneg_left hBody (norm_nonneg _)
    _ = ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
          ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
          ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖ := by
      ring

/-- Operator-norm bound on one raw tail atom: the raw signed coefficient times
the uniformly bounded unweighted kernel.  The coefficient-norm is the paired
two-sided raw weight (via `abs_rawPhysicalRenewalCoefficient_eq_twoSidedRawWeight`),
so the tail total variation stays explicitly on the weight side. -/
theorem norm_finiteEulerPhysicalRawRenewalTailAtom_le
    (B : ℝ) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    ‖finiteEulerPhysicalRawRenewalTailAtom B owner lambda family forwardIndex
        renewalIndex‖ ≤
      finiteEulerTwoSidedRawWeight family.visiblePrimes
        (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) *
        (‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
          ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
          ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖) := by
  unfold finiteEulerPhysicalRawRenewalTailAtom
  have hweight0 : 0 ≤ finiteEulerTwoSidedRawWeight family.visiblePrimes
      (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) :=
    finiteEulerTwoSidedRawWeight_nonneg family.visiblePrimes
      (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex))
  have hnorms0 : 0 ≤ ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
      ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
      ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖ := by positivity
  have hprod0 : 0 ≤ finiteEulerTwoSidedRawWeight family.visiblePrimes
      (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) *
      (‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
        ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
        ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖) :=
    mul_nonneg hweight0 hnorms0
  split_ifs with hdisp
  · simpa using hprod0
  · have hraw : finiteEulerPhysicalRawRenewalAtom owner lambda family forwardIndex
        renewalIndex =
        (finiteEulerProjectionSandwichRawSignedWeight family.visiblePrimes forwardIndex
          renewalIndex : ℂ) •
          finiteEulerPhysicalUnweightedRenewalAtom owner lambda family forwardIndex
            renewalIndex :=
      finiteEulerPhysicalRawRenewalAtom_eq_rawCoefficient_smul_unweighted owner lambda
        family forwardIndex renewalIndex
    rw [hraw]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_finiteEulerProjectionSandwichRawSignedWeight]
    exact mul_le_mul_of_nonneg_left
      (norm_finiteEulerPhysicalUnweightedRenewalAtom_le_const owner lambda family
        forwardIndex renewalIndex) hweight0

/-- Absolute operator-norm summability of the raw tail atoms in the renewal
index, for each fixed forward index. -/
theorem summable_norm_finiteEulerPhysicalRawRenewalTailAtom
    (B : ℝ) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    Summable (fun renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes =>
      ‖finiteEulerPhysicalRawRenewalTailAtom B owner lambda family forwardIndex
        renewalIndex‖) := by
  -- Fixing a forward index, the renewal-restricted pairing is injective (the
  -- full pairing is the two-sided-coordinate bijection), so precomposing the
  -- summable weight with it stays summable; then multiply by the fixed `C`.
  let C : ℝ := ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
    ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
    ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖
  have hpoint : ∀ renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
      ‖finiteEulerPhysicalRawRenewalTailAtom B owner lambda family forwardIndex
        renewalIndex‖ ≤
        finiteEulerTwoSidedRawWeight family.visiblePrimes
          (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) * C := by
    intro renewalIndex
    exact norm_finiteEulerPhysicalRawRenewalTailAtom_le B owner lambda family
      forwardIndex renewalIndex
  have hfull : Summable (finiteEulerTwoSidedRawWeight family.visiblePrimes) :=
    (finiteEulerTwoSidedRawWeight_hasSum family.visiblePrimes).summable
  have hinj : Function.Injective
        (fun renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes =>
          pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) := by
      intro r₁ r₂ hpr
      -- `split (pair (f, r))` is the pair identity, so its second component
      -- recovers the renewal coordinate.
      have hpairEq :
          (forwardIndex, r₁) = (forwardIndex, r₂) :=
        (split_pairForwardRenewalIndex family.visiblePrimes (forwardIndex, r₁)).symm.trans
          ((congrArg (splitForwardRenewalIndex family.visiblePrimes) hpr).trans
            (split_pairForwardRenewalIndex family.visiblePrimes (forwardIndex, r₂)))
      exact congrArg Prod.snd hpairEq
  have hmajorant : Summable
      (fun renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes =>
        finiteEulerTwoSidedRawWeight family.visiblePrimes
          (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) * C) :=
    (hfull.comp_injective hinj).mul_right C
  exact Summable.of_nonneg_of_le
    (fun _ : FiniteEulerRenewalIndex family.visiblePrimes => norm_nonneg _)
    hpoint hmajorant

end CCM24FiniteSCausalMarkovRawRenewalTailBound
end CCM25Concrete
end Source
end ConnesWeilRH
