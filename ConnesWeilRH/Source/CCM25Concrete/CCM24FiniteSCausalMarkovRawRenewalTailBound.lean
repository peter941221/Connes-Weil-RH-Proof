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

/-- Axis-A0: the compact support piece inherits trace-class legality by
subtraction.  The full physical response splits as support plus tail
(`inverseLowerFactorPhysicalRenewalResponse_eq_support_add_tail`), so given a
trace-class witness for the full response and for the tail, the support piece is
trace-class along the same basis.  This removes the explicit `hsupport` premise
from the split and split-bound consumers once the tail is bounded, using only
`isTraceClassAlong_sub` (no new analytic estimate). -/
theorem inverseLowerFactorPhysicalRenewalSupport_isTraceClassAlong_of_full_and_tail
    {rho : Type*} (B : Real)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho Complex (sourceSoninCarrier lambda))
    (hfull : IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalResponse owner lambda family))
    (htail : IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)) :
    IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family) := by
  have hsupport_eq : inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda
      family =
      inverseLowerFactorPhysicalRenewalResponse owner lambda family -
        inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family := by
    rw [inverseLowerFactorPhysicalRenewalResponse_eq_support_add_tail B owner lambda
      family]
    abel
  rw [hsupport_eq]
  exact isTraceClassAlong_sub sourceBasis
    (inverseLowerFactorPhysicalRenewalResponse owner lambda family)
    (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family) hfull htail

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
tail raw total variation.  This section assembles the per-atom facts into a
single **whole-tail** operator-norm bound

```text
‖R^(>B)‖ ≤ C0 · ∑'_{D>B} twoSidedRawWeight
```

with the `C0` constant carrying every index-independent operator norm, and then
chains the (already formal) exponential tail decay
`∑'_{D>B} w ≤ exp(-B/4)·∏_p (1+ρ_p)/(1-ρ_p)` onto it to get

```text
‖R^(>B)‖ ≤ C0 · exp(-B/4) · ∏_p primeTwoSidedQuarterMass
```

No trace is interchanged anywhere here: coefficient support does not give trace
support (Proof 807 boundary), so the module produces the tail *operator-norm*
bound that a trace-class layer then feeds through `abs (Re Tr(R^(>B)))`.
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

/-- The operator-norm, index-independent constant of one paired raw renewal
kernel: `‖J†‖ * ‖det‖ * ‖(I-P)‖ * ‖transported‖ * ‖J‖`.  This is the exact
right-hand side of `norm_finiteEulerPhysicalUnweightedRenewalAtom_le_const`. -/
noncomputable def rawRenewalTailNormConstant
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : ℝ :=
  ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
    ‖(ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda)‖ *
    ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖

/-- A raw tail atom has operator norm at most the raw paired weight times the
family-independent constant.  This is the same bound as
`norm_finiteEulerPhysicalRawRenewalTailAtom_le`, with the constant named. -/
theorem norm_finiteEulerPhysicalRawRenewalTailAtom_le_const
    (B : ℝ) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    ‖finiteEulerPhysicalRawRenewalTailAtom B owner lambda family forwardIndex
        renewalIndex‖ ≤
      finiteEulerTwoSidedRawWeight family.visiblePrimes
        (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) *
        rawRenewalTailNormConstant owner lambda family := by
  rw [rawRenewalTailNormConstant]
  exact norm_finiteEulerPhysicalRawRenewalTailAtom_le B owner lambda family
    forwardIndex renewalIndex

/-- The raw tail atom bound is also true with the constant on the left (product
commutes). -/
theorem norm_finiteEulerPhysicalRawRenewalTailAtom_le_const'
    (B : ℝ) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    ‖finiteEulerPhysicalRawRenewalTailAtom B owner lambda family forwardIndex
        renewalIndex‖ ≤
      rawRenewalTailNormConstant owner lambda family *
        finiteEulerTwoSidedRawWeight family.visiblePrimes
          (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) := by
  rw [mul_comm]
  exact norm_finiteEulerPhysicalRawRenewalTailAtom_le_const B owner lambda family
    forwardIndex renewalIndex

/-- A raw tail atom has operator norm at most the constant times the **indicated**
raw weight: `0` on `{D ≤ B}` (where the tail atom vanishes) and the plain bound
on `{D > B}`.  The indicator is what converts the summed per-atom bound into an
exponential tail decay. -/
theorem norm_finiteEulerPhysicalRawRenewalTailAtom_le_const_ind
    (B : ℝ) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    ‖finiteEulerPhysicalRawRenewalTailAtom B owner lambda family forwardIndex
        renewalIndex‖ ≤
      rawRenewalTailNormConstant owner lambda family *
        (if B < finiteEulerTwoSidedDisplacement family.visiblePrimes
            (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) then
            finiteEulerTwoSidedRawWeight family.visiblePrimes
              (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex))
          else 0) := by
  have h : ‖finiteEulerPhysicalRawRenewalTailAtom B owner lambda family forwardIndex
      renewalIndex‖ ≤
      rawRenewalTailNormConstant owner lambda family *
        (if B < finiteEulerTwoSidedDisplacement family.visiblePrimes
            (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) then
            finiteEulerTwoSidedRawWeight family.visiblePrimes
              (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex))
          else 0) := by
    by_cases hD : B < finiteEulerTwoSidedDisplacement family.visiblePrimes
        (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex))
    · rw [if_pos hD]
      exact norm_finiteEulerPhysicalRawRenewalTailAtom_le_const' B owner lambda family
        forwardIndex renewalIndex
    · rw [if_neg hD]
      unfold finiteEulerPhysicalRawRenewalTailAtom
      rw [if_pos (le_of_not_gt hD)]
      simp
  by_cases hD : B < finiteEulerTwoSidedDisplacement family.visiblePrimes
      (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex))
  · rw [if_pos hD]
    rw [if_pos hD] at h
    exact h
  · rw [if_neg hD]
    unfold finiteEulerPhysicalRawRenewalTailAtom
    rw [if_pos (le_of_not_gt hD)]
    simp

/-- The renewed-fiber sum of (indicator · two-sided raw weight · C0) is summable
in the renewal index, for each fixed forward index.  The plain raw-weight fiber
is summable (the pairing is injective in the renewal coordinate, and the full
weight is summable); the indicator and the constant factor preserve summability. -/
theorem summable_twoSidedRawWeight_tail_fiber
    (B : ℝ) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    Summable (fun renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes =>
      rawRenewalTailNormConstant owner lambda family *
        (if B < finiteEulerTwoSidedDisplacement family.visiblePrimes
            (pairForwardRenewalIndex family.visiblePrimes
              (forwardIndex, renewalIndex)) then
            finiteEulerTwoSidedRawWeight family.visiblePrimes
              (pairForwardRenewalIndex family.visiblePrimes
                (forwardIndex, renewalIndex))
          else 0)) := by
  classical
  have hweightFiber : Summable (fun renewalIndex : FiniteEulerRenewalIndex
      family.visiblePrimes =>
      finiteEulerTwoSidedRawWeight family.visiblePrimes
        (pairForwardRenewalIndex family.visiblePrimes
          (forwardIndex, renewalIndex))) := by
    exact ((finiteEulerTwoSidedRawWeight_hasSum family.visiblePrimes).summable
      ).comp_injective (fun r₁ r₂ hp =>
        by
          have hpairEq : (forwardIndex, r₁) = (forwardIndex, r₂) :=
            (split_pairForwardRenewalIndex family.visiblePrimes (forwardIndex, r₁)).symm.trans
              ((congrArg (splitForwardRenewalIndex family.visiblePrimes) hp).trans
                (split_pairForwardRenewalIndex family.visiblePrimes (forwardIndex, r₂)))
          exact congrArg Prod.snd hpairEq)
  have hle : ∀ renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
      (if B < finiteEulerTwoSidedDisplacement family.visiblePrimes
          (pairForwardRenewalIndex family.visiblePrimes
            (forwardIndex, renewalIndex)) then
          finiteEulerTwoSidedRawWeight family.visiblePrimes
            (pairForwardRenewalIndex family.visiblePrimes
              (forwardIndex, renewalIndex))
        else 0) ≤ finiteEulerTwoSidedRawWeight family.visiblePrimes
          (pairForwardRenewalIndex family.visiblePrimes
            (forwardIndex, renewalIndex)) := by
    intro renewalIndex
    split_ifs with hB
    · rfl
    · exact finiteEulerTwoSidedRawWeight_nonneg _ _
  have hinder : Summable (fun renewalIndex : FiniteEulerRenewalIndex
      family.visiblePrimes =>
      if B < finiteEulerTwoSidedDisplacement family.visiblePrimes
          (pairForwardRenewalIndex family.visiblePrimes
            (forwardIndex, renewalIndex)) then
          finiteEulerTwoSidedRawWeight family.visiblePrimes
            (pairForwardRenewalIndex family.visiblePrimes
              (forwardIndex, renewalIndex))
        else 0) := by
    apply Summable.of_nonneg_of_le
    · intro renewalIndex
      split_ifs with hB
      · exact finiteEulerTwoSidedRawWeight_nonneg _ _
      · simp
    · exact hle
    · exact hweightFiber
  exact hinder.mul_left (rawRenewalTailNormConstant owner lambda family)

/-- The `C0`-scaled indicator·weight double-sum reassociates onto the two-sided
coordinate: `Σ_f Σ'ᵣ C0·[D>B]·w(f,r) = C0 · Σ'_{D>B} w`.  The forward sum is
finite, so `tsum_fintype` collapses it and `Summable.tsum_prod` flattens the
nested `Σ'f Σ'ᵣ` into a product tsum; `tsum_mul_left` pulls the constant out;
and the equiv `split` reindexes the pure-weight product tsum onto the two-sided
coordinate (`pair (split index) = index`). -/
theorem rawRenewalTailWeightDoubleSum_reassoc
    (B : ℝ) (C0 : ℝ) (S : List CCM24VisiblePrime) :
    (∑ forwardIndex : FiniteEulerForwardIndex S,
      ∑' renewalIndex : FiniteEulerRenewalIndex S,
        C0 *
          if B < finiteEulerTwoSidedDisplacement S
              (pairForwardRenewalIndex S (forwardIndex, renewalIndex)) then
            finiteEulerTwoSidedRawWeight S
              (pairForwardRenewalIndex S (forwardIndex, renewalIndex))
          else 0) =
      C0 * (∑' index : FiniteEulerTwoSidedRenewalIndex S,
        if B < finiteEulerTwoSidedDisplacement S index then
          finiteEulerTwoSidedRawWeight S index
        else 0) := by
  classical
  let ind := fun (p : FiniteEulerForwardIndex S × FiniteEulerRenewalIndex S) =>
    if B < finiteEulerTwoSidedDisplacement S (pairForwardRenewalIndex S p) then
      finiteEulerTwoSidedRawWeight S (pairForwardRenewalIndex S p)
    else 0
  let indMode := fun (p : FiniteEulerForwardIndex S × FiniteEulerRenewalIndex S) =>
    C0 * ind p
  have hindModeSum : Summable indMode := by
    have hrawSum : Summable (fun p : FiniteEulerForwardIndex S ×
        FiniteEulerRenewalIndex S =>
        finiteEulerTwoSidedRawWeight S (pairForwardRenewalIndex S p)) := by
      apply (finiteEulerTwoSidedRawWeight_hasSum S).summable.comp_injective
      intro p₁ p₂ hp
      exact (split_pairForwardRenewalIndex S p₁).symm.trans
        ((congrArg (splitForwardRenewalIndex S) hp).trans
          (split_pairForwardRenewalIndex S p₂))
    have hle : ∀ p, ind p ≤ finiteEulerTwoSidedRawWeight S
        (pairForwardRenewalIndex S p) := by
      intro p
      by_cases hB : B < finiteEulerTwoSidedDisplacement S
          (pairForwardRenewalIndex S p)
      · simp [ind, hB]
      · simp [ind, hB, finiteEulerTwoSidedRawWeight_nonneg]
    have hnonneg : ∀ p, 0 ≤ ind p := by
      intro p
      by_cases hB : B < finiteEulerTwoSidedDisplacement S
          (pairForwardRenewalIndex S p)
      · simp [ind, hB, finiteEulerTwoSidedRawWeight_nonneg]
      · simp [ind, hB]
    have hindSum : Summable ind := Summable.of_nonneg_of_le hnonneg hle hrawSum
    simpa [indMode] using hindSum.mul_left C0
  rw [← tsum_fintype (L := SummationFilter.unconditional
      (FiniteEulerForwardIndex S))]
  rw [← Summable.tsum_prod (h := hindModeSum)]
  conv_lhs => rw [tsum_mul_left]
  rw [show (∑' p : FiniteEulerForwardIndex S × FiniteEulerRenewalIndex S, ind p) =
        (∑' index : FiniteEulerTwoSidedRenewalIndex S,
          if B < finiteEulerTwoSidedDisplacement S index then
            finiteEulerTwoSidedRawWeight S index else 0) by
    rw [← (forwardRenewalIndexEquiv S).symm.tsum_eq]
    apply tsum_congr
    intro index
    dsimp [ind]
    change (if B < finiteEulerTwoSidedDisplacement S (pairForwardRenewalIndex S
        (splitForwardRenewalIndex S index)) then
        finiteEulerTwoSidedRawWeight S (pairForwardRenewalIndex S
          (splitForwardRenewalIndex S index)) else 0) =
      (if B < finiteEulerTwoSidedDisplacement S index then
        finiteEulerTwoSidedRawWeight S index else 0)
    rw [pair_splitForwardRenewalIndex S index]]

/-- The whole tail operator `R^(>B)` has operator norm at most the constant times
the raw-weight tail total variation on `{D > B}`:
`‖R^(>B)‖ ≤ C0 · ∑'_{D>B} twoSidedRawWeight`.  Proof 807 splits
`R^(>B) = ∑_f ∑'_r tailAtom(f,r)`; the finite forward sum is folded per fiber
(each renewal fiber is absolutely summable), the triangle inequality moves the
norm inside, the per-atom indicated bound converts each norm to the indicator
times the weight times `C0`, and the weight double-sum is reindexed onto the
two-sided coordinate by the coordinate bijection. -/
theorem norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const
    (B : ℝ) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family‖ ≤
      rawRenewalTailNormConstant owner lambda family *
        (∑' index : FiniteEulerTwoSidedRenewalIndex family.visiblePrimes,
          if B < finiteEulerTwoSidedDisplacement family.visiblePrimes index then
            finiteEulerTwoSidedRawWeight family.visiblePrimes index
          else 0) := by
  unfold inverseLowerFactorPhysicalRenewalTailResponse
  calc
    ‖∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
        ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          finiteEulerPhysicalRawRenewalTailAtom B owner lambda family
            forwardIndex renewalIndex‖ ≤
      ∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
        ‖∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          finiteEulerPhysicalRawRenewalTailAtom B owner lambda family
            forwardIndex renewalIndex‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
        ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          ‖finiteEulerPhysicalRawRenewalTailAtom B owner lambda family
            forwardIndex renewalIndex‖ := by
          apply Finset.sum_le_sum
          intro forwardIndex _hforward
          exact norm_tsum_le_tsum_norm (f := fun renewalIndex =>
            finiteEulerPhysicalRawRenewalTailAtom B owner lambda family
              forwardIndex renewalIndex)
            (summable_norm_finiteEulerPhysicalRawRenewalTailAtom B owner lambda
              family forwardIndex)
    _ ≤ ∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
        ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          rawRenewalTailNormConstant owner lambda family *
            (if B < finiteEulerTwoSidedDisplacement family.visiblePrimes
                (pairForwardRenewalIndex family.visiblePrimes
                  (forwardIndex, renewalIndex)) then
                finiteEulerTwoSidedRawWeight family.visiblePrimes
                  (pairForwardRenewalIndex family.visiblePrimes
                    (forwardIndex, renewalIndex))
              else 0) := by
          apply Finset.sum_le_sum
          intro forwardIndex _hforward
          exact (summable_norm_finiteEulerPhysicalRawRenewalTailAtom B owner lambda
                family forwardIndex).tsum_le_tsum
              (fun renewalIndex =>
                norm_finiteEulerPhysicalRawRenewalTailAtom_le_const_ind B owner
                  lambda family forwardIndex renewalIndex)
              (summable_twoSidedRawWeight_tail_fiber B owner lambda family
                forwardIndex)
    _ = rawRenewalTailNormConstant owner lambda family *
        (∑' index : FiniteEulerTwoSidedRenewalIndex family.visiblePrimes,
          if B < finiteEulerTwoSidedDisplacement family.visiblePrimes index then
            finiteEulerTwoSidedRawWeight family.visiblePrimes index
          else 0) := by
          rw [rawRenewalTailWeightDoubleSum_reassoc B
            (rawRenewalTailNormConstant owner lambda family) family.visiblePrimes]

/-- The operator-norm, index-independent constant is nonnegative (a product of
operator norms), which an inequality-chaining step needs to multiply through. -/
theorem rawRenewalTailNormConstant_nonneg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    0 ≤ rawRenewalTailNormConstant owner lambda family := by
  unfold rawRenewalTailNormConstant
  positivity

/-- The whole tail operator decays exponentially in `B`: after the
`rawRenewalTailWeightDoubleSum_reassoc` identification, the tail total
variation `Σ'_{D>B} w` is at most `exp(-B/4)·∏_p primeTwoSidedQuarterMass`, and
multiplying through by the (nonnegative) constant gives
`‖R^(>B)‖ ≤ C0 · exp(-B/4) · ∏`.  This is the decay chain that feeds into the
trace-layer bound for Gate 3U. -/
theorem norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const_exp
    (B : ℝ) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family‖ ≤
      rawRenewalTailNormConstant owner lambda family *
        (Real.exp (-B / 4) *
          (family.visiblePrimes.map primeTwoSidedQuarterMass).prod) := by
  have hstep := norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const B owner
    lambda family
  have hdecay := finiteEulerTwoSidedRawWeight_tail_decay family.visiblePrimes B
  exact le_trans hstep (mul_le_mul_of_nonneg_left hdecay
    (rawRenewalTailNormConstant_nonneg owner lambda family))

end CCM24FiniteSCausalMarkovRawRenewalTailBound
end CCM25Concrete
end Source
end ConnesWeilRH
