/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Trace-class legality for a smoothed global-log crossing

The rank-one smoothing is a deliberately small first producer.  It keeps the
crossing operator and the smoothing vectors on one object, proves the actual
Hilbert-Schmidt summability, and stores no trace value.  A later convolution
owner can replace the rank-one smoother after its kernel-energy estimate is
available.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open scoped InnerProduct InnerProductSpace

noncomputable def cc20SmoothedCrossing (b : ℝ)
    (k h : cc20GlobalLogCrossingL2) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20SingleCrossingOperator b ∘L InnerProductSpace.rankOne ℂ k h

theorem cc20SmoothedCrossing_apply (b : ℝ)
    (k h u : cc20GlobalLogCrossingL2) :
    cc20SmoothedCrossing b k h u =
      ⟪h, u⟫_ℂ • cc20SingleCrossingOperator b k := by
  simp [cc20SmoothedCrossing, InnerProductSpace.rankOne_apply]

theorem cc20SmoothedCrossing_eq_rankOne (b : ℝ)
    (k h : cc20GlobalLogCrossingL2) :
    cc20SmoothedCrossing b k h =
      InnerProductSpace.rankOne ℂ (cc20SingleCrossingOperator b k) h := by
  simp [cc20SmoothedCrossing, InnerProductSpace.comp_rankOne]

theorem cc20SmoothedCrossing_basis_normSq_summable
    (b : ℝ) (k h : cc20GlobalLogCrossingL2)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ cc20GlobalLogCrossingL2) :
    Summable (fun i => ‖cc20SmoothedCrossing b k h (basis i)‖ ^ 2) := by
  have hBessel : Summable (fun i => ‖⟪h, basis i⟫_ℂ‖ ^ 2) := by
    refine summable_of_sum_le (c := ‖h‖ ^ 2) (fun i => sq_nonneg _) ?_
    intro s
    simpa only [norm_inner_symm] using
      basis.orthonormal.sum_inner_products_le h
  have hnorm (i : ι) :
      ‖cc20SmoothedCrossing b k h (basis i)‖ ^ 2 =
        (‖cc20SingleCrossingOperator b k‖ ^ 2) *
          ‖⟪h, basis i⟫_ℂ‖ ^ 2 := by
    rw [cc20SmoothedCrossing_apply, norm_smul]
    rw [mul_pow]
    ring
  simpa only [hnorm] using hBessel.mul_left (‖cc20SingleCrossingOperator b k‖ ^ 2)

/-- The ordinary trace of the first-stage rank-one smoothing is its rank-one
pairing. This is not the convolution-square diagonal scalar. -/
theorem cc20SmoothedCrossing_ordinaryTraceAlong
    (b : ℝ) (k h : cc20GlobalLogCrossingL2)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.ordinaryTraceAlong basis (cc20SmoothedCrossing b k h) =
      ⟪h, cc20SingleCrossingOperator b k⟫_ℂ := by
  rw [PositiveTrace.ordinaryTraceAlong]
  simp_rw [cc20SmoothedCrossing_apply, inner_smul_right]
  exact basis.tsum_inner_mul_inner h (cc20SingleCrossingOperator b k)

noncomputable def cc20SmoothedCrossingBasisHilbertSchmidtData
    (b : ℝ) (k h : cc20GlobalLogCrossingL2)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.BasisHilbertSchmidtData basis where
  operator := cc20SmoothedCrossing b k h
  summable_normSq := cc20SmoothedCrossing_basis_normSq_summable b k h basis

theorem cc20SmoothedCrossing_positiveComposition_traceClass
    (b : ℝ) (k h : cc20GlobalLogCrossingL2)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.IsTraceClassAlong basis
      (cc20SmoothedCrossingBasisHilbertSchmidtData b k h basis).positiveComposition :=
  PositiveTrace.BasisHilbertSchmidtData.positiveComposition_isTraceClassAlong
    (cc20SmoothedCrossingBasisHilbertSchmidtData b k h basis)

theorem cc20SmoothedCrossing_positiveComposition_trace_nonnegative
    (b : ℝ) (k h : cc20GlobalLogCrossingL2)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ cc20GlobalLogCrossingL2) :
    0 ≤ (PositiveTrace.ordinaryTraceAlong basis
      (cc20SmoothedCrossingBasisHilbertSchmidtData b k h basis).positiveComposition).re :=
  PositiveTrace.BasisHilbertSchmidtData.ordinaryTrace_positiveComposition_re_nonnegative
    (cc20SmoothedCrossingBasisHilbertSchmidtData b k h basis)

/-- The canonical first-stage producer uses the same source test on both sides
of the rank-one smoothing.  In particular, it cannot mix unrelated `L2`
witnesses for the crossing input and the trace coefficient. -/
noncomputable def cc20SourceTestSmoothedCrossing
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20SmoothedCrossing b (cc20LogPullbackLp p) (cc20LogPullbackLp p)

theorem cc20SourceTestSmoothedCrossing_eq_rankOne
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (b : ℝ) :
    cc20SourceTestSmoothedCrossing p b =
      InnerProductSpace.rankOne ℂ
        (cc20SingleCrossingOperator b (cc20LogPullbackLp p))
        (cc20LogPullbackLp p) := by
  exact cc20SmoothedCrossing_eq_rankOne b _ _

theorem cc20SourceTestSmoothedCrossing_ordinaryTraceAlong
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (b : ℝ) {ι : Type*}
    (basis : HilbertBasis ι ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.ordinaryTraceAlong basis
        (cc20SourceTestSmoothedCrossing p b) =
      ⟪cc20LogPullbackLp p,
        cc20SingleCrossingOperator b (cc20LogPullbackLp p)⟫_ℂ := by
  exact cc20SmoothedCrossing_ordinaryTraceAlong b _ _ basis

theorem cc20SourceTestSmoothedCrossing_positiveComposition_traceClass
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (b : ℝ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.IsTraceClassAlong basis
      (cc20SmoothedCrossingBasisHilbertSchmidtData b
        (cc20LogPullbackLp p) (cc20LogPullbackLp p) basis).positiveComposition :=
  cc20SmoothedCrossing_positiveComposition_traceClass b _ _ basis

theorem cc20SourceTestSmoothedCrossing_positiveComposition_trace_nonnegative
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (b : ℝ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ cc20GlobalLogCrossingL2) :
    0 ≤ (PositiveTrace.ordinaryTraceAlong basis
      (cc20SmoothedCrossingBasisHilbertSchmidtData b
        (cc20LogPullbackLp p) (cc20LogPullbackLp p) basis).positiveComposition).re :=
  cc20SmoothedCrossing_positiveComposition_trace_nonnegative b _ _ basis

end CC20Concrete
end Source
end ConnesWeilRH
