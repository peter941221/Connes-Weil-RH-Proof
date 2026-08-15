import ConnesWeilRH.Dev.C1XiFiniteCommonCircle

/-!
# C1XiFiniteSupportReindex - finite xi-support to source-zero reindexing

The finite divisor support owned by one closed-ball xi factorization consists
of exactly source nontrivial zero coordinates.  This module keeps the
conversion as one finite embedding, reads each local divisor multiplicity back
as the analytic xi multiplicity on that same source subtype, and reindexes the
common-circle residue sum accordingly.

No contour limit, arithmetic readback, explicit-formula equality, or RH claim
is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteSupportReindex

open Filter
open CC20YoshidaNearZeros
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiFiniteCommonCircle
open C1XiFiniteFactor
open C1XiVerticalFunctional
open scoped BigOperators Topology

/-- The coordinate embedding from the finite divisor support of one xi
factorization to the exact source zero subtype.  The zero certificate comes
from the same closed-ball divisor owner, not from a fresh choice. -/
noncomputable def xiClosedBallSupportToSourceZero
    (c : Complex) (R : Real) :
    ((xiClosedBallDivisor_support_finite c R).toFinset : Set Complex) ↪
      sourceNontrivialZeroSet := by
  classical
  refine
    { toFun := fun u => ⟨u.1, ?_⟩
      inj' := ?_ }
  · change RHDefinitionBridge.standard.sourceNontrivialZero u.1
    apply (completedRiemannXi_eq_zero_iff_sourceNontrivialZero u.1).mp
    exact
      (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support c R
        ((xiClosedBallDivisor_support_finite c R).mem_toFinset.mp u.2)).2
  · intro u v huv
    exact Subtype.ext
      (congrArg (fun w : sourceNontrivialZeroSet => w.1) huv)

/-- The finite source-zero family represented by the exact divisor support of
one closed-ball xi factorization. -/
noncomputable def xiClosedBallSourceZeros (c : Complex) (R : Real) :
    Finset sourceNontrivialZeroSet := by
  classical
  exact ((xiClosedBallDivisor_support_finite c R).toFinset.attach).map
    (xiClosedBallSupportToSourceZero c R)

/-- A source zero belongs to the factor-owned finite family exactly when its
coordinate belongs to the factor's divisor support. -/
theorem mem_xiClosedBallSourceZeros_iff
    (c : Complex) (R : Real) (rho : sourceNontrivialZeroSet) :
    rho ∈ xiClosedBallSourceZeros c R ↔
      rho.1 ∈ (xiClosedBallDivisor_support_finite c R).toFinset := by
  classical
  constructor
  · intro hrho
    rw [xiClosedBallSourceZeros] at hrho
    rcases Finset.mem_map.mp hrho with ⟨u, _hu, hvalue⟩
    have hcoord : u.1 = rho.1 := by
      exact congrArg Subtype.val hvalue
    rw [← hcoord]
    exact u.2
  · intro hrho
    rw [xiClosedBallSourceZeros]
    let u : ((xiClosedBallDivisor_support_finite c R).toFinset : Set Complex) :=
      ⟨rho.1, hrho⟩
    refine Finset.mem_map.mpr ⟨u, ?_, ?_⟩
    · simp
    · apply Subtype.ext
      rfl

/-- A finite source-zero sum whose summand depends only on the complex
coordinate is exactly the sum over the same factor-owned divisor support. -/
theorem sum_xiClosedBallSourceZeros_eq_sum_support
    {M : Type*} [AddCommMonoid M] (c : Complex) (R : Real) (f : Complex → M) :
    (∑ rho ∈ xiClosedBallSourceZeros c R, f rho.1) =
      ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset, f u := by
  classical
  rw [xiClosedBallSourceZeros, Finset.sum_map]
  calc
    (∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset.attach,
        f (xiClosedBallSupportToSourceZero c R u).1) =
        ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset.attach, f u.1 := by
      apply Finset.sum_congr rfl
      intro u _hu
      rfl
    _ = ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset, f u :=
      Finset.sum_attach _ _

/-- The integer multiplicity held by the finite divisor owner is the analytic
xi multiplicity of the corresponding source zero. -/
theorem xiClosedBallDivisor_cast_eq_xiMultiplicity_of_mem_sourceZeros
    (c : Complex) (R : Real) (rho : sourceNontrivialZeroSet)
    (hrho : rho ∈ xiClosedBallSourceZeros c R) :
    (xiClosedBallDivisor c R rho.1 : Complex) = (xiMultiplicity rho : Complex) := by
  have hsupp : rho.1 ∈ (xiClosedBallDivisor c R).support :=
    (xiClosedBallDivisor_support_finite c R).mem_toFinset.mp
      ((mem_xiClosedBallSourceZeros_iff c R rho).mp hrho)
  have hball : rho.1 ∈ Metric.closedBall c |R| :=
    (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support c R hsupp).1
  have hdiv : xiClosedBallDivisor c R rho.1 = (xiMultiplicity rho : Int) := by
    change MeromorphicOn.divisor completedRiemannXi (Metric.closedBall c |R|) rho.1 =
      (xiMultiplicity rho : Int)
    exact (xiMultiplicity_cast_eq_divisor_of_mem_closedBall rho hball).symm
  rw [hdiv]
  norm_num

/-- The finite-factor residue weight at a reindexed source zero is exactly its
existing one-weight spectral summand. -/
theorem factor_weight_eq_spectralTerm_of_mem_sourceZeros
    (F : CompactLogTest) (c : Complex) (R : Real) (rho : sourceNontrivialZeroSet)
    (hrho : rho ∈ xiClosedBallSourceZeros c R) :
    (xiClosedBallDivisor c R rho.1 : Complex) * centeredLaplaceWeight F rho.1 =
      spectralTerm F rho := by
  rw [xiClosedBallDivisor_cast_eq_xiMultiplicity_of_mem_sourceZeros c R rho hrho]
  exact (spectralTerm_eq_multiplicity_mul_centeredLaplaceWeight F rho).symm

/-- One finite factor-owned residue contribution, with the common-circle
inside test packaged as an ordinary function. -/
noncomputable def xiClosedBallFactorResidueTerm
    (F : CompactLogTest) (c : Complex) (R r : Real) (u : Complex) : Complex := by
  classical
  exact if u ∈ Metric.ball c r then
    -(2 * (Real.pi : Complex) * Complex.I *
      ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u))
  else 0

/-- The corresponding finite source-indexed residue contribution. -/
noncomputable def xiClosedBallSourceResidueTerm
    (F : CompactLogTest) (c : Complex) (r : Real)
    (rho : sourceNontrivialZeroSet) : Complex := by
  classical
  exact if rho.1 ∈ Metric.ball c r then
    -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho)
  else 0

/-- The source-zero coordinates from one finite factorization that lie inside
the common contour circle.  This is a filtered finite family, not an arbitrary
selected zero set. -/
noncomputable def xiClosedBallSourceZerosInside
    (c : Complex) (R r : Real) : Finset sourceNontrivialZeroSet := by
  classical
  exact (xiClosedBallSourceZeros c R).filter (fun rho => rho.1 ∈ Metric.ball c r)

/-- Membership in the finite source family inside the common circle records
both the original factor-owned support and the strict inside condition. -/
theorem mem_xiClosedBallSourceZerosInside_iff
    (c : Complex) (R r : Real) (rho : sourceNontrivialZeroSet) :
    rho ∈ xiClosedBallSourceZerosInside c R r ↔
      rho.1 ∈ (xiClosedBallDivisor_support_finite c R).toFinset ∧
        rho.1 ∈ Metric.ball c r := by
  classical
  rw [xiClosedBallSourceZerosInside, Finset.mem_filter,
    mem_xiClosedBallSourceZeros_iff]

/-- A common factor-owned xi circle reads the finite source-indexed spectral
sum of every xi zero enclosed by that circle.  The finite family remains the
exact ambient divisor support of the same factorization owner. -/
theorem circleIntegral_xiContourKernel_eq_sourceSpectralSum_of_factor_support
    (F : CompactLogTest) {c : Complex} {R r : Real} {g : Complex → Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    (hr : 0 < r)
    (hdisc : Metric.closedBall c r ⊆ Metric.ball c |R|)
    (hboundary : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      u ∉ Metric.sphere c r) :
    (∮ z in C(c, r), xiContourKernel F z) =
      ∑ rho ∈ xiClosedBallSourceZeros c R,
        xiClosedBallSourceResidueTerm F c r rho := by
  classical
  calc
    (∮ z in C(c, r), xiContourKernel F z) =
        ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
          xiClosedBallFactorResidueTerm F c R r u := by
      simpa only [xiClosedBallFactorResidueTerm] using
        (circleIntegral_xiContourKernel_eq_sum_of_factor_support_mem_ball F
          hanalytic hnonzero hfactor hr hdisc hboundary)
    _ = ∑ rho ∈ xiClosedBallSourceZeros c R,
        xiClosedBallFactorResidueTerm F c R r rho.1 := by
      symm
      exact sum_xiClosedBallSourceZeros_eq_sum_support c R (fun u =>
        xiClosedBallFactorResidueTerm F c R r u)
    _ = ∑ rho ∈ xiClosedBallSourceZeros c R,
        xiClosedBallSourceResidueTerm F c r rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      by_cases hins : rho.1 ∈ Metric.ball c r
      · simp only [xiClosedBallFactorResidueTerm, xiClosedBallSourceResidueTerm,
          if_pos hins]
        rw [factor_weight_eq_spectralTerm_of_mem_sourceZeros F c R rho hrho]
      · simp [xiClosedBallFactorResidueTerm, xiClosedBallSourceResidueTerm, hins]

/-- The common factor-owned xi circle is exactly minus `2*pi*i` times the
finite spectral sum over the source-zero coordinates strictly inside it. -/
theorem circleIntegral_xiContourKernel_eq_neg_finiteSourceSpectralSum_of_factor_support
    (F : CompactLogTest) {c : Complex} {R r : Real} {g : Complex → Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    (hr : 0 < r)
    (hdisc : Metric.closedBall c r ⊆ Metric.ball c |R|)
    (hboundary : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      u ∉ Metric.sphere c r) :
    (∮ z in C(c, r), xiContourKernel F z) =
      -(2 * (Real.pi : Complex) * Complex.I *
        ∑ rho ∈ xiClosedBallSourceZerosInside c R r, spectralTerm F rho) := by
  classical
  calc
    (∮ z in C(c, r), xiContourKernel F z) =
        ∑ rho ∈ xiClosedBallSourceZeros c R,
          xiClosedBallSourceResidueTerm F c r rho :=
      circleIntegral_xiContourKernel_eq_sourceSpectralSum_of_factor_support F
        hanalytic hnonzero hfactor hr hdisc hboundary
    _ = ∑ rho ∈ xiClosedBallSourceZeros c R,
        if rho.1 ∈ Metric.ball c r then
          -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho)
        else 0 := by
      rfl
    _ = ∑ rho ∈ xiClosedBallSourceZeros c R with rho.1 ∈ Metric.ball c r,
        -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
      rw [Finset.sum_filter]
    _ = -(2 * (Real.pi : Complex) * Complex.I *
        ∑ rho ∈ xiClosedBallSourceZeros c R with rho.1 ∈ Metric.ball c r,
          spectralTerm F rho) := by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    _ = -(2 * (Real.pi : Complex) * Complex.I *
        ∑ rho ∈ xiClosedBallSourceZerosInside c R r, spectralTerm F rho) := by
      rfl

end C1XiFiniteSupportReindex
end Source
end ConnesWeilRH
