import ConnesWeilRH.Dev.C1XiFiniteRectanglePrincipalPart
import ConnesWeilRH.Dev.C1XiFiniteSupportReindex

/-!
# C1XiFiniteRectangleSupportReindex - factor-owned rectangle sums as source spectra

The finite divisor support of one closed-ball xi factorization has already
been embedded into the exact source zero subtype.  This module applies the
same embedding to the strict interior predicate of one rectangle, so a
rectangle readout remains owned by that factorization throughout its
conversion to a finite source spectral sum.

No contour limit, arithmetic readback, explicit-formula equality, or RH claim
is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteRectangleSupportReindex

open Filter
open CC20YoshidaNearZeros
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiFiniteFactor
open C1XiFiniteRectangleBoundary
open C1XiFiniteRectanglePrincipalPart
open C1XiFiniteSupportReindex
open C1XiVerticalFunctional
open scoped BigOperators Topology

/-- The source-zero coordinates from one finite xi factorization that lie
strictly inside a given rectangle.  This is a filtered factor-owned finite
family, not an independently selected zero set. -/
noncomputable def xiClosedBallSourceZerosInsideRectangle
    (c : Complex) (R : Real) (z w : Complex) :
    Finset sourceNontrivialZeroSet := by
  classical
  exact (xiClosedBallSourceZeros c R).filter
    (fun rho => strictlyInsideRectangle z w rho.1)

/-- Membership in the filtered source family records both the finite divisor
owner and strict rectangle inclusion. -/
theorem mem_xiClosedBallSourceZerosInsideRectangle_iff
    (c : Complex) (R : Real) (z w : Complex)
    (rho : sourceNontrivialZeroSet) :
    rho ∈ xiClosedBallSourceZerosInsideRectangle c R z w ↔
      rho.1 ∈ (xiClosedBallDivisor_support_finite c R).toFinset ∧
        strictlyInsideRectangle z w rho.1 := by
  classical
  rw [xiClosedBallSourceZerosInsideRectangle, Finset.mem_filter,
    mem_xiClosedBallSourceZeros_iff]

/-- A factor-owned rectangle sum converts to the same finite source-zero
family before its residues are read as spectral terms. -/
theorem sum_xiClosedBallSourceZerosInsideRectangle_eq_sum_support
    {M : Type*} [AddCommMonoid M] (c : Complex) (R : Real) (z w : Complex)
    (f : Complex -> M) :
    (∑ rho ∈ xiClosedBallSourceZerosInsideRectangle c R z w, f rho.1) =
      ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        @ite (α := M) (strictlyInsideRectangle z w u) (Classical.propDecidable _)
          (f u) 0 := by
  classical
  rw [xiClosedBallSourceZerosInsideRectangle, Finset.sum_filter]
  exact sum_xiClosedBallSourceZeros_eq_sum_support c R
    (fun u => if strictlyInsideRectangle z w u then f u else 0)

/-- One finite factor-owned rectangle readout is exactly minus `2*pi*i` times
the source spectral sum over the same factor owner's zero coordinates strictly
inside the rectangle.  The finite factorization and zero-free boundary remain
explicit hypotheses; this theorem does not take a contour limit. -/
theorem xiRectangleBoundaryIntegral_xiContourKernel_eq_neg_finiteSourceSpectralSum_of_factor_support
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ q : Metric.closedBall c |R|, g q ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    {z w : Complex} (hrectangle : Complex.Rectangle z w ⊆ Metric.ball c |R|)
    (hstandard : standardRectangle z w)
    (hboundary : xiRectangleBoundaryAvoidsZeros z w) :
    xiRectangleBoundaryIntegral (xiContourKernel F) z w =
      -(2 * (Real.pi : Complex) * Complex.I *
        ∑ rho ∈ xiClosedBallSourceZerosInsideRectangle c R z w,
          spectralTerm F rho) := by
  classical
  let support : Finset Complex := (xiClosedBallDivisor_support_finite c R).toFinset
  let factorWeight : Complex -> Complex := fun u =>
    (xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u
  calc
    xiRectangleBoundaryIntegral (xiContourKernel F) z w =
        ∑ u ∈ support,
          if strictlyInsideRectangle z w u then
            -(2 * (Real.pi : Complex) * Complex.I *
              ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u))
          else 0 := by
      simpa only [support] using
        (xiRectangleBoundaryIntegral_xiContourKernel_eq_sum_of_strictlyInside F
          hanalytic hnonzero hfactor hrectangle hstandard hboundary)
    _ = ∑ u ∈ support with strictlyInsideRectangle z w u,
        -(2 * (Real.pi : Complex) * Complex.I * factorWeight u) := by
      simp only [factorWeight]
      rw [Finset.sum_filter]
    _ = -(2 * (Real.pi : Complex) * Complex.I *
        ∑ u ∈ support with strictlyInsideRectangle z w u, factorWeight u) := by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    _ = -(2 * (Real.pi : Complex) * Complex.I *
        ∑ rho ∈ xiClosedBallSourceZerosInsideRectangle c R z w,
          factorWeight rho.1) := by
      congr 2
      symm
      rw [sum_xiClosedBallSourceZerosInsideRectangle_eq_sum_support]
      rw [Finset.sum_filter]
    _ = -(2 * (Real.pi : Complex) * Complex.I *
        ∑ rho ∈ xiClosedBallSourceZerosInsideRectangle c R z w,
          spectralTerm F rho) := by
      congr 2
      apply Finset.sum_congr rfl
      intro rho hrho
      have hfactorMember :=
        (mem_xiClosedBallSourceZerosInsideRectangle_iff c R z w rho).mp hrho
      have hsourceMember : rho ∈ xiClosedBallSourceZeros c R :=
        (mem_xiClosedBallSourceZeros_iff c R rho).mpr hfactorMember.1
      exact factor_weight_eq_spectralTerm_of_mem_sourceZeros F c R rho hsourceMember

end C1XiFiniteRectangleSupportReindex
end Source
end ConnesWeilRH
