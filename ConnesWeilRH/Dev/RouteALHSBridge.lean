import Mathlib.Analysis.InnerProductSpace.Basic
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace RouteALHsGateBridge

open scoped BigOperators ComplexConjugate InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.PositiveTrace

private lemma am_gm_prod (a b : ℝ) :
    a * b ≤ (1 / 2 : ℝ) * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

theorem summable_norm_prod
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {basis : HilbertBasis ι ℂ H}
    (A B : H →L[ℂ] G)
    (hleft : Summable fun i => ‖A (basis i)‖ ^ 2)
    (hright : Summable fun i => ‖B (basis i)‖ ^ 2) :
    Summable fun i => ‖A (basis i)‖ * ‖B (basis i)‖ := by
  refine Summable.of_nonneg_of_le
    (f := fun i : ι => (1 / 2 : ℝ) * (‖A (basis i)‖ ^ 2 + ‖B (basis i)‖ ^ 2))
    (fun i : ι => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun i : ι => am_gm_prod (‖A (basis i)‖) (‖B (basis i)‖))
    ((hleft.add hright).mul_left (1 / 2 : ℝ))

theorem abs_re_infiniteTrace_adjoint_of_le_tsum_prod
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {basis : HilbertBasis ι ℂ H}
    (A B : H →L[ℂ] G)
    (hleft : Summable fun i => ‖A (basis i)‖ ^ 2)
    (hright : Summable fun i => ‖B (basis i)‖ ^ 2) :
    ‖(ordinaryTraceAlong basis (A† ∘L B)).re‖ ≤
      ∑' i, ‖A (basis i)‖ * ‖B (basis i)‖ := by
  classical
  let data : BasisHilbertSchmidtPairData (G := G) basis :=
    ⟨A, B, hleft, hright⟩
  have hprod : A† ∘L B = data.traceProduct := by rfl
  rw [hprod]
  let prd : ι → ℝ := fun i => ‖A (basis i)‖ * ‖B (basis i)‖
  have hprd_sum : Summable prd := summable_norm_prod A B hleft hright
  have hdiag : Summable (fun i : ι =>
      ‖(⟪basis i, data.traceProduct (basis i)⟫_ℂ : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (f := prd)
      (fun i : ι => norm_nonneg _)
      (fun i : ι => by
        rw [data.traceProduct_diagonal i]
        exact norm_inner_le_norm (𝕜 := ℂ) (A (basis i)) (B (basis i)))
      hprd_sum
  have hind : Summable (fun i : ι =>
      ‖(⟪A (basis i), B (basis i)⟫_ℂ : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (f := prd)
      (fun i : ι => norm_nonneg _)
      (fun i : ι => norm_inner_le_norm (𝕜 := ℂ) (A (basis i)) (B (basis i)))
      hprd_sum
  calc
    ‖(ordinaryTraceAlong basis data.traceProduct).re‖ ≤
        ‖ordinaryTraceAlong basis data.traceProduct‖ :=
      Complex.abs_re_le_norm _
    _ = ‖(∑' i : ι, (⟪basis i, data.traceProduct (basis i)⟫_ℂ : ℂ))‖ :=
      rfl
    _ ≤ ∑' i : ι, ‖(⟪basis i, data.traceProduct (basis i)⟫_ℂ : ℂ)‖ :=
      norm_tsum_le_tsum_norm hdiag
    _ = ∑' i : ι, ‖(⟪A (basis i), B (basis i)⟫_ℂ : ℂ)‖ := by
      apply tsum_congr
      intro i
      rw [data.traceProduct_diagonal i]
    _ ≤ ∑' i : ι, prd i := by
      exact hasSum_le
        (fun i : ι => norm_inner_le_norm (𝕜 := ℂ) (A (basis i)) (B (basis i)))
        hind.hasSum
        hprd_sum.hasSum

end RouteALHsGateBridge
end Dev
end Source
end ConnesWeilRH
