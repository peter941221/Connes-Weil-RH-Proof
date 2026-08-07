import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
namespace ConnesWeilRH.Source.CC20Concrete.PositiveTrace
open scoped ComplexConjugate InnerProduct InnerProductSpace
set_option linter.unusedSectionVars false
variable {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem norm_basis_one (basis : HilbertBasis ι ℂ H) (i : ι) : ‖basis i‖ = 1 :=
  basis.orthonormal.1 i
theorem diag_abs_le_opNorm (basis : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (i : ι) :
    ‖⟪ (basis i), T (basis i)⟫_ℂ‖ ≤ ‖T‖ := by
  have hob : ‖⟪ (basis i), T (basis i)⟫_ℂ‖ ≤ ‖basis i‖ * ‖T (basis i)‖ :=
    norm_inner_le_norm (basis i) (T (basis i))
  have hunit : ‖basis i‖ = 1 := basis.orthonormal.1 i
  have hop : ‖T (basis i)‖ ≤ ‖T‖ * ‖basis i‖ := T.le_opNorm (basis i)
  calc
    ‖⟪ (basis i), T (basis i)⟫_ℂ‖ ≤ ‖basis i‖ * ‖T (basis i)‖ := hob
    _ ≤ ‖basis i‖ * (‖T‖ * ‖basis i‖) := by
      exact mul_le_mul_of_nonneg_left hop (norm_nonneg (basis i))
    _ = ‖T‖ := by rw [hunit]; ring
/-- Route-A bridge: on a finite Hilbert basis, the diagonal-series trace is
bounded by the cardinality times the operator norm.  No nuclear theory. -/
theorem norm_ordinaryTraceAlong_le_card_mul_opNorm (b : HilbertBasis ι ℂ H)
    [Fintype ι] (T : H →L[ℂ] H) :
    ‖ordinaryTraceAlong b T‖ ≤ (Fintype.card ι : ℝ) * ‖T‖ := by
  have hdiag (i : ι) : ‖⟪ (b i), T (b i)⟫_ℂ‖ ≤ ‖T‖ := diag_abs_le_opNorm b T i
  have hcard : (∑ i : ι, ‖T‖) = (Fintype.card ι : ℝ) * ‖T‖ := by
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]
  rw [ordinaryTraceAlong]
  rw [tsum_fintype]
  calc
    ‖(∑ i : ι, ⟪ (b i), T (b i)⟫_ℂ)‖ ≤ (∑ i : ι, ‖⟪ (b i), T (b i)⟫_ℂ‖) := by
      exact norm_sum_le Finset.univ _
    _ ≤ (∑ i : ι, ‖T‖) := by
      exact Finset.sum_le_sum (fun i _ => hdiag i)
    _ = (Fintype.card ι : ℝ) * ‖T‖ := hcard
/-- Real-part corollary used by Gate endpoints. -/
theorem abs_re_ordinaryTraceAlong_le_card_mul_opNorm (I : HilbertBasis ι ℂ H)
    [Fintype ι] (T : H →L[ℂ] H) :
    ‖(ordinaryTraceAlong I T).re‖ ≤ (Fintype.card ι : ℝ) * ‖T‖ := by
  exact le_trans (Complex.abs_re_le_norm (ordinaryTraceAlong I T))
    (norm_ordinaryTraceAlong_le_card_mul_opNorm I T)

/-- Abstract finite-carrier Gate production: on ANY finite Hilbert basis, a
supplied operator-norm bound ||T|| <= M yields the |Re trace| bound the Gate
consumer wants: |Re Tr (along basis) T| <= (card basis) * M.  Route-A closing
lemma: pair with the real tail operator-norm decay theorem to close a finite
carrier Gate. -/
theorem finiteGate_AbstractGate_of_norm_le (b : HilbertBasis x ℂ H)
    [Fintype x] (T : H →L[ℂ] H) (M : ℝ) (hM : ‖T‖ ≤ M) :
    ‖(ordinaryTraceAlong b T).re‖ ≤ (Fintype.card x : ℝ) * M := by
  have hb := abs_re_ordinaryTraceAlong_le_card_mul_opNorm b T
  exact le_trans hb (mul_le_mul_of_nonneg_left hM (by positivity))

end ConnesWeilRH.Source.CC20Concrete.PositiveTrace
