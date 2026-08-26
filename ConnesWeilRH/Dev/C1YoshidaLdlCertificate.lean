import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Yoshida exact-rational LDLᵀ coercivity engine

Yoshida 1992 (§6, "A numerical example") closes the endpoint sign for the
window `a = log 2 / 2` by an exact elimination on the Gram matrix of the
sine basis: the odd part is a 10x10 real symmetric matrix and the even part
a 200x200 one, and the elimination is tracked in strict rational interval
arithmetic.  The engine behind both is the classical LDLᵀ statement:

```text
U = L * D * Lᵀ,  L unit lower triangular,  D diagonal with positive entries
      ⟹  x ⬝ᵥ (U *ᵥ x) = ∑ i, d i * (Lᵀ *ᵥ x) i ^ 2 > 0   for x ≠ 0
```

This leaf formalizes that engine over `Fin n` together with an explicit
3x3 synthetic rational witness.  The witness proves non-vacuity of the
pipeline; transcribing Yoshida's actual digamma interval data for the 10x10
odd matrix remains future work and is NOT claimed here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1YoshidaLdlCertificate

open Matrix

/-- The reading identity behind exact LDLᵀ elimination: the quadratic form
of `L * diagonal d * Lᵀ` is the `d`-weighted sum of squares of `Lᵀ *ᵥ x`.
This is the exact statement Yoshida tracks through the elimination steps. -/
theorem ldlt_dotProduct_eq {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((L * diagonal d * Lᵀ) *ᵥ x) = ∑ i, d i * (Lᵀ *ᵥ x) i ^ 2 := by
  have h1 : (L * diagonal d * Lᵀ) *ᵥ x
      = L *ᵥ (diagonal d *ᵥ (Lᵀ *ᵥ x)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A unit lower triangular matrix: diagonal `1`, strict upper part `0`. -/
def IsUnitLowerTriangular {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, L i i = 1) ∧ ∀ i j, i < j → L i j = 0

/-- The transpose of a unit lower triangular matrix acts injectively: if
`z` is nonzero and `i₀` is its largest nonzero coordinate, then coordinate
`i₀` of `Lᵀ *ᵥ z` is `z i₀` itself, because every `j > i₀` contributes
`z j = 0` and every `j < i₀` contributes `L j i₀ = 0`.  This is the forward
substitution step of exact elimination. -/
theorem unitLowerTriangular_transpose_mulVec_injective {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : IsUnitLowerTriangular L) :
    Function.Injective (fun x => Lᵀ *ᵥ x) := by
  intro x y hxy
  by_contra hne
  have hxy' : Lᵀ *ᵥ x = Lᵀ *ᵥ y := hxy
  have hz0 : Lᵀ *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy', sub_self]
  have hzne : (x - y) ≠ 0 := sub_ne_zero_of_ne hne
  obtain ⟨i₁, hi₁⟩ : ∃ i, (x - y) i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hzne (funext hcon)
  have hex : ∃ i₀, (x - y) i₀ ≠ 0 ∧ ∀ j, i₀ < j → (x - y) j = 0 := by
    have hsne : (Finset.univ.filter fun i => (x - y) i ≠ 0).Nonempty :=
      ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₁⟩⟩
    refine ⟨(Finset.univ.filter fun i => (x - y) i ≠ 0).max' hsne, ?_, ?_⟩
    · have hmem := Finset.max'_mem _ hsne
      simpa [Finset.mem_filter] using hmem
    · intro j hj
      by_contra hzj
      exact absurd
        (Finset.le_max' _ j
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj⟩))
        (not_le.2 hj)
  obtain ⟨i₀, hi₀, hmax⟩ := hex
  have hcomp : (Lᵀ *ᵥ (x - y)) i₀ = (x - y) i₀ := by
    have hsum : ∑ j ∈ Finset.univ, Lᵀ i₀ j * (x - y) j
        = Lᵀ i₀ i₀ * (x - y) i₀ := by
      refine Finset.sum_eq_single i₀ ?_ ?_
      · intro j _hj hji
        rcases lt_trichotomy j i₀ with hlt | heq | hgt
        · rw [Matrix.transpose_apply, hL.2 j i₀ hlt, zero_mul]
        · exact absurd heq hji
        · rw [hmax j hgt, mul_zero]
      · intro hmem
        exact (hmem (Finset.mem_univ _)).elim
    rw [Matrix.mulVec, dotProduct, hsum]
    rw [show Lᵀ i₀ i₀ = 1 from by
        rw [Matrix.transpose_apply]
        exact hL.1 i₀, one_mul]
  rw [hz0, Pi.zero_apply] at hcomp
  exact hi₀ hcomp.symm

/-- The main LDLᵀ coercivity engine: an exact factorization `U = L * D * Lᵀ`
with `L` unit lower triangular and `d` positive on the diagonal makes `U`
positive definite.  Yoshida's §6 elimination produces exactly such a
factorization with rational interval data. -/
theorem posDef_of_ldlt {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (hL : IsUnitLowerTriangular L) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    (L * diagonal d * Lᵀ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · have hdH : (diagonal d).IsHermitian :=
      isHermitian_diagonal_of_self_adjoint _ (funext fun _ => rfl)
    have hgen := Matrix.isHermitian_conjTranspose_mul_mul (Lᵀ) hdH
    have hEq : (Lᵀ)ᴴ * diagonal d * Lᵀ = L * diagonal d * Lᵀ := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_transpose]
    rw [hEq] at hgen
    exact hgen
  · intro x hx
    show 0 < x ⬝ᵥ ((L * diagonal d * Lᵀ) *ᵥ x)
    rw [ldlt_dotProduct_eq L d x]
    rcases eq_or_ne (Lᵀ *ᵥ x) 0 with hy | hy
    · exact absurd
        (unitLowerTriangular_transpose_mulVec_injective L hL
          (show (fun x => Lᵀ *ᵥ x) x = (fun x => Lᵀ *ᵥ x) 0 from by
            simp only [Matrix.mulVec_zero]
            exact hy))
        hx
    · refine Finset.sum_pos' ?_ ?_
      · intro i _
        exact mul_nonneg (hd i).le (sq_nonneg _)
      · obtain ⟨i₂, hi₂⟩ : ∃ i, (Lᵀ *ᵥ x) i ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          exact hy (funext hcon)
        exact ⟨i₂, Finset.mem_univ _,
          mul_pos (hd i₂) (sq_pos_of_ne_zero hi₂)⟩

/-! ## An explicit 3x3 synthetic rational witness

The following factorization is synthetic (it is not transcribed from
Yoshida's digamma data); it proves the pipeline is non-vacuous and produces
the first structurally nonzero Yoshida-shape certificate.  Transcribing the
actual 10x10 odd / 200x200 even interval data remains future work.
-/

/-- Synthetic unit lower triangular factor with rational entries, written
as an explicit entry function so that triangularity is a `simp` fact. -/
noncomputable def witnessL : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if i < j then 0
    else if i = j then 1
    else if (i, j) = (1, 0) then 1 / 2
    else if (i, j) = (2, 0) then 1 / 3
    else if (i, j) = (2, 1) then 1 / 4
    else 0

/-- Synthetic positive diagonal. -/
def witnessD : Fin 3 → ℝ :=
  ![4, 9, 1]

theorem witnessL_isUnitLowerTriangular : IsUnitLowerTriangular witnessL := by
  refine ⟨?_, ?_⟩
  · intro i
    simp [witnessL]
  · intro i j h
    simp [witnessL, h]

theorem witnessD_pos : ∀ i, 0 < witnessD i := by
  intro i
  fin_cases i <;> norm_num [witnessD]

/-- The exact rational matrix carried by the synthetic factorization. -/
theorem witness_matrix_eq :
    witnessL * diagonal witnessD * witnessLᵀ =
      !![4, 2, 4 / 3; 2, 10, 35 / 12; 4 / 3, 35 / 12, 289 / 144] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessL, witnessD, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.transpose_apply, Matrix.vecMul_diagonal, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.of_apply] <;>
    norm_num

/-- The first structurally nonzero Yoshida-shape certificate: the synthetic
factorization makes its Gram matrix positive definite. -/
theorem witness_posDef : (witnessL * diagonal witnessD * witnessLᵀ).PosDef :=
  posDef_of_ldlt witnessL witnessL_isUnitLowerTriangular witnessD witnessD_pos

theorem witness_dotProduct_pos {x : Fin 3 → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ ((witnessL * diagonal witnessD * witnessLᵀ) *ᵥ x) :=
  witness_posDef.dotProduct_mulVec_pos hx

end C1YoshidaLdlCertificate
end Source
end ConnesWeilRH
