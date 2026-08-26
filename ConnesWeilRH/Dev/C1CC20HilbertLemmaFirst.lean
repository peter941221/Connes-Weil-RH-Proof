import ConnesWeilRH.Dev.C1CC20FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# CC20 Lemma `first` on a complex Hilbert space

CC20, `weil-compo.tex`, Lemma `first`, reduces its Hilbert-space quadratic
form to one Hermitian two-dimensional block and a nonnegative orthogonal
remainder.  This file supplies the complex block and the exact orthogonal
coordinate bookkeeping.  Numerical spectral enclosures remain separate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20HilbertLemmaFirst

/-- A Hermitian two-by-two quadratic form with real diagonal entries. -/
noncomputable def cc20ComplexHermitianForm
    (p r : ℝ) (q x y : ℂ) : ℝ :=
  p * Complex.normSq x + 2 * (x * star (q * y)).re +
    r * Complex.normSq y

/-- A positive diagonal and nonnegative determinant make the complex
Hermitian two-by-two form nonnegative. -/
theorem cc20ComplexHermitianForm_nonneg
    {p r : ℝ} {q : ℂ}
    (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hdet : Complex.normSq q ≤ p * r) :
    ∀ x y : ℂ, 0 ≤ cc20ComplexHermitianForm p r q x y := by
  intro x y
  by_cases hp0 : p = 0
  · have hqnorm : Complex.normSq q = 0 := by
      have hqnonneg := Complex.normSq_nonneg q
      nlinarith
    have hq : q = 0 := Complex.normSq_eq_zero.mp hqnorm
    simp only [cc20ComplexHermitianForm, hp0, zero_mul, hq, zero_mul,
      star_zero, mul_zero, Complex.zero_re, mul_zero, zero_add]
    exact mul_nonneg hr (Complex.normSq_nonneg y)
  · have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hscaled :
        0 ≤ p * cc20ComplexHermitianForm p r q x y := by
      calc
        0 ≤ Complex.normSq ((p : ℂ) * x + q * y) +
            (p * r - Complex.normSq q) * Complex.normSq y :=
          add_nonneg (Complex.normSq_nonneg _)
            (mul_nonneg (sub_nonneg.mpr hdet) (Complex.normSq_nonneg y))
        _ = p * cc20ComplexHermitianForm p r q x y := by
          simp only [cc20ComplexHermitianForm, Complex.normSq_apply,
            Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
            Complex.conj_re, Complex.conj_im]
          ring
    exact nonneg_of_mul_nonneg_right hscaled hppos

/-- Shifted form: positivity after subtracting `epsilon` from both diagonal
entries gives an `epsilon` lower bound against the coordinate norm. -/
theorem cc20ComplexHermitianForm_ge_epsilon
    {p r epsilon : ℝ} {q : ℂ}
    (hp : 0 ≤ p - epsilon) (hr : 0 ≤ r - epsilon)
    (hdet : Complex.normSq q ≤ (p - epsilon) * (r - epsilon)) :
    ∀ x y : ℂ,
      epsilon * (Complex.normSq x + Complex.normSq y) ≤
        cc20ComplexHermitianForm p r q x y := by
  intro x y
  have hnonneg := cc20ComplexHermitianForm_nonneg hp hr hdet x y
  unfold cc20ComplexHermitianForm at hnonneg ⊢
  linarith

/-- Expanding one rank-one square gives exactly the Hermitian block used in
CC20 Lemma `first`. -/
theorem cc20RankOneSquare_eq_complexHermitianForm
    (a b c beta : ℝ) (alpha x y : ℂ) :
    -b * Complex.normSq x +
        a * Complex.normSq (star alpha * x + (beta : ℂ) * y) +
        c * Complex.normSq y =
      cc20ComplexHermitianForm
        (a * Complex.normSq alpha - b)
        (a * beta ^ 2 + c)
        ((a * beta : ℝ) * alpha) x y := by
  simp only [cc20ComplexHermitianForm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-! ### Orthogonal coordinates in the ambient Hilbert space -/

/-- Remove the component of `xi` along `phi`. -/
noncomputable def cc20OrthogonalPart
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (phi xi : H) : H :=
  xi - inner ℂ phi xi • phi

theorem inner_cc20OrthogonalPart_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {phi : H} (hphi : ‖phi‖ = 1) (xi : H) :
    inner ℂ phi (cc20OrthogonalPart phi xi) = 0 := by
  rw [cc20OrthogonalPart, inner_sub_right, inner_smul_right,
    inner_self_eq_one_of_norm_eq_one hphi]
  simp

/-- Pythagoras for a unit vector and its explicitly defined orthogonal
remainder. -/
theorem norm_sq_eq_normSq_inner_add_orthogonalPart
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {phi : H} (hphi : ‖phi‖ = 1) (xi : H) :
    ‖xi‖ ^ 2 = Complex.normSq (inner ℂ phi xi) +
      ‖cc20OrthogonalPart phi xi‖ ^ 2 := by
  have horth :
      inner ℂ (inner ℂ phi xi • phi) (cc20OrthogonalPart phi xi) = 0 := by
    rw [inner_smul_left]
    simp [inner_cc20OrthogonalPart_eq_zero hphi]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (inner ℂ phi xi • phi) (cc20OrthogonalPart phi xi) horth
  have hsum :
      inner ℂ phi xi • phi + cc20OrthogonalPart phi xi = xi := by
    simp [cc20OrthogonalPart]
  rw [hsum] at hpyth
  simpa [pow_two, norm_smul, hphi, Complex.normSq_eq_norm_sq] using hpyth

/-- An explicit orthonormal pair spanning the exceptional two-dimensional
block in CC20 Lemma `first`. -/
structure CC20OrthonormalFrame
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  phi : H
  chi : H
  phi_unit : ‖phi‖ = 1
  chi_unit : ‖chi‖ = 1
  phi_chi_inner : inner ℂ phi chi = 0

/-- The ambient Hilbert-space form from CC20 Lemma `first`.  The first term
is the exceptional eigendirection, the second is the rank-one repair, and
the third is the spectral-gap contribution on `phiᵖ`. -/
noncomputable def cc20LemmaFirstHilbertForm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (frame : CC20OrthonormalFrame H) (psi : H)
    (a b c : ℝ) (xi : H) : ℝ :=
  -b * Complex.normSq (inner ℂ frame.phi xi) +
    a * Complex.normSq (inner ℂ psi xi) +
    c * ‖cc20OrthogonalPart frame.phi xi‖ ^ 2

/-- The Hilbert-space form of CC20 Lemma `first`.

`psi = alpha * phi + beta * chi` locates the rank-one repair vector in the
exceptional two-plane.  The three shifted matrix hypotheses certify that
plane, while `epsilon ≤ c` controls the orthogonal remainder. -/
theorem cc20LemmaFirstHilbertForm_ge_epsilon
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (frame : CC20OrthonormalFrame H)
    {psi : H} {alpha : ℂ} {a b c beta epsilon : ℝ}
    (hpsi : psi = alpha • frame.phi + (beta : ℂ) • frame.chi)
    (hp : 0 ≤ a * Complex.normSq alpha - b - epsilon)
    (hr : 0 ≤ a * beta ^ 2 + c - epsilon)
    (hdet : Complex.normSq ((a * beta : ℝ) * alpha) ≤
      (a * Complex.normSq alpha - b - epsilon) *
        (a * beta ^ 2 + c - epsilon))
    (hepsilon_le_c : epsilon ≤ c) :
    ∀ xi : H,
      epsilon * ‖xi‖ ^ 2 ≤
        cc20LemmaFirstHilbertForm frame psi a b c xi := by
  intro xi
  let x : ℂ := inner ℂ frame.phi xi
  let u : H := cc20OrthogonalPart frame.phi xi
  let y : ℂ := inner ℂ frame.chi xi
  let z : H := cc20OrthogonalPart frame.chi u
  have hchi_phi : inner ℂ frame.chi frame.phi = 0 :=
    inner_eq_zero_symm.mp frame.phi_chi_inner
  have hyu : inner ℂ frame.chi u = y := by
    dsimp only [u, y]
    rw [cc20OrthogonalPart, inner_sub_right, inner_smul_right, hchi_phi]
    simp
  have hnorm_phi :
      ‖xi‖ ^ 2 = Complex.normSq x + ‖u‖ ^ 2 := by
    simpa only [x, u] using
      norm_sq_eq_normSq_inner_add_orthogonalPart frame.phi_unit xi
  have hnorm_chi :
      ‖u‖ ^ 2 = Complex.normSq y + ‖z‖ ^ 2 := by
    have h := norm_sq_eq_normSq_inner_add_orthogonalPart frame.chi_unit u
    simpa only [z, hyu] using h
  have hnorm_total :
      ‖xi‖ ^ 2 = Complex.normSq x + Complex.normSq y + ‖z‖ ^ 2 := by
    linarith [hnorm_phi, hnorm_chi]
  have hpsi_inner :
      inner ℂ psi xi = star alpha * x + (beta : ℂ) * y := by
    rw [hpsi, inner_add_left, inner_smul_left, inner_smul_left]
    simp only [x, y, Complex.star_def, Complex.conj_ofReal]
  have hform :
      cc20LemmaFirstHilbertForm frame psi a b c xi =
        cc20ComplexHermitianForm
            (a * Complex.normSq alpha - b)
            (a * beta ^ 2 + c)
            ((a * beta : ℝ) * alpha) x y +
          c * ‖z‖ ^ 2 := by
    change -b * Complex.normSq x +
        a * Complex.normSq (inner ℂ psi xi) + c * ‖u‖ ^ 2 = _
    rw [hpsi_inner, hnorm_chi,
      ← cc20RankOneSquare_eq_complexHermitianForm a b c beta alpha x y]
    ring
  have hblock :
      epsilon * (Complex.normSq x + Complex.normSq y) ≤
        cc20ComplexHermitianForm
          (a * Complex.normSq alpha - b)
          (a * beta ^ 2 + c)
          ((a * beta : ℝ) * alpha) x y :=
    cc20ComplexHermitianForm_ge_epsilon hp hr hdet x y
  have htail : epsilon * ‖z‖ ^ 2 ≤ c * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hepsilon_le_c (sq_nonneg _)
  rw [hform, hnorm_total]
  linarith

end C1CC20HilbertLemmaFirst
end Source
end ConnesWeilRH
