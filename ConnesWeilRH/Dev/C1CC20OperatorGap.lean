import ConnesWeilRH.Dev.C1CC20EndpointCertificateData
import ConnesWeilRH.Dev.C1CC20HilbertLemmaFirst
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# CC20 operator-gap data: the abstract skeleton of Lemma `second`

CC20 (arXiv:2006.13771, `weil-compo.tex` Lemma `second`) derives the rank-one
bound `⟨ξ | nf_I ξ⟩ ≤ γ |⟨ξ₀ | ξ⟩|²` with `γ ∼ 2.94355` from exactly two
analytic inputs:

```text
(H1)  ⟨ξ|(id − T)ξ⟩ + a·|⟨ξ₀|ξ⟩|² ≥ ε₂·‖ξ‖²     (Lemma `first` applied to T:
      b = λ_max − 1 ∼ 0.05158, c = 1 − λ₂ > 0.227784, a ∼ 0.064,
      ε₂ ∼ 0.00441)
(H2)  ‖kf_I − T‖ ≤ ε₁,  ε₁ ≃ 0.00122 < ε₂       (equation `spectral0`)
```

Everything between those inputs and the conclusion is scalar algebra, done
twice below: coercivity transfer through the operator gap, then the sign
flip by multiplication with `−2ε'(1₊)`.  The constant is

```text
gamma := 2 * ε'(1₊) * a.
```

Both analytic inputs remain caller premises; this leaf does not prove the
spectral estimates themselves.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20OperatorGap

open C1CC20EndpointCertificateData
open C1CC20HilbertLemmaFirst

/-! ### The genuine operator-norm input -/

/-- The real quadratic form of a bounded operator on a complex Hilbert space. -/
def cc20RealQuadraticForm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (xi : H) : ℝ :=
  (inner ℂ xi (A xi)).re

/-- The form used in CC20 Lemma `second`: `Re <xi, (id - A) xi>`. -/
def cc20DefectQuadraticForm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (xi : H) : ℝ :=
  (inner ℂ xi (xi - A xi)).re

theorem cc20DefectQuadraticForm_eq_norm_sq_sub_realQuadraticForm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (xi : H) :
    cc20DefectQuadraticForm A xi =
      ‖xi‖ ^ 2 - cc20RealQuadraticForm A xi := by
  unfold cc20DefectQuadraticForm cc20RealQuadraticForm
  have hself : (inner ℂ xi xi).re = ‖xi‖ ^ 2 := by
    have h := inner_self_eq_norm_mul_norm (𝕜 := ℂ) xi
    change (inner ℂ xi xi).re = ‖xi‖ * ‖xi‖ at h
    simpa only [pow_two] using h
  rw [inner_sub_right, Complex.sub_re, hself]

/-- Read the quadratic form of an operator from CC20's exceptional
eigenvector decomposition `T = lambdaMax |phi><phi| + R`.  The residual is
required to preserve `phiᵖ`; no self-adjointness is hidden in this theorem. -/
theorem cc20RealQuadraticForm_eq_of_spectralDecomposition
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (frame : CC20OrthonormalFrame H)
    (T R : H →L[ℂ] H) (lambdaMax : ℝ)
    (hT : ∀ xi : H,
      T xi = (lambdaMax : ℂ) •
          (inner ℂ frame.phi xi • frame.phi) +
        R (cc20OrthogonalPart frame.phi xi))
    (hR_invariant : ∀ u : H, inner ℂ frame.phi u = 0 →
      inner ℂ frame.phi (R u) = 0) :
    ∀ xi : H,
      cc20RealQuadraticForm T xi =
        lambdaMax * Complex.normSq (inner ℂ frame.phi xi) +
          cc20RealQuadraticForm R (cc20OrthogonalPart frame.phi xi) := by
  intro xi
  let x : ℂ := inner ℂ frame.phi xi
  let u : H := cc20OrthogonalPart frame.phi xi
  have hphi_u : inner ℂ frame.phi u = 0 := by
    simpa only [u] using
      inner_cc20OrthogonalPart_eq_zero frame.phi_unit xi
  have hu_phi : inner ℂ u frame.phi = 0 :=
    inner_eq_zero_symm.mp hphi_u
  have hphi_Ru : inner ℂ frame.phi (R u) = 0 :=
    hR_invariant u hphi_u
  have hTxi :
      T xi = (lambdaMax : ℂ) • (x • frame.phi) + R u := by
    simpa only [x, u] using hT xi
  have hxi : xi = x • frame.phi + u := by
    simp [x, u, cc20OrthogonalPart]
  change cc20RealQuadraticForm T xi =
    lambdaMax * Complex.normSq x + cc20RealQuadraticForm R u
  unfold cc20RealQuadraticForm
  rw [hTxi, hxi]
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hu_phi, hphi_Ru,
    inner_self_eq_one_of_norm_eq_one frame.phi_unit,
    mul_zero, add_zero, zero_add]
  simp only [Complex.normSq_apply, Complex.add_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  norm_num

/-- CC20's exceptional-eigenvalue decomposition and an upper spectral bound
on the orthogonal residual imply the exact defect-form lower bound used in
Lemma `first`.

This replaces the scalar `spectral2`/`spectral3` shadow by three operator-level
facts: the decomposition of `T`, invariance of `phi`'s orthogonal complement,
and the Rayleigh-quotient upper bound for `R` on that complement. -/
theorem cc20DefectQuadraticForm_ge_of_spectralDecomposition
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (frame : CC20OrthonormalFrame H)
    (T R : H →L[ℂ] H) (lambdaMax lambda2 : ℝ)
    (hT : ∀ xi : H,
      T xi = (lambdaMax : ℂ) •
          (inner ℂ frame.phi xi • frame.phi) +
        R (cc20OrthogonalPart frame.phi xi))
    (hR_invariant : ∀ u : H, inner ℂ frame.phi u = 0 →
      inner ℂ frame.phi (R u) = 0)
    (hR_upper : ∀ u : H, inner ℂ frame.phi u = 0 →
      cc20RealQuadraticForm R u ≤ lambda2 * ‖u‖ ^ 2) :
    ∀ xi : H,
      -(lambdaMax - 1) * Complex.normSq (inner ℂ frame.phi xi) +
          (1 - lambda2) * ‖cc20OrthogonalPart frame.phi xi‖ ^ 2 ≤
        cc20DefectQuadraticForm T xi := by
  intro xi
  let u : H := cc20OrthogonalPart frame.phi xi
  have hphi_u : inner ℂ frame.phi u = 0 := by
    simpa only [u] using
      inner_cc20OrthogonalPart_eq_zero frame.phi_unit xi
  have hnorm :
      ‖xi‖ ^ 2 = Complex.normSq (inner ℂ frame.phi xi) + ‖u‖ ^ 2 := by
    simpa only [u] using
      norm_sq_eq_normSq_inner_add_orthogonalPart frame.phi_unit xi
  have hquadratic :=
    cc20RealQuadraticForm_eq_of_spectralDecomposition
      frame T R lambdaMax hT hR_invariant xi
  have hupper := hR_upper u hphi_u
  rw [cc20DefectQuadraticForm_eq_norm_sq_sub_realQuadraticForm]
  change -(lambdaMax - 1) * Complex.normSq (inner ℂ frame.phi xi) +
      (1 - lambda2) * ‖u‖ ^ 2 ≤
    ‖xi‖ ^ 2 - cc20RealQuadraticForm T xi
  calc
    -(lambdaMax - 1) * Complex.normSq (inner ℂ frame.phi xi) +
          (1 - lambda2) * ‖u‖ ^ 2 =
        (Complex.normSq (inner ℂ frame.phi xi) + ‖u‖ ^ 2) -
          (lambdaMax * Complex.normSq (inner ℂ frame.phi xi) +
            lambda2 * ‖u‖ ^ 2) := by ring
    _ ≤ (Complex.normSq (inner ℂ frame.phi xi) + ‖u‖ ^ 2) -
          (lambdaMax * Complex.normSq (inner ℂ frame.phi xi) +
            cc20RealQuadraticForm R u) := by
      linarith
    _ = ‖xi‖ ^ 2 - cc20RealQuadraticForm T xi := by
      rw [hnorm, hquadratic]

/-- Operator norm controls the change of the associated quadratic form.
This is the Cauchy--Schwarz step hidden between equation `spectral0` and
Lemma `second` in CC20.  Self-adjointness is unnecessary because only the
real part is used. -/
theorem abs_cc20RealQuadraticForm_sub_le_opNorm_mul_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K T : H →L[ℂ] H) (xi : H) :
    |cc20RealQuadraticForm K xi - cc20RealQuadraticForm T xi| ≤
      ‖K - T‖ * ‖xi‖ ^ 2 := by
  calc
    |cc20RealQuadraticForm K xi - cc20RealQuadraticForm T xi| =
        |(inner ℂ xi ((K - T) xi)).re| := by
      simp only [cc20RealQuadraticForm, ContinuousLinearMap.sub_apply,
        inner_sub_right, Complex.sub_re]
    _ ≤ ‖inner ℂ xi ((K - T) xi)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖xi‖ * ‖(K - T) xi‖ := norm_inner_le_norm _ _
    _ ≤ ‖xi‖ * (‖K - T‖ * ‖xi‖) :=
      mul_le_mul_of_nonneg_left ((K - T).le_opNorm xi) (norm_nonneg _)
    _ = ‖K - T‖ * ‖xi‖ ^ 2 := by ring

/-- The same estimate for the CC20 defect form `id - A`. -/
theorem abs_cc20DefectQuadraticForm_sub_le_opNorm_mul_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K T : H →L[ℂ] H) (xi : H) :
    |cc20DefectQuadraticForm K xi - cc20DefectQuadraticForm T xi| ≤
      ‖K - T‖ * ‖xi‖ ^ 2 := by
  rw [show cc20DefectQuadraticForm K xi - cc20DefectQuadraticForm T xi =
      cc20RealQuadraticForm T xi - cc20RealQuadraticForm K xi by
    simp only [cc20DefectQuadraticForm, cc20RealQuadraticForm,
      inner_sub_right, Complex.sub_re]
    ring]
  rw [abs_sub_comm]
  exact abs_cc20RealQuadraticForm_sub_le_opNorm_mul_sq K T xi

/-- Equation `spectral0`, `‖K - T‖ ≤ epsilon`, implies its exact
quadratic-form shadow for `Re <xi, (id - K) xi>`. -/
theorem cc20DefectQuadraticForm_sub_lower_bound_of_opNorm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K T : H →L[ℂ] H) {epsilon : ℝ}
    (hgap : ‖K - T‖ ≤ epsilon) :
    ∀ xi : H, -epsilon * ‖xi‖ ^ 2 ≤
      cc20DefectQuadraticForm K xi - cc20DefectQuadraticForm T xi := by
  intro xi
  have habs :
      |cc20DefectQuadraticForm K xi - cc20DefectQuadraticForm T xi| ≤
        epsilon * ‖xi‖ ^ 2 :=
    (abs_cc20DefectQuadraticForm_sub_le_opNorm_mul_sq K T xi).trans
      (mul_le_mul_of_nonneg_right hgap (sq_nonneg _))
  simpa only [neg_mul] using neg_le_of_abs_le habs

/-- The numeric constants of Lemma `second`, with their order constraints.
The two analytic hypotheses live on the quadratic forms, not here. -/
structure CC20OperatorGapData (H : Type*) [NormedAddCommGroup H] where
  /-- the rank-one repair weight `a` (paper value `∼ 0.064`). -/
  a : ℝ
  /-- the operator gap `‖kf_I − T‖ ≤ ε₁` (paper value `≃ 0.00122`). -/
  epsilon1 : ℝ
  /-- the T-side coercivity constant `ε₂` (paper value `∼ 0.00441`). -/
  epsilon2 : ℝ
  /-- the derivative constant `2ε'(1₊)` packaged as one nonnegative scalar. -/
  ePrime : ℝ
  h_epsilon2_pos : 0 < epsilon2
  h_epsilon1_nonneg : 0 ≤ epsilon1
  h_a_nonneg : 0 ≤ a
  h_ePrime_nonneg : 0 ≤ ePrime
  h_gap : epsilon1 < epsilon2

/-- The rank-one constant produced by the gap data: `gamma = 2ε'(1₊)·a`. -/
noncomputable def CC20OperatorGapData.gamma
    {H : Type*} [NormedAddCommGroup H]
    (data : CC20OperatorGapData H) : ℝ :=
  2 * data.ePrime * data.a

/-- CC20 Lemma `first` converts the explicit exceptional spectral block of
`T` into the T-side coercivity used by Lemma `second`.

The caller now supplies only equation `spectral2`/`spectral3` as
`hspectral`; the rank-one repair and the passage from the two-dimensional
block to the whole Hilbert space are proved here. -/
theorem cc20TCoercivity_of_spectralBlock
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (data : CC20OperatorGapData H)
    (frame : CC20OrthonormalFrame H)
    (T : H →L[ℂ] H)
    {psi : H} {alpha : ℂ} {b c beta : ℝ}
    (hpsi : psi = alpha • frame.phi + (beta : ℂ) • frame.chi)
    (hp : 0 ≤ data.a * Complex.normSq alpha - b - data.epsilon2)
    (hr : 0 ≤ data.a * beta ^ 2 + c - data.epsilon2)
    (hdet : Complex.normSq ((data.a * beta : ℝ) * alpha) ≤
      (data.a * Complex.normSq alpha - b - data.epsilon2) *
        (data.a * beta ^ 2 + c - data.epsilon2))
    (hepsilon_le_c : data.epsilon2 ≤ c)
    (hspectral : ∀ xi : H,
      -b * Complex.normSq (inner ℂ frame.phi xi) +
          c * ‖cc20OrthogonalPart frame.phi xi‖ ^ 2 ≤
        cc20DefectQuadraticForm T xi) :
    ∀ xi : H,
      cc20DefectQuadraticForm T xi +
          data.a * ‖inner ℂ psi xi‖ ^ 2 ≥
        data.epsilon2 * ‖xi‖ ^ 2 := by
  intro xi
  have hhilbert := cc20LemmaFirstHilbertForm_ge_epsilon
    frame hpsi hp hr hdet hepsilon_le_c xi
  have hpsi_normSq :
      Complex.normSq (inner ℂ psi xi) = ‖inner ℂ psi xi‖ ^ 2 :=
    Complex.normSq_eq_norm_sq _
  unfold cc20LemmaFirstHilbertForm at hhilbert
  rw [hpsi_normSq] at hhilbert
  linarith [hspectral xi]

/-- Lemma `first` from an actual exceptional-eigenvector decomposition of
`T` and an upper spectral bound on its orthogonal residual.  No pointwise
defect-form estimate is supplied by the caller. -/
theorem cc20TCoercivity_of_spectralDecomposition
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (data : CC20OperatorGapData H)
    (frame : CC20OrthonormalFrame H)
    (T R : H →L[ℂ] H) (lambdaMax lambda2 : ℝ)
    {psi : H} {alpha : ℂ} {beta : ℝ}
    (hpsi : psi = alpha • frame.phi + (beta : ℂ) • frame.chi)
    (hp : 0 ≤ data.a * Complex.normSq alpha -
      (lambdaMax - 1) - data.epsilon2)
    (hr : 0 ≤ data.a * beta ^ 2 +
      (1 - lambda2) - data.epsilon2)
    (hdet : Complex.normSq ((data.a * beta : ℝ) * alpha) ≤
      (data.a * Complex.normSq alpha - (lambdaMax - 1) - data.epsilon2) *
        (data.a * beta ^ 2 + (1 - lambda2) - data.epsilon2))
    (hepsilon_le_gap : data.epsilon2 ≤ 1 - lambda2)
    (hT : ∀ xi : H,
      T xi = (lambdaMax : ℂ) •
          (inner ℂ frame.phi xi • frame.phi) +
        R (cc20OrthogonalPart frame.phi xi))
    (hR_invariant : ∀ u : H, inner ℂ frame.phi u = 0 →
      inner ℂ frame.phi (R u) = 0)
    (hR_upper : ∀ u : H, inner ℂ frame.phi u = 0 →
      cc20RealQuadraticForm R u ≤ lambda2 * ‖u‖ ^ 2) :
    ∀ xi : H,
      cc20DefectQuadraticForm T xi +
          data.a * ‖inner ℂ psi xi‖ ^ 2 ≥
        data.epsilon2 * ‖xi‖ ^ 2 := by
  exact cc20TCoercivity_of_spectralBlock data frame T hpsi hp hr hdet
    hepsilon_le_gap
    (cc20DefectQuadraticForm_ge_of_spectralDecomposition
      frame T R lambdaMax lambda2 hT hR_invariant hR_upper)

/-- Coercivity transfer through the operator gap: `(H1)` on the quadratic
form `qT`, plus the quadratic-form shadow `(H2)` of `‖kf_I − T‖ ≤ ε₁`,
upgrade to the same coercivity for `qKf` at the shifted level `ε₂ − ε₁`.
This is the displayed inequality chain of Lemma `second`'s proof. -/
theorem cc20GapCoercivity_transfer
    {H : Type*} [NormedAddCommGroup H]
    (data : CC20OperatorGapData H)
    {qT qKf ell : H → ℝ}
    (hT : ∀ ξ, qT ξ + data.a * (ell ξ) ^ 2 ≥ data.epsilon2 * ‖ξ‖ ^ 2)
    (hgap : ∀ ξ, -(data.epsilon1) * ‖ξ‖ ^ 2 ≤ qKf ξ - qT ξ) :
    ∀ ξ, qKf ξ + data.a * (ell ξ) ^ 2 ≥
      (data.epsilon2 - data.epsilon1) * ‖ξ‖ ^ 2 := by
  intro ξ
  have hnorm : (0 : ℝ) ≤ ‖ξ‖ ^ 2 := sq_nonneg _
  nlinarith [hT ξ, hgap ξ]

/-- The operator-level form of the preceding transfer.  Unlike
`cc20GapCoercivity_transfer`, this theorem accepts CC20's actual hypothesis
`‖kf_I - T‖ ≤ epsilon1`; the quadratic-form estimate is now a conclusion. -/
theorem cc20GapCoercivity_transfer_of_opNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (data : CC20OperatorGapData H)
    (kf T : H →L[ℂ] H) {ell : H → ℝ}
    (hT : ∀ xi,
      cc20DefectQuadraticForm T xi + data.a * (ell xi) ^ 2 ≥
        data.epsilon2 * ‖xi‖ ^ 2)
    (hgap : ‖kf - T‖ ≤ data.epsilon1) :
    ∀ xi, cc20DefectQuadraticForm kf xi + data.a * (ell xi) ^ 2 ≥
      (data.epsilon2 - data.epsilon1) * ‖xi‖ ^ 2 := by
  exact cc20GapCoercivity_transfer data hT
    (cc20DefectQuadraticForm_sub_lower_bound_of_opNorm_le kf T hgap)

/-- The rank-one conclusion of Lemma `second`: after the sign flip by
`−2ε'(1₊) ≤ 0`, the transferred coercivity bounds the negative form by
`gamma·|⟨ξ₀|ξ⟩|²` with `gamma = 2ε'(1₊)·a`. -/
theorem cc20NegativeForm_le_rankOne
    {H : Type*} [NormedAddCommGroup H]
    (data : CC20OperatorGapData H)
    {qKf ell : H → ℝ}
    (hcoer : ∀ ξ, qKf ξ + data.a * (ell ξ) ^ 2 ≥
      (data.epsilon2 - data.epsilon1) * ‖ξ‖ ^ 2) :
    ∀ ξ, -(2 * data.ePrime) * qKf ξ ≤ data.gamma * (ell ξ) ^ 2 := by
  intro ξ
  have hpos2 : (0 : ℝ) ≤ 2 * data.ePrime :=
    mul_nonneg (by norm_num) data.h_ePrime_nonneg
  have hneg : (-(2 : ℝ) * data.ePrime) ≤ 0 := by
    linarith
  have hflip := mul_le_mul_of_nonpos_left (hcoer ξ) hneg
  have hgapline := data.h_gap
  have hdiff : (0 : ℝ) ≤ data.epsilon2 - data.epsilon1 := by
    linarith
  have htail : (0 : ℝ) ≤
      2 * data.ePrime * (data.epsilon2 - data.epsilon1) * ‖ξ‖ ^ 2 :=
    mul_nonneg (mul_nonneg hpos2 hdiff) (sq_nonneg _)
  change -(2 * data.ePrime) * qKf ξ ≤
    2 * data.ePrime * data.a * (ell ξ) ^ 2
  ring_nf at hflip htail ⊢
  linarith

/-- CC20 Lemma `second` from the genuine operator gap and the T-side
coercivity.  The only remaining analytic input is now the stated spectral
estimate on `T`; no caller-supplied scalar shadow of the norm gap remains. -/
theorem cc20NegativeForm_le_rankOne_of_opNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (data : CC20OperatorGapData H)
    (kf T : H →L[ℂ] H) {ell : H → ℝ}
    (hT : ∀ xi,
      cc20DefectQuadraticForm T xi + data.a * (ell xi) ^ 2 ≥
        data.epsilon2 * ‖xi‖ ^ 2)
    (hgap : ‖kf - T‖ ≤ data.epsilon1) :
    ∀ xi, -(2 * data.ePrime) * cc20DefectQuadraticForm kf xi ≤
      data.gamma * (ell xi) ^ 2 := by
  exact cc20NegativeForm_le_rankOne data
    (cc20GapCoercivity_transfer_of_opNorm data kf T hT hgap)

/-- The operator-level conclusion of CC20 Lemma `second`, assembled directly
from the exceptional spectral block of `T`, the Lemma-first determinant
certificate, and equation `spectral0`. -/
theorem cc20NegativeForm_le_rankOne_of_spectralBlock_and_opNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (data : CC20OperatorGapData H)
    (frame : CC20OrthonormalFrame H)
    (kf T : H →L[ℂ] H)
    {psi : H} {alpha : ℂ} {b c beta : ℝ}
    (hpsi : psi = alpha • frame.phi + (beta : ℂ) • frame.chi)
    (hp : 0 ≤ data.a * Complex.normSq alpha - b - data.epsilon2)
    (hr : 0 ≤ data.a * beta ^ 2 + c - data.epsilon2)
    (hdet : Complex.normSq ((data.a * beta : ℝ) * alpha) ≤
      (data.a * Complex.normSq alpha - b - data.epsilon2) *
        (data.a * beta ^ 2 + c - data.epsilon2))
    (hepsilon_le_c : data.epsilon2 ≤ c)
    (hspectral : ∀ xi : H,
      -b * Complex.normSq (inner ℂ frame.phi xi) +
          c * ‖cc20OrthogonalPart frame.phi xi‖ ^ 2 ≤
        cc20DefectQuadraticForm T xi)
    (hgap : ‖kf - T‖ ≤ data.epsilon1) :
    ∀ xi : H,
      -(2 * data.ePrime) * cc20DefectQuadraticForm kf xi ≤
        data.gamma * ‖inner ℂ psi xi‖ ^ 2 := by
  exact cc20NegativeForm_le_rankOne_of_opNorm data kf T
    (cc20TCoercivity_of_spectralBlock data frame T hpsi hp hr hdet
      hepsilon_le_c hspectral)
    hgap

/-- CC20 Lemma `second` from the genuine spectral decomposition of `T`, the
residual spectral upper bound, the Lemma-first determinant certificate, and
the operator-norm estimate `spectral0`.  This endpoint has no caller-supplied
pointwise `hspectral` premise. -/
theorem cc20NegativeForm_le_rankOne_of_spectralDecomposition_and_opNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (data : CC20OperatorGapData H)
    (frame : CC20OrthonormalFrame H)
    (kf T R : H →L[ℂ] H) (lambdaMax lambda2 : ℝ)
    {psi : H} {alpha : ℂ} {beta : ℝ}
    (hpsi : psi = alpha • frame.phi + (beta : ℂ) • frame.chi)
    (hp : 0 ≤ data.a * Complex.normSq alpha -
      (lambdaMax - 1) - data.epsilon2)
    (hr : 0 ≤ data.a * beta ^ 2 +
      (1 - lambda2) - data.epsilon2)
    (hdet : Complex.normSq ((data.a * beta : ℝ) * alpha) ≤
      (data.a * Complex.normSq alpha - (lambdaMax - 1) - data.epsilon2) *
        (data.a * beta ^ 2 + (1 - lambda2) - data.epsilon2))
    (hepsilon_le_gap : data.epsilon2 ≤ 1 - lambda2)
    (hT : ∀ xi : H,
      T xi = (lambdaMax : ℂ) •
          (inner ℂ frame.phi xi • frame.phi) +
        R (cc20OrthogonalPart frame.phi xi))
    (hR_invariant : ∀ u : H, inner ℂ frame.phi u = 0 →
      inner ℂ frame.phi (R u) = 0)
    (hR_upper : ∀ u : H, inner ℂ frame.phi u = 0 →
      cc20RealQuadraticForm R u ≤ lambda2 * ‖u‖ ^ 2)
    (hgap : ‖kf - T‖ ≤ data.epsilon1) :
    ∀ xi : H,
      -(2 * data.ePrime) * cc20DefectQuadraticForm kf xi ≤
        data.gamma * ‖inner ℂ psi xi‖ ^ 2 := by
  exact cc20NegativeForm_le_rankOne_of_opNorm data kf T
    (cc20TCoercivity_of_spectralDecomposition data frame T R
      lambdaMax lambda2 hpsi hp hr hdet hepsilon_le_gap hT
      hR_invariant hR_upper)
    hgap

/-- Feeding the gap constant into the endpoint certificate data layer.
The band hypotheses remain explicit: the numeric enclosure of `2ε'(1₊)·a`
is caller-supplied. -/
noncomputable def CC20OperatorGapData.toGammaSpectralData
    {H : Type*} [NormedAddCommGroup H]
    (data : CC20OperatorGapData H)
    (hband : (294 : ℝ) / 100 < data.gamma)
    (hband' : data.gamma < (2944 : ℝ) / 1000) :
    CC20GammaSpectralData where
  gamma := data.gamma
  gamma_lower := hband
  gamma_upper := hband'

end C1CC20OperatorGap
end Source
end ConnesWeilRH
