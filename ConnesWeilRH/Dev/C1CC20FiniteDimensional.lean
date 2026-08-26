import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# CC20 endpoint: finite-dimensional positivity brick

CC20, `weil-compo.tex`, Lemma `first` (the source is distributed with the
paper at <https://arxiv.org/abs/2006.13771>), reduces the endpoint estimate to
a real symmetric two-dimensional quadratic form.  This leaf records that
algebraic reduction only.  In particular, it does not assert the numerical
spectral bounds used by CC20's Lemma `second` and it does not prove the
Archimedean endpoint estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20FiniteDimensional

/-! ### A generic two-by-two quadratic-form lemma -/

/-- A real symmetric two-by-two form is nonnegative when its trace and
determinant are nonnegative.

The proof is by completing the square.  This is the exact algebraic step used
in CC20 Lemma `first`; no finite-dimensional spectral theorem is hidden here.
-/
theorem quadraticForm_nonneg_of_trace_det
    (p q r : ℝ)
    (htrace : 0 ≤ p + r)
    (hdet : 0 ≤ p * r - q ^ 2) :
    ∀ x y : ℝ, 0 ≤ p * x ^ 2 + 2 * q * x * y + r * y ^ 2 := by
  intro x y
  by_cases hp : 0 < p
  · have hscaled :
        0 ≤ p * (p * x ^ 2 + 2 * q * x * y + r * y ^ 2) := by
      calc
        0 ≤ (p * r - q ^ 2) * y ^ 2 + (p * x + q * y) ^ 2 := by
          exact add_nonneg (mul_nonneg hdet (sq_nonneg y)) (sq_nonneg _)
        _ = p * (p * x ^ 2 + 2 * q * x * y + r * y ^ 2) := by ring
    exact nonneg_of_mul_nonneg_right hscaled hp
  · have hp0 : p = 0 := by
      have hp' : p ≤ 0 := le_of_not_gt hp
      have hp_nonneg : 0 ≤ p := by
        by_contra hpn
        have hpneg : p < 0 := lt_of_not_ge hpn
        have hrpos : 0 < r := by nlinarith [htrace]
        have hprneg : p * r < 0 := mul_neg_of_neg_of_pos hpneg hrpos
        nlinarith [hdet, sq_nonneg q]
      exact le_antisymm hp' hp_nonneg
    subst hp0
    have hr : 0 ≤ r := by nlinarith [htrace]
    have hq0 : q = 0 := by
      have hqnonpos : q ^ 2 ≤ 0 := by nlinarith [hdet]
      nlinarith [sq_nonneg q]
    simpa [hq0] using mul_nonneg hr (sq_nonneg y)

/-- Shifted version of the two-by-two lemma.  Positivity of the matrix
`[[p - ε, q], [q, r - ε]]` is exactly the lower bound `ε ‖(x,y)‖²` for the
unshifted form. -/
theorem quadraticForm_ge_of_shifted_trace_det
    (p q r ε : ℝ)
    (htrace : 0 ≤ (p - ε) + (r - ε))
    (hdet : 0 ≤ (p - ε) * (r - ε) - q ^ 2) :
    ∀ x y : ℝ,
      ε * (x ^ 2 + y ^ 2) ≤ p * x ^ 2 + 2 * q * x * y + r * y ^ 2 := by
  intro x y
  have hshift := quadraticForm_nonneg_of_trace_det
    (p - ε) q (r - ε) htrace hdet x y
  nlinarith

/-- Converse certificate for a two-by-two form.  The nonnegative form forces
nonnegative diagonal entries; if the first one is positive, evaluating at
`(q,-p)` forces the determinant to be nonnegative.  If it is zero, any
nonzero off-diagonal entry would make the form negative at a suitable point. -/
theorem trace_det_of_quadraticForm_nonneg
    (p q r : ℝ)
    (hform : ∀ x y : ℝ, 0 ≤ p * x ^ 2 + 2 * q * x * y + r * y ^ 2) :
    0 ≤ p + r ∧ 0 ≤ p * r - q ^ 2 := by
  have hp : 0 ≤ p := by simpa using hform 1 0
  have hr : 0 ≤ r := by simpa using hform 0 1
  have htrace : 0 ≤ p + r := add_nonneg hp hr
  refine ⟨htrace, ?_⟩
  by_cases hp0 : p = 0
  · have hq0 : q = 0 := by
      by_contra hq
      have hqne : q ≠ 0 := hq
      have hbad := hform (-(r + 1) / (2 * q)) 1
      have hlinear :
          2 * q * (-(r + 1) / (2 * q)) + r = -1 := by
        field_simp [hqne]
        ring
      simp only [hp0, zero_mul, one_pow, mul_one, zero_add] at hbad
      rw [hlinear] at hbad
      nlinarith
    simp [hp0, hq0]
  · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have htest := hform q (-p)
    have hdet_mul : 0 ≤ p * (p * r - q ^ 2) := by
      convert htest using 1
      ring
    exact nonneg_of_mul_nonneg_right hdet_mul hp_pos

/-! ### The CC20 Lemma-first parameterization -/

/-- The CC20 Lemma `first` matrix in coordinates.

Here `α` is the component along `φ` and `β` the component in `φ^⊥`, so the
unit-vector constraint is `α² + β² = 1`.  The two hypotheses are exactly

`a + c ≥ b` and `b (a + c) ≤ a (b + c) α²`.
-/
def cc20LemmaFirstForm (a b c α β x y : ℝ) : ℝ :=
  (a * α ^ 2 - b) * x ^ 2 +
    2 * (a * α * β) * x * y +
    (a * β ^ 2 + c) * y ^ 2

theorem cc20LemmaFirstForm_trace
    {a b c α β : ℝ} (hunit : α ^ 2 + β ^ 2 = 1) :
    (a * α ^ 2 - b) + (a * β ^ 2 + c) = a + c - b := by
  calc
    (a * α ^ 2 - b) + (a * β ^ 2 + c) =
        a * (α ^ 2 + β ^ 2) + c - b := by ring
    _ = a + c - b := by rw [hunit]; ring

theorem cc20LemmaFirstForm_determinant
    {a b c α β : ℝ} (hunit : α ^ 2 + β ^ 2 = 1) :
    (a * α ^ 2 - b) * (a * β ^ 2 + c) - (a * α * β) ^ 2 =
      a * α ^ 2 * (b + c) - b * (a + c) := by
  have hβsq : β ^ 2 = 1 - α ^ 2 := by nlinarith [hunit]
  rw [show (a * α * β) ^ 2 = a ^ 2 * α ^ 2 * β ^ 2 by ring,
    hβsq]
  ring

theorem cc20LemmaFirstForm_nonneg
    {a b c α β : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hunit : α ^ 2 + β ^ 2 = 1)
    (htrace : b ≤ a + c)
    (hdet : b * (a + c) ≤ a * (b + c) * α ^ 2) :
    ∀ x y : ℝ, 0 ≤ cc20LemmaFirstForm a b c α β x y := by
  have hbc : 0 ≤ b + c := add_nonneg hb hc
  have htrace' :
      0 ≤ (a * α ^ 2 - b) + (a * β ^ 2 + c) := by
    nlinarith [hunit, htrace, hbc]
  have hdet' :
      0 ≤ (a * α ^ 2 - b) * (a * β ^ 2 + c) - (a * α * β) ^ 2 := by
    rw [cc20LemmaFirstForm_determinant hunit]
    nlinarith [hdet, hbc]
  intro x y
  exact quadraticForm_nonneg_of_trace_det
    (a * α ^ 2 - b) (a * α * β) (a * β ^ 2 + c)
    htrace' hdet' x y

/-- Exact `iff` form of CC20 Lemma `first` for the coordinate block. -/
theorem cc20LemmaFirstForm_nonneg_iff
    {a b c α β : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hunit : α ^ 2 + β ^ 2 = 1) :
    (∀ x y : ℝ, 0 ≤ cc20LemmaFirstForm a b c α β x y) ↔
      b ≤ a + c ∧ b * (a + c) ≤ a * (b + c) * α ^ 2 := by
  constructor
  · intro hform
    have hform' :
        ∀ x y : ℝ,
          0 ≤ (a * α ^ 2 - b) * x ^ 2 +
            2 * (a * α * β) * x * y +
            (a * β ^ 2 + c) * y ^ 2 := by
      intro x y
      simpa [cc20LemmaFirstForm] using hform x y
    have htd := trace_det_of_quadraticForm_nonneg
      (a * α ^ 2 - b) (a * α * β) (a * β ^ 2 + c) hform'
    have htrace_eq :=
      cc20LemmaFirstForm_trace (a := a) (b := b) (c := c)
        (α := α) (β := β) hunit
    have hdet_eq :=
      cc20LemmaFirstForm_determinant (a := a) (b := b) (c := c)
        (α := α) (β := β) hunit
    constructor
    · nlinarith [htd.1, htrace_eq]
    · nlinarith [htd.2, hdet_eq]
  · rintro ⟨htrace, hdet⟩
    exact cc20LemmaFirstForm_nonneg ha hb hc hunit htrace hdet

/-- Coercivity for the CC20 block once a candidate `ε` has passed the same
trace/determinant test after shifting the diagonal by `ε`. -/
theorem cc20LemmaFirstForm_ge_epsilon
    {a b c α β ε : ℝ}
    (hshift_trace : 0 ≤
      (a * α ^ 2 - b - ε) + (a * β ^ 2 + c - ε))
    (hshift_det : 0 ≤
      (a * α ^ 2 - b - ε) * (a * β ^ 2 + c - ε) -
        (a * α * β) ^ 2) :
    ∀ x y : ℝ,
      ε * (x ^ 2 + y ^ 2) ≤ cc20LemmaFirstForm a b c α β x y := by
  intro x y
  exact quadraticForm_ge_of_shifted_trace_det
    (a * α ^ 2 - b) (a * α * β) (a * β ^ 2 + c) ε
    hshift_trace hshift_det x y

/-- A packaged, reusable positivity certificate for the CC20 two-dimensional
endpoint block.  The data fields are in `Type` rather than `Prop`, so that
the real parameters are retained for later numerical readback. -/
structure CC20LemmaFirstCertificate where
  a : ℝ
  b : ℝ
  c : ℝ
  alpha : ℝ
  beta : ℝ
  a_nonnegative : 0 ≤ a
  b_nonnegative : 0 ≤ b
  c_nonnegative : 0 ≤ c
  unit_decomposition : alpha ^ 2 + beta ^ 2 = 1
  trace_condition : b ≤ a + c
  determinant_condition : b * (a + c) ≤ a * (b + c) * alpha ^ 2

theorem CC20LemmaFirstCertificate.nonnegative
    (certificate : CC20LemmaFirstCertificate) (x y : ℝ) :
    0 ≤ cc20LemmaFirstForm certificate.a certificate.b certificate.c
      certificate.alpha certificate.beta x y := by
  exact cc20LemmaFirstForm_nonneg
    certificate.a_nonnegative certificate.b_nonnegative
    certificate.c_nonnegative certificate.unit_decomposition
    certificate.trace_condition certificate.determinant_condition x y

end C1CC20FiniteDimensional
end Source
end ConnesWeilRH
