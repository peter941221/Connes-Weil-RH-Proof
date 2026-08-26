import ConnesWeilRH.Dev.C1CC20EndpointCertificateData
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
  show -(2 * data.ePrime) * qKf ξ ≤ 2 * data.ePrime * data.a * (ell ξ) ^ 2
  ring_nf at hflip htail ⊢
  linarith

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
