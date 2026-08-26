import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# CC20 endpoint coefficient: exact rational band

CC20 Lemma `second` (source: <https://arxiv.org/abs/2006.13771>) defines the
rank-one coefficient as `c = 4 * gamma / log 2` and records the numerical band
`13 < c < 17`.
This leaf formalizes only the finite arithmetic implication from an explicit
rational enclosure for `gamma`; it does not prove that enclosure from the
operator or spectral argument.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20EndpointCoefficient

/-- The paper's coefficient `4 * gamma / log 2` lies in `(13, 17)` once the
Euler/operator constant has the displayed exact rational enclosure.

The two hypotheses are deliberately caller-supplied numerical data.  The
proof uses Mathlib's certified decimal bounds for `log 2`, so no floating-point
or unverified numerical computation is involved.
-/
theorem cc20EndpointCoefficient_band
    {gamma : ℝ}
    (hgamma_lower : (294 : ℝ) / 100 < gamma)
    (hgamma_upper : gamma < (2944 : ℝ) / 1000) :
    13 < 4 * gamma / Real.log 2 ∧
      4 * gamma / Real.log 2 < 17 := by
  have hlog_pos : 0 < Real.log 2 := by
    exact lt_trans (by norm_num) Real.log_two_gt_d9
  constructor
  · apply (lt_div_iff₀ hlog_pos).2
    nlinarith [Real.log_two_lt_d9]
  · apply (div_lt_iff₀ hlog_pos).2
    nlinarith [Real.log_two_gt_d9]

end C1CC20EndpointCoefficient
end Source
end ConnesWeilRH
