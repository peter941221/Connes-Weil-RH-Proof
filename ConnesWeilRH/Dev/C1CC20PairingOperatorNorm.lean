/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20ProductIntegrability
import ConnesWeilRH.Dev.C1CC20OperatorGap

/-!
# From CC20 pairing bounds to operator-norm gaps

Paper equation (121) is a bound on every scalar pairing.  The CC20 operator
gap consumer instead expects an operator-norm bound.  This leaf records the
short Hilbert-space passage between those two forms:

    |<eta, A xi>| <= B * ||eta|| * ||xi||  for all eta, xi
                    implies
    ||A|| <= B.

The proof tests the pairing bound at `eta = A xi` and cancels the nonzero
output norm.  The CC20 specialization then turns a pairing bound for `kf - T`
into the exact norm-gap premise consumed by `C1CC20OperatorGap`.

This does not construct the concrete windowed operator on the `L2` quotient.
That representation and the certified `L1` profile difference remain separate
analytic obligations.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20PairingOperatorNorm

open C1CC20OperatorGap

/-- A uniform bound on all Hilbert-space pairings of a bounded operator bounds
its operator norm. -/
theorem opNorm_le_of_norm_inner_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ eta xi : H,
      ‖inner ℂ eta (A xi)‖ ≤ B * ‖eta‖ * ‖xi‖) :
    ‖A‖ ≤ B := by
  refine A.opNorm_le_bound hB ?_
  intro xi
  by_cases hzero : A xi = 0
  · simpa [hzero] using mul_nonneg hB (norm_nonneg xi)
  · have hpos : 0 < ‖A xi‖ := norm_pos_iff.mpr hzero
    have hself : ‖inner ℂ (A xi) (A xi)‖ = ‖A xi‖ * ‖A xi‖ := by
      rw [← inner_self_re_eq_norm]
      exact inner_self_eq_norm_mul_norm _
    exact le_of_mul_le_mul_left (by
      calc
        ‖A xi‖ * ‖A xi‖ = ‖inner ℂ (A xi) (A xi)‖ := hself.symm
        _ ≤ B * ‖A xi‖ * ‖xi‖ := hpair (A xi) xi
        _ = ‖A xi‖ * (B * ‖xi‖) := by ring) hpos

/-- A CC20 equation-(121)-style pairing estimate is precisely enough to
produce the operator-norm gap used by Lemma `second`. -/
theorem cc20GapNorm_le_of_pairingBound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (data : CC20OperatorGapData H) (kf T : H →L[ℂ] H)
    (hpair : ∀ eta xi : H,
      ‖inner ℂ eta ((kf - T) xi)‖ ≤
        data.epsilon1 * ‖eta‖ * ‖xi‖) :
    ‖kf - T‖ ≤ data.epsilon1 :=
  opNorm_le_of_norm_inner_le (kf - T) data.h_epsilon1_nonneg hpair

/-- The rank-one conclusion of CC20 Lemma `second` from a pairing estimate for
the operator gap.  The spectral/coercivity input on `T` remains explicit. -/
theorem cc20NegativeForm_le_rankOne_of_pairingBound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (data : CC20OperatorGapData H) (kf T : H →L[ℂ] H) {ell : H → ℝ}
    (hT : ∀ xi,
      cc20DefectQuadraticForm T xi + data.a * (ell xi) ^ 2 ≥
        data.epsilon2 * ‖xi‖ ^ 2)
    (hpair : ∀ eta xi : H,
      ‖inner ℂ eta ((kf - T) xi)‖ ≤
        data.epsilon1 * ‖eta‖ * ‖xi‖) :
    ∀ xi, -(2 * data.ePrime) * cc20DefectQuadraticForm kf xi ≤
      data.gamma * (ell xi) ^ 2 := by
  exact cc20NegativeForm_le_rankOne_of_opNorm data kf T hT
    (cc20GapNorm_le_of_pairingBound data kf T hpair)

end C1CC20PairingOperatorNorm
end Source
end ConnesWeilRH
