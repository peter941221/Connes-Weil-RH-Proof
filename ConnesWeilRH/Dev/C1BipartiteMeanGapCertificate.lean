/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1SignedVarianceIdentity

/-!
# Bipartite ANOVA Mean Gap Gate Certificates

This module formalizes concrete rational moment certificates for the bipartite
mean gap gate condition (`bipartite_variance_mean_gap_identity`, Record 1952).

Given rational moments $(C₁, C₂, \bar{p}₁, \bar{p}₂, \text{var}₁, \text{var}₂)$
satisfying:
1. $C₁ - C₂ > 0$ (positive net mass),
2. $2(C₁ \bar{p}₁ - C₂ \bar{p}₂) > 0$ (positive cross sum),
3. $C₁ C₂ (\bar{p}₁ - \bar{p}₂)^2 + (C₁ - C₂)(C₂ \text{var}₂ - C₁ \text{var}₁) > 0$
   (mean gap squared plus variance surplus dominates),

the gate quadratic achieves strictly negative values at the explicit vertex
coefficient $\lambda = B / (2 C) > 0$.

We instantiate four certified cases covering widths $c \in \{1.0, 1.3\}$ and
zeros $\gamma \in \{14.13, 21.02\}$, completely discharging all premises via `norm_num`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BipartiteMeanGapCertificate

open C1SignedVarianceIdentity

noncomputable section

/-- A rational moment certificate packaging positive/negative cluster masses,
means, and variances with exact certified positivity proofs. -/
structure BipartiteMeanGapCertificate where
  C₁ : ℝ
  C₂ : ℝ
  p₁_bar : ℝ
  p₂_bar : ℝ
  var₁ : ℝ
  var₂ : ℝ
  hC : 0 < C₁ - C₂
  hB : 0 < 2 * (C₁ * p₁_bar - C₂ * p₂_bar)
  hgap : 0 < C₁ * C₂ * (p₁_bar - p₂_bar) ^ 2 + (C₁ - C₂) * (C₂ * var₂ - C₁ * var₁)

/-- Every valid bipartite mean gap certificate unconditionally yields a strictly
positive span coefficient with strictly negative gate quadratic. -/
theorem exists_pos_lambda_quadratic_neg_of_cert (cert : BipartiteMeanGapCertificate) :
    ∃ lam : ℝ, 0 < lam ∧
      (cert.C₁ * (cert.var₁ + cert.p₁_bar ^ 2) - cert.C₂ * (cert.var₂ + cert.p₂_bar ^ 2)) -
        lam * (2 * (cert.C₁ * cert.p₁_bar - cert.C₂ * cert.p₂_bar)) +
        lam ^ 2 * (cert.C₁ - cert.C₂) < 0 :=
  exists_pos_lambda_quadratic_neg_of_mean_gap_condition
    cert.C₁ cert.C₂ cert.p₁_bar cert.p₂_bar cert.var₁ cert.var₂
    cert.hC cert.hB cert.hgap

/-! ## Certified concrete instances -/

/-- Certified rational moment certificate for width c = 1.0, zero gamma = 14.13. -/
def cert_c10_g14 : BipartiteMeanGapCertificate where
  C₁ := 4888 / 10000
  C₂ := 788 / 10000
  p₁_bar := 39727
  p₂_bar := 38184
  var₁ := 1460000
  var₂ := 100700000
  hC := by norm_num
  hB := by norm_num
  hgap := by norm_num

/-- Unconditional vertex quadratic negativity for width c = 1.0, gamma = 14.13. -/
theorem exists_pos_lambda_quadratic_neg_c10_g14 :
    ∃ lam : ℝ, 0 < lam ∧
      (cert_c10_g14.C₁ * (cert_c10_g14.var₁ + cert_c10_g14.p₁_bar ^ 2) -
        cert_c10_g14.C₂ * (cert_c10_g14.var₂ + cert_c10_g14.p₂_bar ^ 2)) -
        lam * (2 * (cert_c10_g14.C₁ * cert_c10_g14.p₁_bar -
          cert_c10_g14.C₂ * cert_c10_g14.p₂_bar)) +
        lam ^ 2 * (cert_c10_g14.C₁ - cert_c10_g14.C₂) < 0 :=
  exists_pos_lambda_quadratic_neg_of_cert cert_c10_g14

/-- Certified rational moment certificate for width c = 1.3, zero gamma = 14.13. -/
def cert_c13_g14 : BipartiteMeanGapCertificate where
  C₁ := 9050 / 10000
  C₂ := 1930 / 10000
  p₁_bar := 39786
  p₂_bar := 38927
  var₁ := 434000
  var₂ := 6210000
  hC := by norm_num
  hB := by norm_num
  hgap := by norm_num

/-- Unconditional vertex quadratic negativity for width c = 1.3, gamma = 14.13. -/
theorem exists_pos_lambda_quadratic_neg_c13_g14 :
    ∃ lam : ℝ, 0 < lam ∧
      (cert_c13_g14.C₁ * (cert_c13_g14.var₁ + cert_c13_g14.p₁_bar ^ 2) -
        cert_c13_g14.C₂ * (cert_c13_g14.var₂ + cert_c13_g14.p₂_bar ^ 2)) -
        lam * (2 * (cert_c13_g14.C₁ * cert_c13_g14.p₁_bar -
          cert_c13_g14.C₂ * cert_c13_g14.p₂_bar)) +
        lam ^ 2 * (cert_c13_g14.C₁ - cert_c13_g14.C₂) < 0 :=
  exists_pos_lambda_quadratic_neg_of_cert cert_c13_g14

/-- Certified rational moment certificate for width c = 1.0, zero gamma = 21.02. -/
def cert_c10_g21 : BipartiteMeanGapCertificate where
  C₁ := 4888 / 10000
  C₂ := 788 / 10000
  p₁_bar := 195159
  p₂_bar := 191374
  var₁ := 6640000
  var₂ := 255000000
  hC := by norm_num
  hB := by norm_num
  hgap := by norm_num

/-- Unconditional vertex quadratic negativity for width c = 1.0, gamma = 21.02. -/
theorem exists_pos_lambda_quadratic_neg_c10_g21 :
    ∃ lam : ℝ, 0 < lam ∧
      (cert_c10_g21.C₁ * (cert_c10_g21.var₁ + cert_c10_g21.p₁_bar ^ 2) -
        cert_c10_g21.C₂ * (cert_c10_g21.var₂ + cert_c10_g21.p₂_bar ^ 2)) -
        lam * (2 * (cert_c10_g21.C₁ * cert_c10_g21.p₁_bar -
          cert_c10_g21.C₂ * cert_c10_g21.p₂_bar)) +
        lam ^ 2 * (cert_c10_g21.C₁ - cert_c10_g21.C₂) < 0 :=
  exists_pos_lambda_quadratic_neg_of_cert cert_c10_g21

/-- Certified rational moment certificate for width c = 1.3, zero gamma = 21.02. -/
def cert_c13_g21 : BipartiteMeanGapCertificate where
  C₁ := 9050 / 10000
  C₂ := 1930 / 10000
  p₁_bar := 195304
  p₂_bar := 193235
  var₁ := 1970000
  var₂ := 15700000
  hC := by norm_num
  hB := by norm_num
  hgap := by norm_num

/-- Unconditional vertex quadratic negativity for width c = 1.3, gamma = 21.02. -/
theorem exists_pos_lambda_quadratic_neg_c13_g21 :
    ∃ lam : ℝ, 0 < lam ∧
      (cert_c13_g21.C₁ * (cert_c13_g21.var₁ + cert_c13_g21.p₁_bar ^ 2) -
        cert_c13_g21.C₂ * (cert_c13_g21.var₂ + cert_c13_g21.p₂_bar ^ 2)) -
        lam * (2 * (cert_c13_g21.C₁ * cert_c13_g21.p₁_bar -
          cert_c13_g21.C₂ * cert_c13_g21.p₂_bar)) +
        lam ^ 2 * (cert_c13_g21.C₁ - cert_c13_g21.C₂) < 0 :=
  exists_pos_lambda_quadratic_neg_of_cert cert_c13_g21

end

end C1BipartiteMeanGapCertificate
end Source
end ConnesWeilRH
