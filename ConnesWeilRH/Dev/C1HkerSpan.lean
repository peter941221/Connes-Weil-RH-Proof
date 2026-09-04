/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1TboxPullthrough

/-!
# Record 1120: (c) Hker closed via C1 exact annihilation at span level

Lands the LAST named slot of the record-1118 class-certificate chain
(docs/proofs/1120_hker_c1_span_preregistration.md): mechanism C1 of the
1118 decision rule, lifted to span level.  The committed rational data
satisfies `R * K = 0` EXACTLY (K is the exact-Fraction RREF nullspace
basis of the rationalized R, generation-time-asserted and re-verified by
`docs/proofs/1120_hker_probe.py`), so EVERY coefficient vector
`c = K.mulVec y` in the certificate's whitening subspace annihilates R
as a rational identity - the T-box domain condition `R.mulVec c = 0` is
a design constraint on the Stage-B test, not an analytic hypothesis.
Mechanism C2 (drift bound on the TRUE moment table) is NOT invoked; the
physical residual stays a named T2-side obligation, never silently
assumed.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HkerSpan

open Matrix
open C1HboxRationalData
open C1GateLevelTransferClasses
open C1LocalConfigurationDomination
open C1TboxPullthrough
open C1WindowRationalIngest
open CCM25Concrete.CompactLogConvolution

/-- **C1 exact annihilation at span level** (generic): if the basis `K`
annihilates `R` as a matrix identity, then every coefficient vector in
its span annihilates `R` as a vector identity. -/
theorem hkerC1_of_RK0 {m n k : ℕ} (R : Matrix (Fin m) (Fin n) ℝ)
    (K : Matrix (Fin n) (Fin k) ℝ) (hRK : R * K = 0) (y : Fin k → ℝ) :
    R.mulVec (K.mulVec y) = 0 := by
  have h1 : R.mulVec (K.mulVec y) = (R * K).mulVec y := by
    rw [Matrix.mulVec_mulVec]
  rw [h1, hRK, Matrix.zero_mulVec]

set_option maxHeartbeats 2000000000 in
-- reason: 15 entries x 8-term sums of ~100-digit rational products
/-- **C1 anchor (2,8)**: the committed basis exactly annihilates the
committed constraint matrix (rational identity; probe-verified). -/
theorem RK0_q28 : Q28.R * Q28.K = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals (simp [Q28.R, Q28.K, Matrix.mul_apply,
    Fin.sum_univ_succ]; norm_num)

set_option maxHeartbeats 2000000000 in
-- reason: 15 entries x 8-term sums of ~100-digit rational products
/-- **C1 anchor (3,8)**. -/
theorem RK0_q38 : Q38.R * Q38.K = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals (simp [Q38.R, Q38.K, Matrix.mul_apply,
    Fin.sum_univ_succ]; norm_num)

set_option maxHeartbeats 2000000000 in
-- reason: 15 entries x 8-term sums of ~100-digit rational products
/-- **C1 anchor (4,8)**. -/
theorem RK0_q48 : Q48.R * Q48.K = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals (simp [Q48.R, Q48.K, Matrix.mul_apply,
    Fin.sum_univ_succ]; norm_num)

/-- Span form of the C1 discharge, per class: the `hker` slot of the
1119 T-box theorems holds for EVERY `c = K.mulVec y`. -/
theorem hkerC1_q28 (y : Fin 5 → ℝ) : Q28.R.mulVec (Q28.K.mulVec y) = 0 :=
  hkerC1_of_RK0 Q28.R Q28.K RK0_q28 y

theorem hkerC1_q38 (y : Fin 5 → ℝ) : Q38.R.mulVec (Q38.K.mulVec y) = 0 :=
  hkerC1_of_RK0 Q38.R Q38.K RK0_q38 y

theorem hkerC1_q48 (y : Fin 5 → ℝ) : Q48.R.mulVec (Q48.K.mulVec y) = 0 :=
  hkerC1_of_RK0 Q48.R Q48.K RK0_q48 y

/-- **T-box span discharge (2,8)**: the radius-form box theorem holds on
the whole whitening subspace, no per-instance kernel check needed. -/
theorem tbox_spanK_q28 (Gt Mt : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, |Gt i j - Q28.G i j| ≤ radG_q28 i j)
    (hM : ∀ i j, |Mt i j - Q28.M i j| ≤ radM_q28 i j)
    (y : Fin 5 → ℝ) :
    Q28.K.mulVec y ⬝ᵥ (Mt *ᵥ (Q28.K.mulVec y))
      ≤ Q28.U * Q28.K.mulVec y ⬝ᵥ (Gt *ᵥ (Q28.K.mulVec y)) :=
  tbox_q28 Gt Mt hG hM (Q28.K.mulVec y) (hkerC1_q28 y)

/-- **T-box span discharge (3,8)**. -/
theorem tbox_spanK_q38 (Gt Mt : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, |Gt i j - Q38.G i j| ≤ radG_q38 i j)
    (hM : ∀ i j, |Mt i j - Q38.M i j| ≤ radM_q38 i j)
    (y : Fin 5 → ℝ) :
    Q38.K.mulVec y ⬝ᵥ (Mt *ᵥ (Q38.K.mulVec y))
      ≤ Q38.U * Q38.K.mulVec y ⬝ᵥ (Gt *ᵥ (Q38.K.mulVec y)) :=
  tbox_q38 Gt Mt hG hM (Q38.K.mulVec y) (hkerC1_q38 y)

/-- **T-box span discharge (4,8)**. -/
theorem tbox_spanK_q48 (Gt Mt : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, |Gt i j - Q48.G i j| ≤ radG_q48 i j)
    (hM : ∀ i j, |Mt i j - Q48.M i j| ≤ radM_q48 i j)
    (y : Fin 5 → ℝ) :
    Q48.K.mulVec y ⬝ᵥ (Mt *ᵥ (Q48.K.mulVec y))
      ≤ Q48.U * Q48.K.mulVec y ⬝ᵥ (Gt *ᵥ (Q48.K.mulVec y)) :=
  tbox_q48 Gt Mt hG hM (Q48.K.mulVec y) (hkerC1_q48 y)

/-- **ABSOLUTE headline over the span (2,8)**: with representation and
normalization slots, `Hbox` pins the gate at the named margin for every
coefficient vector of the whitening subspace. -/
theorem absolute_spanK_q28 {w : CompactLogTest}
    {G_true : Matrix (Fin 8) (Fin 8) ℝ} {M_true : Matrix (Fin 8) (Fin 8) ℝ}
    {y : Fin 5 → ℝ}
    (hrep : ICgate w.convolutionSquare
      = Q28.K.mulVec y ⬝ᵥ (M_true *ᵥ (Q28.K.mulVec y)))
    (hnorm : Q28.K.mulVec y ⬝ᵥ (G_true *ᵥ (Q28.K.mulVec y)) = 1)
    (hbox : Hbox GLo_q28 GHi_q28 MLo_q28 MHi_q28 G_true M_true) :
    ICgate w.convolutionSquare ≤ -mu_q28 :=
  absolute_true_q28 hrep (hkerC1_q28 y) hnorm hbox

/-- **ABSOLUTE headline over the span (3,8)**. -/
theorem absolute_spanK_q38 {w : CompactLogTest}
    {G_true : Matrix (Fin 8) (Fin 8) ℝ} {M_true : Matrix (Fin 8) (Fin 8) ℝ}
    {y : Fin 5 → ℝ}
    (hrep : ICgate w.convolutionSquare
      = Q38.K.mulVec y ⬝ᵥ (M_true *ᵥ (Q38.K.mulVec y)))
    (hnorm : Q38.K.mulVec y ⬝ᵥ (G_true *ᵥ (Q38.K.mulVec y)) = 1)
    (hbox : Hbox GLo_q38 GHi_q38 MLo_q38 MHi_q38 G_true M_true) :
    ICgate w.convolutionSquare ≤ -mu_q38 :=
  absolute_true_q38 hrep (hkerC1_q38 y) hnorm hbox

/-- **ABSOLUTE headline over the span (4,8)**. -/
theorem absolute_spanK_q48 {w : CompactLogTest}
    {G_true : Matrix (Fin 8) (Fin 8) ℝ} {M_true : Matrix (Fin 8) (Fin 8) ℝ}
    {y : Fin 5 → ℝ}
    (hrep : ICgate w.convolutionSquare
      = Q48.K.mulVec y ⬝ᵥ (M_true *ᵥ (Q48.K.mulVec y)))
    (hnorm : Q48.K.mulVec y ⬝ᵥ (G_true *ᵥ (Q48.K.mulVec y)) = 1)
    (hbox : Hbox GLo_q48 GHi_q48 MLo_q48 MHi_q48 G_true M_true) :
    ICgate w.convolutionSquare ≤ -mu_q48 :=
  absolute_true_q48 hrep (hkerC1_q48 y) hnorm hbox

end C1HkerSpan
end Source
end ConnesWeilRH
