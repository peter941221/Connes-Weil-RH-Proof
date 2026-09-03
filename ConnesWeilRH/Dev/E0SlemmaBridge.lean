/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Notation

/-!
# E0: the S-lemma top-bound bridge (record 1111)

Promotes the certificate CORE of records 1108-1110 to a formal theorem:
for symmetric-real matrix data `G, M : n x n`, `R, NU : m x n` and `U : R`,
the S-lemma pencil

    T(U, NU) := U • G - M - (Rᵀ * NU + NUᵀ * R)

being positive semidefinite IMPLIES the certified bound statement

    ∀ c, R *ᵥ c = 0  →  c ⬝ᵥ (M *ᵥ c) ≤ U * (c ⬝ᵥ (G *ᵥ c))

(`isTopBound` below), i.e. "certified top of the pencil M/G on the null space
of R is at most U" - the exact sentence 1109 (2,8) and 1110 (4,8) certify on
the float-domain machine.  No G-positive-definiteness is needed for the
implication, and NO multiplier-sign surgery: on the kernel the `NU` term
contributes exactly zero to the quadratic form (`c ⬝ᵥ ((Rᵀ*NU) *ᵥ c) =
(R *ᵥ c) ⬝ᵥ (NU *ᵥ c)`), which is the mechanism that kept 1108's conclusion
alive through its erratum.

This module is the INGESTION TEMPLATE for record 1112's rational interval
certificates.  It proves no sign about the window class: the concrete
transcendental data of 1108-1110 enter ONLY through a future data-ingestion
brick (and, down the line, the I-C function-space bridge - records 1112/1114
own those).  The toy `E0SlemmaBridge.ingestion_toy` discharges the schema on
closed numeric data (n = 2, m = 1, pencil exactly 0) to prove the template
accepts data at all.  RH unclaimed; no gate Prop is discharged here.
-/

namespace ConnesWeilRH
namespace Source
namespace E0SlemmaBridge

open Matrix

variable {n m : ℕ}

/-- The S-lemma pencil of records 1108-1110: `U • G - M - (Rᵀ * NU + NUᵀ * R)`
with the 1109 shape convention (`R, NU : m x n`). -/
def sLemmaPencil (U : ℝ) (G M : Matrix (Fin n) (Fin n) ℝ)
    (R NU : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  U • G - M - (R.transpose * NU + NU.transpose * R)

/-- The certified bound statement consumed by the float-domain records:
`U` bounds the `M`-form over the `G`-form on the null space of `R`. -/
def isTopBound (U : ℝ) (G M : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ c : Fin n → ℝ, R.mulVec c = 0 →
    dotProduct c (M.mulVec c) ≤ U * dotProduct c (G.mulVec c)

/-- **E0 bridge (headline)**: a positive-semidefinite S-lemma pencil carries
the top bound.  For every `c` in the kernel of `R` the two multiplier terms of
the pencil contribute zero to the quadratic form, so `0 ≤ cᵀTc = U cᵀGc - cᵀMc`
is exactly the certified inequality.  THIS is why ANY admissible multiplier
carries the implication (1108 erratum mechanism) and why no eigenvalue-sign
surgery appears in the certificate chain. -/
theorem isTopBound_of_psd {G M : Matrix (Fin n) (Fin n) ℝ}
    {R NU : Matrix (Fin m) (Fin n) ℝ} {U : ℝ}
    (hT : (sLemmaPencil U G M R NU).PosSemidef) : isTopBound U G M R := by
  intro c hc
  obtain ⟨_, hq⟩ := posSemidef_iff_dotProduct_mulVec.mp hT
  have hnz : 0 ≤ dotProduct c (sLemmaPencil U G M R NU *ᵥ c) := by simpa using hq c
  have hmulR : dotProduct c ((R.transpose * NU) *ᵥ c)
      = dotProduct (R.mulVec c) (NU.mulVec c) := by
    rw [mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have hmulN : dotProduct c ((NU.transpose * R) *ᵥ c)
      = dotProduct (R.mulVec c) (NU.mulVec c) := by
    rw [dotProduct_comm, mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
      dotProduct_comm]
  have hexp : dotProduct c (sLemmaPencil U G M R NU *ᵥ c)
      = U * dotProduct c (G.mulVec c) - dotProduct c (M.mulVec c)
        - (dotProduct (R.mulVec c) (NU.mulVec c)
          + dotProduct (R.mulVec c) (NU.mulVec c)) := by
    unfold sLemmaPencil
    simp only [sub_mulVec, add_mulVec, neg_mulVec, smul_mulVec_assoc, mulVec_mulVec,
      dotProduct_sub, dotProduct_add, dotProduct_neg, dotProduct_smul,
      dotProduct_mulVec, vecMul_transpose]
    ring
  rw [hexp, hmulR, hc, zero_dotProduct, hmulN, hc, zero_dotProduct] at hnz
  linarith

/-- Rayleigh-quotient form (`G > 0`): the literal "certified top <= U"
sentence of 1109/1110 for `G`-normalized test vectors. -/
theorem ratio_le_of_psd {G M : Matrix (Fin n) (Fin n) ℝ}
    {R NU : Matrix (Fin m) (Fin n) ℝ} {U : ℝ}
    (hT : (sLemmaPencil U G M R NU).PosSemidef)
    (c : Fin n → ℝ) (hc : R.mulVec c = 0)
    (hg : 0 < dotProduct c (G.mulVec c)) :
    dotProduct c (M.mulVec c) / dotProduct c (G.mulVec c) ≤ U := by
  have h := isTopBound_of_psd hT c hc
  rw [div_le_iff₀ hg]
  simpa using h

/-- **Toy ingestion evidence** (NOT a window class - a closed-data witness
that the template accepts computation): `R = ![0 1]` forces `c₂ = 0`;
`M = !![0 1; 1 0]` has top `0` on that kernel; `NU = !![-1 0]` cancels the
off-diagonal exactly, making the pencil the zero matrix at `U = 0`. -/
theorem ingestion_toy :
    isTopBound (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (!![(0 : ℝ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      (!![(0 : ℝ), 1] : Matrix (Fin 1) (Fin 2) ℝ) := by
  refine isTopBound_of_psd ?_
  have hzero : sLemmaPencil (0 : ℝ) 1 (!![(0 : ℝ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      (!![(0 : ℝ), 1] : Matrix (Fin 1) (Fin 2) ℝ)
      (!![-(1 : ℝ), 0] : Matrix (Fin 1) (Fin 2) ℝ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [sLemmaPencil, Matrix.mul_apply, transpose_apply, dotProduct,
        Fin.sum_univ_one, Fin.sum_univ_two]
  rw [hzero]
  exact PosSemidef.zero

end E0SlemmaBridge
end Source
end ConnesWeilRH
