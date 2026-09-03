/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import ConnesWeilRH.Dev.E0SlemmaBridge

/-!
# Record 1115: the rational-ingestion theorem (algebraic half, generic part)

Turns the EXACT RATIONAL data of 1115 - center matrices `G, M : n x n`,
moment rows `R : m x n`, an exact kernel closure `K * V + W * R = 1`
(1115 §0), the raw pencil center `D = U • G - M` and its symmetrization
`Dc` (additive identity `Dc + Dc = D + Dᵀ`), and an exact unit-LDL^T
`Kᵀ * Dc * K = L * diagonal d * Lᵀ` with nonnegative pivots `d` - into
record 1111's `E0SlemmaBridge.isTopBound U G M R`.

Why this is the right ingestion shape (1115 §3c + the run-3 finding):
every hypothesis of the concrete instances (modules `...Q28/Q38/Q48`)
is an entrywise RATIONAL identity, discharged by `norm_num` on data
read out of the committed bundles - no float-computed kernel object is
trusted (the law-55 center-displacement channel simply does not exist
over Q).  The proof is a closed-form sum of squares
`U • cᵀGc - cᵀMc = Σᵢ dᵢ (Lᵀx)ᵢ²` for `c = K x` (with `x` the closure
witness `V *ᵥ c`): the whitened-box / diagonal-dominance machinery that
DISCOVERED the positive pivots never enters the proof.

The `Dc` detour (rather than `Dc := U • G - M` literally): the 1112/1113
float machines produce ENTRYWISE-valid boxes whose mid matrix `M` is NOT
transpose-symmetric (measured max asymmetry |M_ij - M_ji| ~ 0.7-7.1 -
the antisymmetric part is invisible to every quadratic form ever
certified, so no certificate is affected, but an exact matrix equation
`Kᵀ (U•G - M) K = L D Lᵀ` with symmetric RHS would be FALSE for the raw
center `D`).  `h2`/`qflip` below prove once and for all that a quadratic
form sees only the symmetrized center, which is exactly `Dc`.

RH is NOT claimed here; this module certifies the ALGEBRAIC implication
from rational bundle data to `isTopBound`.  The transcendental half
(true Gram data inside the outward boxes, and `ker R_true` vs the box
kernel) remains the law-34 chain's own obligation (1115b / 1114).
-/

namespace ConnesWeilRH
namespace Source
namespace C1WindowRationalIngest

open Matrix

variable {n m k : ℕ}

/-- A quadratic form is invariant under transposing its matrix. -/
theorem qf_transpose (D : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (D.transpose.mulVec x) = x ⬝ᵥ (D.mulVec x) := by
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

/-- Pull `A *ᵥ x` out of the left slot of a dot product. -/
theorem dotProduct_mulVec_left {m' : ℕ}
    (A : Matrix (Fin m) (Fin m') ℝ) (x : Fin m' → ℝ) (y : Fin m → ℝ) :
    (A.mulVec x) ⬝ᵥ y = x ⬝ᵥ (A.transpose.mulVec y) :=
  calc (A.mulVec x) ⬝ᵥ y = y ⬝ᵥ A.mulVec x := dotProduct_comm _ _
    _ = (y ᵥ* A) ⬝ᵥ x := dotProduct_mulVec y A x
    _ = (A.transpose.mulVec y) ⬝ᵥ x := congrArg (· ⬝ᵥ x) (mulVec_transpose A y).symm
    _ = x ⬝ᵥ A.transpose.mulVec y := dotProduct_comm _ _

/-- Quadratic-form pull-through: `(K x)ᵀ D (K x) = xᵀ (Kᵀ D K) x`. -/
theorem qform_pull
    (K : Matrix (Fin n) (Fin m) ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) :
    (K.mulVec x) ⬝ᵥ (D.mulVec (K.mulVec x))
      = x ⬝ᵥ ((K.transpose * D * K).mulVec x) := by
  rw [dotProduct_mulVec_left, mulVec_mulVec, mulVec_mulVec]

/-- The closure identity `K * V + W * R = 1` says the columns of `K` span
the kernel of `R` with `V` as explicit witness: `R *ᵥ c = 0 → c = K *ᵥ
(V *ᵥ c)`.  No rank theory needed. -/
theorem exists_mulVec_eq_of_closure
    (K : Matrix (Fin n) (Fin k) ℝ) (V : Matrix (Fin k) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin m) ℝ) (R : Matrix (Fin m) (Fin n) ℝ)
    (hKVW : K * V + W * R = 1) (c : Fin n → ℝ) (hc : R.mulVec c = 0) :
    ∃ x, K.mulVec x = c := by
  refine ⟨V.mulVec c, ?_⟩
  have h1 : (K * V + W * R).mulVec c = (1 : Matrix (Fin n) (Fin n) ℝ).mulVec c :=
    by rw [hKVW]
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, one_mulVec, hc,
    mulVec_zero, add_zero] at h1
  exact h1

/-- The whitened diagonal form is a sum of squares. -/
theorem dotProduct_diagonal_nonneg
    (d : Fin k → ℝ) (hd : ∀ i, 0 ≤ d i) (y : Fin k → ℝ) :
    0 ≤ y ⬝ᵥ (diagonal d).mulVec y := by
  have heq : y ⬝ᵥ (diagonal d).mulVec y = ∑ i : Fin k, y i * (d i * y i) := by
    simp only [dotProduct, mulVec_diagonal]
  rw [heq]
  refine Finset.sum_nonneg fun i _ => ?_
  have : y i * (d i * y i) = d i * (y i * y i) := by ring
  rw [this]
  exact mul_nonneg (hd i) (mul_self_nonneg _)

/-- **The ingestion theorem** (record 1115, generic part): exact rational
closure data + an exact LDL^T factorization of the reduced pencil center
with nonnegative pivots carry record 1111's `isTopBound`.

Architecture note (RED-2 root cause): the smul-bearing term `U • G - M`
is elaborated ONCE and exported through the hypothesis `hD : D = U • G -
M`; every other site speaks of the free variable `D`, and `hDc` is the
ADDITIVE identity `Dc + Dc = D + Dᵀ` (no matrix `•` outside `hD`).
This dodges a real Mathlib v4.30 instance diamond: numeral smuls on
matrices elaborate through different `SMul` instances at different
positions of the same file, and `rw` then refuses to match
visually identical terms. -/
theorem isTopBound_of_closure_sos
    (U : ℝ) (G M : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin n) ℝ)
    (Dc D : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin n) (Fin k) ℝ) (V : Matrix (Fin k) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin m) ℝ) (L : Matrix (Fin k) (Fin k) ℝ)
    (d : Fin k → ℝ)
    (hD : D = U • G - M)
    (hKVW : K * V + W * R = 1)
    (hDc : Dc + Dc = D + D.transpose)
    (h : K.transpose * Dc * K = L * diagonal d * L.transpose)
    (hd : ∀ i, 0 ≤ d i) :
    E0SlemmaBridge.isTopBound U G M R := by
  intro c hc
  obtain ⟨x, hx⟩ := exists_mulVec_eq_of_closure K V W R hKVW c hc
  have e1 : dotProduct c ((Dc + Dc).mulVec c) = 2 * dotProduct c (Dc.mulVec c) := by
    rw [add_mulVec, dotProduct_add, two_mul]
  have e2 : dotProduct c ((D + D.transpose).mulVec c)
      = 2 * dotProduct c (D.mulVec c) := by
    rw [add_mulVec, dotProduct_add, qf_transpose, two_mul]
  have h2 : 2 * dotProduct c (Dc.mulVec c) = 2 * dotProduct c (D.mulVec c) := by
    rw [← e1, hDc, e2]
  have qflip : dotProduct c (D.mulVec c) = dotProduct c (Dc.mulVec c) :=
    mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num) h2.symm
  have h0 : 0 ≤ dotProduct c (Dc.mulVec c) := by
    rw [← hx, qform_pull, h, ← mulVec_mulVec, ← mulVec_mulVec]
    have pullL : x ⬝ᵥ (L.mulVec ((diagonal d).mulVec (L.transpose.mulVec x)))
        = (L.transpose.mulVec x)
          ⬝ᵥ ((diagonal d).mulVec (L.transpose.mulVec x)) := by
      rw [dotProduct_mulVec, ← mulVec_transpose]
    rw [pullL]
    exact dotProduct_diagonal_nonneg d hd _
  have hd0 : 0 ≤ dotProduct c (D.mulVec c) := by
    rw [qflip]
    exact h0
  have heq : dotProduct c (D.mulVec c)
      = U * dotProduct c (G.mulVec c) - dotProduct c (M.mulVec c) := by
    rw [hD, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul]
    simp
  refine le_of_sub_nonneg ?_
  rw [← heq]
  exact hd0

end C1WindowRationalIngest
end Source
end ConnesWeilRH
