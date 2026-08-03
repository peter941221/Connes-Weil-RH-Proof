/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovCompletedForcingSupportBound

/-!
# Abstract guard for the scaled completed-forcing recurrence

Proofs 794 and 795 give a contracting recurrence for a lower-factor-square
normalized physical trace and a uniform bound only for the correspondingly
scaled forcing. This module records a scalar counterexample showing that these
two facts alone cannot recover a uniform bound for the raw trace.

The model deliberately omits the CCM24 real-line Hardy/prolate geometry. It
does not refute a source-specific completed-kernel cancellation. It prevents
the normalized recurrence from being used as such a cancellation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovScaledForcingRecurrenceGuard

/-- A positive lower factor with a fixed one-step contraction. -/
noncomputable def scalarLowerFactor : Nat -> Real
  | 0 => 1
  | n + 1 => scalarLowerFactor n / 2

/-- An unbounded raw endpoint. -/
def scalarRawEndpoint (n : Nat) : Real :=
  4 ^ n

/-- The lower-factor-square normalized endpoint. -/
noncomputable def scalarNormalizedEndpoint (n : Nat) : Real :=
  scalarLowerFactor n ^ 2 * scalarRawEndpoint n

/-- The raw one-step forcing. -/
def scalarForcing (n : Nat) : Real :=
  scalarRawEndpoint (n + 1) - scalarRawEndpoint n

theorem scalarLowerFactor_pos (n : Nat) : 0 < scalarLowerFactor n := by
  induction n with
  | zero => norm_num [scalarLowerFactor]
  | succ n ih =>
      simpa [scalarLowerFactor] using div_pos ih (show (0 : Real) < 2 by norm_num)

/-- The normalized endpoint is uniformly bounded even though the raw endpoint
is not. -/
theorem scalarNormalizedEndpoint_eq_one (n : Nat) :
    scalarNormalizedEndpoint n = 1 := by
  induction n with
  | zero =>
      norm_num [scalarNormalizedEndpoint, scalarLowerFactor, scalarRawEndpoint]
  | succ n ih =>
      change (scalarLowerFactor n / 2) ^ 2 * 4 ^ (n + 1) = 1
      rw [pow_succ]
      calc
        (scalarLowerFactor n / 2) ^ 2 * (4 ^ n * 4) =
            scalarLowerFactor n ^ 2 * 4 ^ n := by ring
        _ = 1 := by simpa [scalarNormalizedEndpoint, scalarRawEndpoint] using ih

/-- The scaled forcing remains uniformly bounded. -/
theorem scalarScaledForcing_eq_three_quarters (n : Nat) :
    scalarLowerFactor (n + 1) ^ 2 * scalarForcing n = (3 / 4 : Real) := by
  change (scalarLowerFactor n / 2) ^ 2 * (4 ^ (n + 1) - 4 ^ n) = 3 / 4
  rw [pow_succ]
  have hnormalized : scalarLowerFactor n ^ 2 * 4 ^ n = 1 := by
    simpa [scalarNormalizedEndpoint, scalarRawEndpoint] using
      scalarNormalizedEndpoint_eq_one n
  calc
    (scalarLowerFactor n / 2) ^ 2 * (4 ^ n * 4 - 4 ^ n) =
        (3 / 4 : Real) * (scalarLowerFactor n ^ 2 * 4 ^ n) := by ring
    _ = 3 / 4 := by rw [hnormalized]; norm_num

/-- This has exactly the stable form of the normalized physical recurrence:
the contraction and scaled forcing coexist with a nondecaying normalized
endpoint. -/
theorem scalarNormalizedEndpoint_succ_eq_contract_add_scaledForcing (n : Nat) :
    scalarNormalizedEndpoint (n + 1) =
      ((1 : Real) / 2) ^ 2 * scalarNormalizedEndpoint n +
        scalarLowerFactor (n + 1) ^ 2 * scalarForcing n := by
  rw [scalarNormalizedEndpoint_eq_one (n + 1), scalarNormalizedEndpoint_eq_one n,
    scalarScaledForcing_eq_three_quarters n]
  norm_num

theorem scalarScaledForcing_abs_le_one (n : Nat) :
    |scalarLowerFactor (n + 1) ^ 2 * scalarForcing n| <= 1 := by
  rw [scalarScaledForcing_eq_three_quarters]
  norm_num

theorem scalarRawEndpoint_tendsto_atTop :
    Filter.Tendsto scalarRawEndpoint Filter.atTop Filter.atTop := by
  simpa only [scalarRawEndpoint] using
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : Real) < 4 by norm_num))

/-- No family-uniform raw bound follows from the recurrence and scaled forcing
properties above. -/
theorem scalarRawEndpoint_not_uniformly_bounded :
    ¬ ∃ bound : Real, ∀ n : Nat, scalarRawEndpoint n <= bound := by
  rintro ⟨bound, hbound⟩
  obtain ⟨n, hn⟩ := (scalarRawEndpoint_tendsto_atTop.eventually_gt_atTop bound).exists
  exact (not_lt_of_ge (hbound n)) hn

/-- The complete scalar witness packages the facts shared by the failed
recurrence bootstrap: positive lower factors, bounded normalized endpoints,
bounded scaled forcing, the exact contracting recurrence, and an unbounded
raw endpoint. -/
theorem scaledForcingRecurrence_has_unbounded_raw_witness :
    (∀ n : Nat, 0 < scalarLowerFactor n) ∧
      (∀ n : Nat, scalarNormalizedEndpoint n = 1) ∧
      (∀ n : Nat, |scalarLowerFactor (n + 1) ^ 2 * scalarForcing n| <= 1) ∧
      (∀ n : Nat,
        scalarNormalizedEndpoint (n + 1) =
          ((1 : Real) / 2) ^ 2 * scalarNormalizedEndpoint n +
            scalarLowerFactor (n + 1) ^ 2 * scalarForcing n) ∧
      (¬ ∃ bound : Real, ∀ n : Nat, scalarRawEndpoint n <= bound) := by
  exact ⟨(fun n => scalarLowerFactor_pos n),
    (fun n => scalarNormalizedEndpoint_eq_one n),
    (fun n => scalarScaledForcing_abs_le_one n),
    (fun n => scalarNormalizedEndpoint_succ_eq_contract_add_scaledForcing n),
    scalarRawEndpoint_not_uniformly_bounded⟩

end CCM24FiniteSCausalMarkovScaledForcingRecurrenceGuard
end CCM25Concrete
end Source
end ConnesWeilRH
