import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.CC20YoshidaMellin
import ConnesWeilRH.Source.AnalyticCoreBase
import ConnesWeilRH.Dev.SchwartzAmbientOwnerProbe

/-!
# Non-degenerate common on the ambient carrier: the prime `2` is visible

`PerCommonSupportSatisfiabilityProbe` proved the narrowed
`PerCommonSourceFinitePrimeSupport` is satisfiable with the trivial `common = 0`.
This probe goes further: it builds a NON-DEGENERATE `common` on the ambient
(Schwartz) carrier, a compact-support smooth bump `commonBump` supported inside
`Icc (3/2) (5/2)` with value `1` at `2`.  Its finite-prime term at the prime `2`
is therefore strictly positive (`sourceFinitePrimeTerm 2 commonBump > 0`), so the
prime `2` is VISIBLE -- while the reverse rows pin the index set exactly to
`{2}`.  The constructed `PerCommonSourceFinitePrimeSupport` therefore has a
non-empty, exact, non-degenerate `globalIndexSet := {2}`, giving Lane-B its
first genuine carrier datum.

RH is NOT claimed.  The probe is an axiom-clean existence witness.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace AmbientPrimeProbe

open AnalyticCore
open CC20YoshidaInterpolationNode

/-- The common test: a compact-support smooth bump, supported in `Icc (3/2)
(5/2)`, value `1` at `2`. -/
noncomputable def commonBump : TestFunction :=
  Classical.choose
    (exists_testFunction_supported_Icc_eq_one
      (a := (3 / 2 : ℝ)) (x := (2 : ℝ)) (b := (5 / 2 : ℝ))
      (hax := by norm_num) (hxb := by norm_num))

/-- Support of the common bump is contained in `Icc (3/2) (5/2)`. -/
lemma commonBump_support_subset :
    Function.support (fun t : ℝ => commonBump t) ⊆
      Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) :=
  (Classical.choose_spec
    (exists_testFunction_supported_Icc_eq_one
      (a := (3 / 2 : ℝ)) (x := (2 : ℝ)) (b := (5 / 2 : ℝ))
      (hax := by norm_num) (hxb := by norm_num))).1

/-- The common bump takes the value `1` at `2`. -/
lemma commonBump_value_two : commonBump (2 : ℝ) = 1 :=
  (Classical.choose_spec
    (exists_testFunction_supported_Icc_eq_one
      (a := (3 / 2 : ℝ)) (x := (2 : ℝ)) (b := (5 / 2 : ℝ))
      (hax := by norm_num) (hxb := by norm_num))).2.2

/-- The evaluation data on the ambient carrier (empty structure, built via `mk`). -/
noncomputable def ambientEval :
    AnalyticCore.SourceEvaluationData ambientSourceAlgebra :=
  AnalyticCore.SourceEvaluationData.mk (A := ambientSourceAlgebra)

/-- `valueAt` of the common bump at the prime `2` is exactly `1`. -/
lemma common_valueAt_two : ambientEval.valueAt commonBump (2 : ℝ) = 1 := by
  rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
  have henc :
      ambientSourceAlgebra.legacy.encode commonBump (2 : ℝ) = 1 := by
    simp [ambientSourceAlgebra, ambientLegacy, commonBump_value_two]
  rw [henc]
  norm_num

/-- `valueAt` of the common bump at `2` is strictly positive. -/
lemma common_valueAt_two_pos : 0 < ambientEval.valueAt commonBump (2 : ℝ) := by
  rw [common_valueAt_two]
  norm_num

/-- The finite-prime term at the prime `2` is strictly positive. -/
lemma term_two_pos : 0 < ambientEval.sourceFinitePrimeTerm 2 commonBump := by
  have hvalInv : 0 ≤ ambientEval.valueAt commonBump ((2 : ℝ)⁻¹) := by
    rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
    exact norm_nonneg _
  have hsum : 0 < ambientEval.valueAt commonBump (2 : ℝ) +
      ambientEval.valueAt commonBump ((2 : ℝ)⁻¹) := by
    exact lt_of_lt_of_le common_valueAt_two_pos (le_add_of_nonneg_right hvalInv)
  have hLam : 0 < ArithmeticFunction.vonMangoldt 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact Real.log_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := by
    exact Real.sqrt_pos.mpr (by norm_num)
  have hsc : 0 < (1 / Real.sqrt (2 : ℝ) : ℝ) := by
    exact div_pos zero_lt_one hsqrt
  rw [AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt]
  exact mul_pos hLam (mul_pos hsc hsum)

/-- `term_two_pos`, as a `≠ 0` witness (the index 2 is genuinely visible). -/
lemma term_two_ne_zero : ambientEval.sourceFinitePrimeTerm 2 commonBump ≠ 0 :=
  ne_of_gt term_two_pos

/-- An integer point of `Icc (3/2) (5/2)` must be `2`. -/
lemma two_of_mem_Icc_two {n : ℕ} (h : (n : ℝ) ∈ Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ)) :
    n = 2 := by
  have hlo : (3 / 2 : ℝ) ≤ (n : ℝ) := h.1
  have hhi : (n : ℝ) ≤ (5 / 2 : ℝ) := h.2
  by_contra hnne
  have hcases : n ≤ 1 ∨ 3 ≤ n := by omega
  rcases hcases with h1 | h3
  · have h1r : (n : ℝ) ≤ (1 : ℝ) := by exact_mod_cast h1
    nlinarith
  · have h3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
    nlinarith

/-- `3/2` is strictly above the reciprocal of any natural number, so `1/n` can
never land inside the bump's support interval. -/
lemma not_mem_Icc_two_inv {n : ℕ} :
    ¬ ((n : ℝ)⁻¹ : ℝ) ∈ Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) := by
  intro h
  have hlo : (3 / 2 : ℝ) ≤ (n : ℝ)⁻¹ := h.1
  by_cases hn0 : n = 0
  · subst hn0
    norm_num at hlo
  · have hnge1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0))
    have hinv : (n : ℝ)⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hnge1
    norm_num at hlo
    linarith

/-- Carrier module of the common bump on the ambient ring: if the encoded value
is non-zero at `n`, then `n` is the visible prime `2`. -/
theorem forward_mem (n : ℕ)
    (hn : ambientEval.sourceFinitePrimeTerm n commonBump ≠ 0) :
    n = 2 := by
  have hcoefne : ((1 / Real.sqrt (n : ℝ)) *
      (ambientEval.valueAt commonBump (n : ℝ) +
        ambientEval.valueAt commonBump ((n : ℝ)⁻¹))) ≠ 0 := by
    intro hzero
    have htermeq : ambientEval.sourceFinitePrimeTerm n commonBump = 0 := by
      rw [AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt, hzero]
      norm_num
    exact hn htermeq
  have hsum : ambientEval.valueAt commonBump (n : ℝ) +
      ambientEval.valueAt commonBump ((n : ℝ)⁻¹) ≠ 0 := by
    intro hsumZero
    apply hcoefne
    rw [hsumZero]
    norm_num
  have hdisc : ambientEval.valueAt commonBump (n : ℝ) ≠ 0 ∨
      ambientEval.valueAt commonBump ((n : ℝ)⁻¹) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hsum (by
      have hz1 : ambientEval.valueAt commonBump (n : ℝ) = 0 := hne.1
      have hz2 : ambientEval.valueAt commonBump ((n : ℝ)⁻¹) = 0 := hne.2
      rw [hz1, hz2]
      norm_num)
  rcases hdisc with h1 | h2
  · have hcne : commonBump (n : ℝ) ≠ 0 := by
      intro hc
      apply h1
      rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
      simp [ambientSourceAlgebra, ambientLegacy, hc]
    have hmem : (n : ℝ) ∈ Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) :=
      commonBump_support_subset hcne
    have hn2 : n = 2 := two_of_mem_Icc_two hmem
    simp [hn2]
  · have hcne : commonBump ((n : ℝ)⁻¹) ≠ 0 := by
      intro hc
      apply h2
      rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
      simp [ambientSourceAlgebra, ambientLegacy, hc]
    have hmem : ((n : ℝ)⁻¹ : ℝ) ∈ Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) :=
      commonBump_support_subset hcne
    exact False.elim (not_mem_Icc_two_inv hmem)

/-- A non-degenerate per-common support on the ambient carrier: exact index set
`{2}`, where the bump's value `1` at `2` makes the prime visible. -/
noncomputable def nonDegenerateSupport :
    AnalyticCore.PerCommonSourceFinitePrimeSupport ambientSourceAlgebra
      ambientEval commonBump :=
{ globalIndexSet := ({2} : Finset ℕ)
  restrictedIndexSet := fun lambda : ℝ =>
    if 2 ≤ lambda ^ 2 then ({2} : Finset ℕ) else ∅
  sourceVisibleGlobalIndex := by
    intro n hn
    rw [forward_mem n hn]
    simp
  sourceVisibleRestrictedIndex := by
    intro lambda n hn hOne hle
    have hn2 : n = 2 := forward_mem n hn
    subst hn2
    rw [if_pos]
    · simp
    · simpa using hle
  commonGlobalIndex := by
    intro n hn
    simp at hn
    rw [hn]
    exact term_two_ne_zero
  commonRestrictedIndex := by
    intro lambda n hn
    by_cases hcut : 2 ≤ lambda ^ 2
    · simp [hcut] at hn
      have hn2 : n = 2 := by simpa using hn
      rw [hn2]
      exact ⟨term_two_ne_zero, by norm_num, hcut⟩
    · simp [hcut] at hn }

/-- The non-degenerate `PerCommonSourceFinitePrimeSupport` is realizable:
a genuine (non-zero) common with a visible prime `2`. -/
theorem nonDegenerate_nonempty :
    Nonempty (AnalyticCore.PerCommonSourceFinitePrimeSupport ambientSourceAlgebra
      ambientEval commonBump) :=
  ⟨nonDegenerateSupport⟩

/-- The visible prime set is exactly `{2}`, shown inside the data. -/
theorem globalIndex_exact :
    (AnalyticCore.PerCommonSourceFinitePrimeSupport.globalIndexSet
        nonDegenerateSupport) = ({2} : Finset ℕ) :=
  rfl

end AmbientPrimeProbe
end Dev
end Source
end ConnesWeilRH