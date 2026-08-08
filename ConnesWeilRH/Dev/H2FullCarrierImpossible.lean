import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.CC20YoshidaMellin
import ConnesWeilRH.Dev.SchwartzAmbientOwnerProbe

/-! The FULL ambient (Schwartz `TestFunction`) carrier cannot host the
per-common finite-prime support data that `SourceWeilFormData` needs, because
its forward row `sourceVisibleGlobalIndex` quantifies over every test while
`globalIndexSet` is a finite `Finset ℕ`.  On the full Schwartz carrier every
prime `p` admits a bump with value `1` at `p`, so `sourceFinitePrimeTerm p` is
strictly positive for every prime; that forces the finite index set to contain
all the infinitely many primes.  H2 therefore needs the compact-family carrier
(`CompactLogTest`).  See docs/proofs/907. -/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace H2FullCarrier

open AnalyticCore
open CC20YoshidaInterpolationNode

/-- A bump on the full Schwartz carrier with value `1` at `(p : ℝ)`. -/
noncomputable def primeBumpAt (p : ℕ) (hp : p.Prime) : TestFunction :=
  Classical.choose
    (exists_testFunction_supported_Icc_eq_one
      (x := (p : ℝ)) (a := (p : ℝ) - 1) (b := (p : ℝ) + 1)
      (hax := by
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
        linarith)
      (hxb := by linarith))

lemma primeBumpAt_value (p : ℕ) (hp : p.Prime) :
    primeBumpAt p hp (p : ℝ) = 1 := by
  unfold primeBumpAt
  exact (Classical.choose_spec
    (exists_testFunction_supported_Icc_eq_one
      (x := (p : ℝ)) (a := (p : ℝ) - 1) (b := (p : ℝ) + 1)
      (hax := by
        have l1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
        linarith)
      (hxb := by linarith))).2.2

/-- The bump is supported inside `Icc (p-1) (p+1)`. -/
lemma primeBumpAt_support_subset (p : ℕ) (hp : p.Prime) :
    Function.support (fun t : ℝ => primeBumpAt p hp t) ⊆
      Set.Icc ((p : ℝ) - 1) ((p : ℝ) + 1) :=
  (Classical.choose_spec
    (exists_testFunction_supported_Icc_eq_one
      (x := (p : ℝ)) (a := (p : ℝ) - 1) (b := (p : ℝ) + 1)
      (hax := by
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
        linarith)
      (hxb := by linarith))).1

lemma bumpValue_pos (p : ℕ) (hp : p.Prime) :
    0 < ‖ambientSourceAlgebra.legacy.encode (primeBumpAt p hp) (p : ℝ)‖ := by
  simpa [ambientSourceAlgebra, ambientLegacy, primeBumpAt_value p hp]

/-- `E.valueAt` of the bump at `p` is strictly positive. -/
lemma valueAt_pos
    (E : AnalyticCore.SourceEvaluationData ambientSourceAlgebra)
    (p : ℕ) (hp : p.Prime) :
    0 < E.valueAt (primeBumpAt p hp) (p : ℝ) := by
  rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
  exact bumpValue_pos p hp

/-- The finite-prime term at a prime is strictly positive on the full carrier. -/
lemma sourceFinitePrimeTerm_pos
    (E : AnalyticCore.SourceEvaluationData ambientSourceAlgebra)
    (p : ℕ) (hp : p.Prime) :
    0 < E.sourceFinitePrimeTerm p (primeBumpAt p hp) := by
  have hval : 0 ≤ E.valueAt (primeBumpAt p hp) ((p : ℝ)⁻¹) := by
    rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
    exact norm_nonneg _
  have hsum : 0 < E.valueAt (primeBumpAt p hp) (p : ℝ) +
      E.valueAt (primeBumpAt p hp) ((p : ℝ)⁻¹) := by
    exact lt_of_lt_of_le (valueAt_pos E p hp) (le_add_of_nonneg_right hval)
  have hLam : 0 < ArithmeticFunction.vonMangoldt p := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact Real.log_pos (by exact_mod_cast hp.one_lt)
  have hsqrt : 0 < Real.sqrt (p : ℝ) := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hsc : 0 < (1 / Real.sqrt (p : ℝ) : ℝ) := by
    exact div_pos zero_lt_one hsqrt
  rw [AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt]
  exact mul_pos hLam (mul_pos hsc hsum)

lemma sourceFinitePrimeTerm_ne_zero
    (E : AnalyticCore.SourceEvaluationData ambientSourceAlgebra)
    (p : ℕ) (hp : p.Prime) :
    E.sourceFinitePrimeTerm p (primeBumpAt p hp) ≠ 0 :=
  ne_of_gt (sourceFinitePrimeTerm_pos E p hp)

/-- Every prime is in the (finite) global index set of any per-common support
on the full ambient carrier. -/
lemma primes_subset_global
    {E : AnalyticCore.SourceEvaluationData ambientSourceAlgebra}
    {common : ambientSourceAlgebra.Test}
    (S : AnalyticCore.PerCommonSourceFinitePrimeSupport ambientSourceAlgebra E common) :
    {q : ℕ | q.Prime} ⊆ {q : ℕ | q ∈ S.globalIndexSet} := by
  intro q hq
  exact S.sourceVisibleGlobalIndex q (primeBumpAt q hq)
    (sourceFinitePrimeTerm_ne_zero E q hq)

/-- The full ambient carrier admits NO per-common source finite-prime support. -/
theorem not_nonempty_PerCommonSourceFinitePrimeSupport_ambient
    {E : AnalyticCore.SourceEvaluationData ambientSourceAlgebra}
    (common : ambientSourceAlgebra.Test) :
    ¬ Nonempty (AnalyticCore.PerCommonSourceFinitePrimeSupport
        ambientSourceAlgebra E common) := by
  intro hend
  rcases hend with ⟨S⟩
  have hSub : {q : ℕ | q.Prime} ⊆ {q : ℕ | q ∈ S.globalIndexSet} :=
    primes_subset_global S
  have hFin : Set.Finite ({q : ℕ | q ∈ S.globalIndexSet} : Set ℕ) :=
    S.globalIndexSet.finite_toSet
  have hprFin : Set.Finite {q : ℕ | q.Prime} := hFin.subset hSub
  exact (Nat.infinite_setOf_prime : {q : ℕ | Nat.Prime q}.Infinite).not_finite hprFin

/-- `E.valueAt` of the encoded-even test at `p` is strictly positive. -/
lemma valueAt_pos_of_encoded_nonzero
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {p : ℕ} (B : A.Test) (hB : A.legacy.encode B (p : ℝ) ≠ 0) :
    0 < E.valueAt B (p : ℝ) := by
  rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
  exact norm_pos_iff.mpr hB

/-- The finite-prime term at a prime is strictly positive, given that the
legacy-encoded test is nonzero there. Carrier-agnostic. -/
lemma term_pos_of_encoded_nonzero
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {p : ℕ} (hp : p.Prime) (B : A.Test)
    (hB : A.legacy.encode B (p : ℝ) ≠ 0) :
    0 < E.sourceFinitePrimeTerm p B := by
  have hvalInv : 0 ≤ E.valueAt B ((p : ℝ)⁻¹) := by
    rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
    exact norm_nonneg _
  have hsum : 0 < E.valueAt B (p : ℝ) + E.valueAt B ((p : ℝ)⁻¹) := by
    exact lt_of_lt_of_le (valueAt_pos_of_encoded_nonzero E B hB)
      (le_add_of_nonneg_right hvalInv)
  have hLam : 0 < ArithmeticFunction.vonMangoldt p := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact Real.log_pos (by exact_mod_cast hp.one_lt)
  have hsqrt : 0 < Real.sqrt (p : ℝ) := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hsc : 0 < (1 / Real.sqrt (p : ℝ) : ℝ) := by
    exact div_pos zero_lt_one hsqrt
  rw [AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt]
  exact mul_pos hLam (mul_pos hsc hsum)

lemma term_ne_zero_of_encoded_nonzero
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {p : ℕ} (hp : p.Prime) (B : A.Test)
    (hB : A.legacy.encode B (p : ℝ) ≠ 0) :
    E.sourceFinitePrimeTerm p B ≠ 0 :=
  ne_of_gt (term_pos_of_encoded_nonzero E hp B hB)

/-- CARRIER-INDEPENDENT impossibility: the λ-free forward row of a
`PerCommonSourceFinitePrimeSupport` is `∀ n, ∀ F, term n F ≠ 0 → n ∈
globalIndexSet`.  Any carrier admitting, for every prime p, a test whose
encoded value is nonzero at p (both the full Schwartz space and a compact-log
family do) forces every prime into the finite `globalIndexSet : Finset ℕ`,
contradicting `Nat.infinite_setOf_prime`.  The structure is therefore
unsatisfiable for ANY non-degenerate carrier; the fix must be architectural
(narrow this forward row from `∀ F` to per-common, like the reverse rows). -/
lemma universal_impossible
    {A : AnalyticCore.SourceTestAlgebra} {E : AnalyticCore.SourceEvaluationData A}
    (B : ℕ → A.Test)
    (hB : ∀ p : ℕ, p.Prime → ¬ A.legacy.encode (B p) (p : ℝ) = 0) :
    ∀ common : A.Test,
      ¬ Nonempty (AnalyticCore.PerCommonSourceFinitePrimeSupport A E common) := by
  intro common hend
  rcases hend with ⟨S⟩
  have hmem : ∀ q : ℕ, q.Prime → q ∈ S.globalIndexSet := by
    intro q hq
    exact S.sourceVisibleGlobalIndex q (B q) (term_ne_zero_of_encoded_nonzero E hq (B q) (hB q hq))
  have hSub : {q : ℕ | q.Prime} ⊆ {q : ℕ | q ∈ S.globalIndexSet} := by
    intro q hq
    exact hmem q hq
  have hFin : Set.Finite ({q : ℕ | q ∈ S.globalIndexSet} : Set ℕ) :=
    S.globalIndexSet.finite_toSet
  have hprFin : Set.Finite {q : ℕ | q.Prime} := hFin.subset hSub
  exact (Nat.infinite_setOf_prime : {q : ℕ | Nat.Prime q}.Infinite).not_finite hprFin

end H2FullCarrier
end Dev
end Source
end ConnesWeilRH