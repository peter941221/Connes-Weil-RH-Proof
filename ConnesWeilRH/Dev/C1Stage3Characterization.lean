import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge

/-!
# C1Stage3Characterization

Stage 3 is not an independent bookkeeping lemma.  This file records the
exact logical boundary of the positive-trace contract: a producer for a test
exists exactly when the same-owner Weil square is nonnegative.  The reverse
direction uses a one-dimensional rank-one `A†A` witness; it is deliberately
not presented as the analytic producer needed for the RH route.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3Characterization

open CC20Concrete.PositiveTrace
open CCM25Concrete.CompactLogConvolution
open C1PositiveTraceLimitBridge
open Filter
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

private abbrev stage3Index := Unit

private noncomputable def stage3Basis :
    HilbertBasis stage3Index ℂ ℂ :=
  (OrthonormalBasis.singleton stage3Index ℂ).toHilbertBasis

private noncomputable def stage3Scalar (g : CompactLogTest) : ℂ :=
  (Real.sqrt (C1SameOwnerWeil.qw g) : ℂ)

private noncomputable def stage3Factor (g : CompactLogTest) : ℂ →L[ℂ] ℂ :=
  stage3Scalar g • ContinuousLinearMap.id ℂ ℂ

private noncomputable def stage3PairData (g : CompactLogTest) :
    BasisHilbertSchmidtPairData (G := ℂ) (stage3Basis) where
  left := stage3Factor g
  right := stage3Factor g
  left_summable_normSq := by
    exact Summable.of_finite
  right_summable_normSq := by
    exact Summable.of_finite

private theorem stage3PairData_trace_re (g : CompactLogTest)
    (hq : 0 ≤ C1SameOwnerWeil.qw g) :
    (ordinaryTraceAlong stage3Basis
      (stage3PairData g).traceProduct).re =
      C1SameOwnerWeil.qw g := by
  rw [ordinaryTraceAlong]
  rw [Complex.re_tsum (stage3PairData g).summable_traceProduct_diagonal]
  simp only [BasisHilbertSchmidtPairData.traceProduct_diagonal]
  have hq_exp :
      0 ≤ C1SameOwnerWeil.poleTerm g.convolutionSquare -
        C1SameOwnerWeil.archimedeanTerm g.convolutionSquare -
        C1SameOwnerWeil.finitePrimeSum g.convolutionSquare := by
    simpa only [C1SameOwnerWeil.qw, C1SameOwnerWeil.psi] using hq
  simp [stage3PairData, stage3Factor, stage3Scalar, stage3Basis,
    Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  rw [← Complex.ofReal_pow]
  rw [Complex.ofReal_re]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt hq_exp

noncomputable def positiveTracePairLimitFamily_exists_of_qw_nonnegative
    (g : CompactLogTest)
    (hq : 0 ≤ C1SameOwnerWeil.qw g) :
    PositiveTracePairLimitFamily (G := ℂ) stage3Basis g := by
  let d := stage3PairData g
  refine
    { traceData := fun _ => d
      self_pair := fun _ => rfl
      remainder := fun _ => 0
      remainder_tendsto_zero := ?_
      readback_tendsto_qw := ?_ }
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : Real))
      atTop (𝓝 (0 : Real)))
  · have htrace :
        (ordinaryTraceAlong stage3Basis d.traceProduct).re =
          C1SameOwnerWeil.qw g := stage3PairData_trace_re g hq
    simpa [d, htrace] using
      (tendsto_const_nhds : Tendsto
        (fun _ : Nat => C1SameOwnerWeil.qw g)
        atTop (𝓝 (C1SameOwnerWeil.qw g)))

theorem qw_nonnegative_iff_stage3_family_exists
    (g : CompactLogTest) :
    0 ≤ C1SameOwnerWeil.qw g ↔
      Nonempty (PositiveTracePairLimitFamily (G := ℂ) stage3Basis g) := by
  constructor
  · exact fun hq => ⟨positiveTracePairLimitFamily_exists_of_qw_nonnegative g hq⟩
  · rintro ⟨h⟩
    exact qw_nonnegative_of_positiveTracePairLimitFamily h

/-- Uniformly over the finite-vanishing owner, a pair-family producer is
exactly the healthy finite-vanishing criterion.  This is a characterization of
the missing sign content, not an analytic construction of the producer. -/
theorem healthyCriterionState_iff_all_vanishing_stage3_pair_families
    (F : Finset CriticalVanishingPoint) :
    C1.healthyCriterionState F ↔
      ∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace F g →
          Nonempty (PositiveTracePairLimitFamily (G := ℂ) stage3Basis g) := by
  rw [C1.healthyCriterionState_iff_all_vanishing_qw_nonnegative]
  constructor
  · intro h g hvanishing
    exact (qw_nonnegative_iff_stage3_family_exists g).mp (h g hvanishing)
  · intro h g hvanishing
    exact (qw_nonnegative_iff_stage3_family_exists g).mpr (h g hvanishing)

end
end C1Stage3Characterization
end Source
end ConnesWeilRH
