import ConnesWeilRH.Dev.C1PositiveTraceCutoffGrowth

/-!
# C1 plain-window cutoff verdict

The exact window-length trace formula closes the remainder-corrected cutoff
readback itself, not only the dominated-diagonal route.  For a nonzero
compact-log root the raw cutoff traces grow linearly without bound, while
`CutoffLimitContracts.readback_tendsto_qw` combined with
`remainder_tendsto_zero` forces those same traces to converge to the finite
same-owner value `C1SameOwnerWeil.qw g`.  Both cannot hold, so the contract
type is empty for every nonzero root on every fixed whole-line basis.

This is a structural verdict about the plain-window detector family
`windowedBoundaryDetector`: its trace is exactly the window bulk mass
`(cutoffUpper - cutoffLower) * integral ||g.test||^2` and carries no
arithmetic content, so no remainder correction of this family can read back
`qw`.  A productive positive-trace limit needs a different detector family
(Hilbert-transform/Mellin-conjugated windows), not further estimates on this
one.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceCutoffVerdict

open MeasureTheory Filter
open scoped Topology
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open C1PositiveTraceCutoffAdapter
open C1PositiveTraceCutoffGrowth
open C1PositiveTraceCutoffObstruction
open C1PositiveTraceWindowProducer

noncomputable section

/-- The exact window-length formula makes the raw cutoff traces monotone:
the window grows with `n` while the whole-line mass stays fixed and
nonnegative. -/
theorem cutoffPositiveBasisData_trace_re_monotone
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    Monotone (fun n : Nat =>
      (ordinaryTraceAlong globalBasis
        (cutoffPositiveBasisData g globalBasis n).positiveComposition).re) := by
  intro m n hmn
  beta_reduce
  rw [cutoffPositiveBasisData_trace_re_eq_window_length_mul_mass,
    cutoffPositiveBasisData_trace_re_eq_window_length_mul_mass]
  have h1 := cutoffUpper_monotone g hmn
  have h2 := cutoffLower_antitone g hmn
  have hmass : 0 ≤ ∫ x : ℝ, Complex.normSq (g.test x) :=
    integral_nonneg (fun x => Complex.normSq_nonneg (g.test x))
  exact mul_le_mul_of_nonneg_right (by linarith) hmass

/-- The remainder-corrected cutoff readback contract is uninhabited for every
nonzero compact-log root.  The two contract fields force the raw traces to
converge to the finite value `qw g`; the exact window-length formula forces
the same traces to grow linearly without bound. -/
theorem not_nonempty_cutoffLimitContracts_of_test_ne_zero
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (hg : g.test ≠ 0) :
    IsEmpty (CutoffLimitContracts g globalBasis) :=
  ⟨fun contracts => by
    have hmono := cutoffPositiveBasisData_trace_re_monotone g globalBasis
    have hconv : Tendsto (fun n : Nat =>
        (ordinaryTraceAlong globalBasis
          (cutoffPositiveBasisData g globalBasis n).positiveComposition).re)
        atTop (𝓝 (C1SameOwnerWeil.qw g)) := by
      have h3 := contracts.readback_tendsto_qw.add contracts.remainder_tendsto_zero
      simpa [sub_add_cancel] using h3
    have hbound : ∀ᶠ n in atTop,
        (ordinaryTraceAlong globalBasis
          (cutoffPositiveBasisData g globalBasis n).positiveComposition).re <
          C1SameOwnerWeil.qw g + 1 :=
      hconv.eventually (gt_mem_nhds (by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
    obtain ⟨n₁, hn₁⟩ := cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero
      g globalBasis hg (C1SameOwnerWeil.qw g + 1)
    have hbig :=
      hmono (le_max_right N n₁ : (n₁ : ℕ) ≤ max N n₁)
    have hsmall := hN (max N n₁) (le_max_left N n₁)
    linarith
  ⟩

end
end C1PositiveTraceCutoffVerdict
end Dev
end Source
end ConnesWeilRH
