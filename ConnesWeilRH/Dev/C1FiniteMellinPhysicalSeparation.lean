import ConnesWeilRH.Dev.C1HealthyDetectorEvenOddPair

/-!
# C1FiniteMellinPhysicalSeparation - finite Laplace data versus a physical point

This raw interpolation lemma is a guard for the active healthy-`CompactLog`
B5 P2 gate.  It does not produce a detector or a sign: it proves only that
finitely many Laplace values cannot by themselves determine an evaluation of
the raw compact-log test at a positive physical log coordinate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FiniteMellinPhysicalSeparation

open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CC20YoshidaInterpolationNode
open CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedYoshidaBridge
open C1HealthyDetectorArchRescue
open C1HealthyDetectorEvenOddPair

noncomputable section

/-- A raw compact-log difference, reusing the existing pointwise sum and
negation constructors. -/
noncomputable def differenceTest (f g : CompactLogTest) : CompactLogTest :=
  sumTest f (negTest g)

@[simp] theorem differenceTest_apply (f g : CompactLogTest) (u : Real) :
    (differenceTest f g).test u = f.test u - g.test u := by
  rw [differenceTest, sumTest_apply, negTest_apply, sub_eq_add_neg]

theorem laplaceAt_differenceTest (f g : CompactLogTest) (s : Complex) :
    CompactLogTest.laplaceAt (differenceTest f g) s =
      CompactLogTest.laplaceAt f s - CompactLogTest.laplaceAt g s := by
  rw [differenceTest, laplaceAt_sumTest, laplaceAt_negTest, sub_eq_add_neg]

theorem support_differenceTest_subset (f g : CompactLogTest) :
    Function.support (differenceTest f g).test ⊆
      Function.support f.test ∪ Function.support g.test := by
  intro u hu
  rcases support_sumTest_subset f (negTest g) hu with hfu | hneg
  · exact Or.inl hfu
  · exact Or.inr (support_negTest g hneg)

/-- A finite collection of bilateral Laplace values does not determine a raw
physical evaluation.  The interpolation correction is placed near zero while
a value-one bump is placed near the positive coordinate `x`; their difference
has zero prescribed Laplace values and still equals one at `x`. -/
theorem exists_laplace_vanishing_test_value_one
    (nodes : Finset Complex) {x : Real} (hx : 0 < x) :
    ∃ h : CompactLogTest,
      Function.support h.test ⊆ Set.Ioo (-x) (2 * x) ∧
        (∀ z : FiniteMellinNode nodes,
          CompactLogTest.laplaceAt h z.1 = 0) ∧
          h.test x = 1 := by
  have hhalf : x / 2 < x := by linarith
  have hthreeHalf : x < 3 * x / 2 := by linarith
  let a : Real := Real.exp (x / 2)
  let b : Real := Real.exp (3 * x / 2)
  obtain ⟨p, hpSupport, _hpNonneg, _hpReal, hpValue⟩ :=
    exists_positive_interval_compact_test_real_bump
      (a := a) (b := b) (t := Real.exp x)
      (by dsimp [a]; exact Real.exp_lt_exp.mpr hhalf)
      (by dsimp [b]; exact Real.exp_lt_exp.mpr hthreeHalf)
      (by dsimp [a]; exact Real.exp_pos _)
  let h0 : CompactLogTest :=
    compactLogTestOfWindow p.test (Real.exp_pos _) (Real.exp_pos _) hpSupport
  have h0support : Function.support h0.test ⊆
      Set.Ioo (x / 2) (3 * x / 2) := by
    simpa [h0, a, b] using
      (compactLogTestOfWindow_support_subset p.test (Real.exp_pos (x / 2))
        (Real.exp_pos (3 * x / 2)) hpSupport)
  have h0value : h0.test x = 1 := by
    simpa [h0] using hpValue
  obtain ⟨h1, h1support, h1values⟩ :=
    CompactLogTest.exists_residualWindow_correction nodes
      (lower := -x / 4) (upper := x / 4)
      (by linarith) (by linarith)
      (fun z => CompactLogTest.laplaceAt h0 z.1)
  have h1zero : h1.test x = 0 := by
    by_contra hne
    have hmem : x ∈ Function.support h1.test :=
      Function.mem_support.mpr hne
    have hbound := h1support hmem
    linarith [hbound.2]
  refine ⟨differenceTest h0 h1, ?_, ?_, ?_⟩
  · refine Set.Subset.trans (support_differenceTest_subset h0 h1) ?_
    refine Set.union_subset ?_ ?_
    · intro u hu
      have hbound := h0support hu
      constructor <;> linarith [hbound.1, hbound.2]
    · intro u hu
      have hbound := h1support hu
      constructor <;> linarith [hbound.1, hbound.2]
  · intro z
    rw [laplaceAt_differenceTest, h1values]
    ring
  · simp [differenceTest_apply, h0value, h1zero]

end
end C1FiniteMellinPhysicalSeparation
end Source
end ConnesWeilRH
