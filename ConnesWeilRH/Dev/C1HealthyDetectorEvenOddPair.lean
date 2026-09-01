import ConnesWeilRH.Dev.C1HealthyDetectorArchRescue
import ConnesWeilRH.Source.RHDefinition

/-!
# C1HealthyDetectorEvenOddPair - the explicit even/odd detector pair

Record 1082 reduced consumer 3 kernel (a) to a NAMED CERTIFICATE SHAPE: an
even base `f`, an odd correction `g`, the three nodal sums, detection, root
support, and strict positivity of the two-term anchor
`0 < arch f.convSq + arch g.convSq`.  The nodal sums, the detection and the
root support were still HYPOTHESES of the rescue gate.

This module discharges them unconditionally, for every off-line source zero:

1. `negTest` - pointwise negation of a compact-log test, with the Laplace
   readback `laplaceAt (negTest f) s = -laplaceAt f s`;
2. `laplaceAt_reflection` - reflection without conjugation trades `s` for
   `-s`: `laplaceAt f.reflection s = laplaceAt f (-s)` (pure substitution, no
   symmetry input);
3. `evenPart h = h + h.reflection` is EVEN and `oddPart h = h - h.reflection`
   is ODD, unconditionally, and their Laplace values are `y(s) + y(-s)` and
   `y(s) - y(-s)` for `y = laplaceAt h`;
4. the 7-node symmetric interpolation: on `{rho, -rho, 0, +-1/2, +-1}` the
   residual-window correction realizes `1` at `rho`, `-1` at `-rho` and `0`
   elsewhere inside the ROOT window `(-log 2 / 2, log 2 / 2)`;
5. `exists_evenOddPair_of_offLineZero` - for every off-line source zero
   there IS a pair with all three nodal sums zero, detection value `2`,
   root support, and the certificate obligation reduced EXACTLY to the
   two-term anchor positivity through the record-1082 rescue gate.

The anchor positivity `0 < arch f.convSq + arch g.convSq` remains the single
open inequality of kernel (a); the 1077-1079 numerics (fl2 = -1.294, sink
33.78%) are the measurement program for it.  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyDetectorEvenOddPair

open MeasureTheory
open scoped ContDiff
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1
open C1HealthyYoshidaDetector
open C1HealthyDetectorRootSupportExit
open C1HealthyDetectorArchRescue

/-! ### Pointwise negation of a compact-log test -/

/-- Pointwise negation of a compact-log test. -/
noncomputable def negTest (f : CompactLogTest) : CompactLogTest := by
  let raw : ℝ → ℂ := fun x => -f.test x
  have hcompact : HasCompactSupport raw := by
    have hmul : HasCompactSupport (fun x : ℝ => (-(1 : ℂ)) * f.test x) :=
      f.compactSupport.mul_left
    simpa [raw, neg_one_mul] using hmul
  have hsmooth : ContDiff ℝ ∞ raw := by
    fun_prop
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem negTest_apply (f : CompactLogTest) (x : ℝ) :
    (negTest f).test x = -f.test x :=
  rfl

/-- Laplace evaluation negates under pointwise negation. -/
theorem laplaceAt_negTest (f : CompactLogTest) (s : ℂ) :
    CompactLogTest.laplaceAt (negTest f) s = -CompactLogTest.laplaceAt f s := by
  have hsplit : (CompactLogTest.exponentialWeight (negTest f) s).test =
      fun x : ℝ => -((CompactLogTest.exponentialWeight f s).test x) := by
    funext x
    simp [CompactLogTest.exponentialWeight_apply, negTest_apply]
  unfold CompactLogTest.laplaceAt
  rw [hsplit, integral_neg]

/-! ### Reflection trades `s` for `-s` -/

/-- Reflection in the log coordinate (without conjugation) evaluates the
Laplace transform at the mirrored point.  Pure substitution, no symmetry
hypothesis on the test. -/
theorem laplaceAt_reflection (f : CompactLogTest) (s : ℂ) :
    CompactLogTest.laplaceAt f.reflection s = CompactLogTest.laplaceAt f (-s) := by
  have hsplit : (CompactLogTest.exponentialWeight f.reflection s).test =
      fun x : ℝ => (CompactLogTest.exponentialWeight f (-s)).test (-x) := by
    funext x
    simp [CompactLogTest.exponentialWeight_apply, CompactLogTest.reflection_apply]
  unfold CompactLogTest.laplaceAt
  rw [hsplit, integral_neg_eq_self]

/-! ### The even and odd parts of a test -/

/-- The even part of a test: `h + h.reflection`, even by construction. -/
noncomputable def evenPart (h : CompactLogTest) : CompactLogTest :=
  sumTest h h.reflection

/-- The odd part of a test: `h - h.reflection`, odd by construction. -/
noncomputable def oddPart (h : CompactLogTest) : CompactLogTest :=
  sumTest h (negTest h.reflection)

theorem laplaceAt_evenPart (h : CompactLogTest) (s : ℂ) :
    CompactLogTest.laplaceAt (evenPart h) s =
      CompactLogTest.laplaceAt h s + CompactLogTest.laplaceAt h.reflection s :=
  laplaceAt_sumTest h h.reflection s

theorem laplaceAt_oddPart (h : CompactLogTest) (s : ℂ) :
    CompactLogTest.laplaceAt (oddPart h) s =
      CompactLogTest.laplaceAt h s - CompactLogTest.laplaceAt h.reflection s := by
  show CompactLogTest.laplaceAt (sumTest h (negTest h.reflection)) s = _
  rw [laplaceAt_sumTest, laplaceAt_negTest]
  ring

theorem test_even_evenPart (h : CompactLogTest) :
    ∀ x : ℝ, (evenPart h).test (-x) = (evenPart h).test x := by
  intro x
  simp only [evenPart, sumTest_apply, CompactLogTest.reflection_apply, neg_neg]
  ring

theorem test_neg_oddPart (h : CompactLogTest) :
    ∀ x : ℝ, (oddPart h).test (-x) = -(oddPart h).test x := by
  intro x
  simp only [oddPart, sumTest_apply, negTest_apply,
    CompactLogTest.reflection_apply, neg_neg]
  ring

/-! ### Support bookkeeping -/

/-- The support of a pointwise sum lies in the union of the summand
supports. -/
theorem support_sumTest_subset (f g : CompactLogTest) :
    Function.support (sumTest f g).test ⊆
      Function.support f.test ∪ Function.support g.test := by
  intro x hx
  simp only [Function.mem_support, Set.mem_union, sumTest_apply] at hx ⊢
  by_cases h1 : f.test x = 0
  · right
    intro h2
    rw [h1, zero_add] at hx
    exact hx h2
  · left
    exact h1

/-- Pointwise negation does not enlarge the support. -/
theorem support_negTest (f : CompactLogTest) :
    Function.support (negTest f).test ⊆ Function.support f.test := by
  intro x hx
  simp only [Function.mem_support, negTest_apply] at hx ⊢
  intro hz
  rw [hz, neg_zero] at hx
  exact hx rfl

/-- On a symmetric log window the even part keeps the closed window. -/
theorem support_evenPart_subset_Icc (h : CompactLogTest) (c : ℝ)
    (hsupp : Function.support h.test ⊆ Set.Ioo (-c) c) :
    Function.support (evenPart h).test ⊆ Set.Icc (-c) c := by
  refine Set.Subset.trans (support_sumTest_subset h h.reflection)
    (Set.union_subset ?_ ?_)
  · exact Set.Subset.trans hsupp Set.Ioo_subset_Icc_self
  · simpa only [neg_neg] using
      CompactLogTest.reflection_support_subset_Icc h (-c) c
        (Set.Subset.trans hsupp Set.Ioo_subset_Icc_self)

/-- On a symmetric log window the odd part keeps the closed window. -/
theorem support_oddPart_subset_Icc (h : CompactLogTest) (c : ℝ)
    (hsupp : Function.support h.test ⊆ Set.Ioo (-c) c) :
    Function.support (oddPart h).test ⊆ Set.Icc (-c) c := by
  refine Set.Subset.trans (support_sumTest_subset h (negTest h.reflection))
    (Set.union_subset ?_ ?_)
  · exact Set.Subset.trans hsupp Set.Ioo_subset_Icc_self
  · refine Set.Subset.trans (support_negTest h.reflection) ?_
    simpa only [neg_neg] using
      CompactLogTest.reflection_support_subset_Icc h (-c) c
        (Set.Subset.trans hsupp Set.Ioo_subset_Icc_self)

/-! ### The seven symmetric interpolation nodes -/

/-- The seven nodes of the symmetric even/odd interpolation: the selected
zero and its reflection, the triple vanishing set and their reflections. -/
noncomputable def pairNodeSet (rho : ℂ) : Finset ℂ :=
  {rho, -rho, 0, 1 / 2, -(1 / 2 : ℂ), 1, -1}

/-- Target values: `1` at `rho`, `-1` at `-rho`, `0` on the five criterion
nodes. -/
noncomputable def pairNodeTarget (rho : ℂ)
    (z : FiniteMellinNode (pairNodeSet rho)) : ℂ :=
  if z.1 = rho then 1 else if z.1 = -rho then -1 else 0

/-! ### The nonzero facts used to evaluate the target -/

private theorem pair_ne_zero
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    rho ≠ 0 := by
  intro hzero
  have hpos := sourceNontrivialZero_zero_lt_re hrho
  rw [hzero] at hpos
  norm_num at hpos

private theorem pair_ne_half
    {rho : ℂ} (hoff : rho.re ≠ 1 / 2) :
    rho ≠ (1 / 2 : ℂ) := by
  intro hhalf
  apply hoff
  calc
    rho.re = (1 / 2 : Complex).re := congrArg Complex.re hhalf
    _ = 1 / 2 := by norm_num

private theorem pair_ne_one
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    rho ≠ 1 := by
  intro hone
  have hlt := sourceNontrivialZero_re_lt_one hrho
  rw [hone] at hlt
  norm_num at hlt

private theorem pair_ne_neg_half
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    rho ≠ -(1 / 2 : ℂ) := by
  intro hnh
  have hpos := sourceNontrivialZero_zero_lt_re hrho
  rw [hnh] at hpos
  norm_num at hpos

private theorem pair_ne_neg_one
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    rho ≠ -1 := by
  intro hnh
  have hpos := sourceNontrivialZero_zero_lt_re hrho
  rw [hnh] at hpos
  norm_num at hpos

private theorem pair_zero_ne_neg_rho {rho : ℂ} (hrho0 : rho ≠ 0) :
    (0 : ℂ) ≠ -rho := by
  intro h
  exact hrho0 (neg_eq_zero.mp h.symm)

private theorem half_ne_neg_rho
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    (1 / 2 : ℂ) ≠ -rho := by
  intro h
  have h' : -(1 / 2 : ℂ) = rho := by simpa using congrArg Neg.neg h
  exact pair_ne_neg_half hrho h'.symm

private theorem negHalf_ne_neg_rho
    {rho : ℂ} (hoff : rho.re ≠ 1 / 2) :
    -(1 / 2 : ℂ) ≠ -rho := by
  intro h
  have h' : (1 / 2 : ℂ) = rho := by simpa using congrArg Neg.neg h
  exact pair_ne_half hoff h'.symm

private theorem one_ne_neg_rho
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    (1 : ℂ) ≠ -rho := by
  intro h
  have h' : (-1 : ℂ) = rho := by simpa using congrArg Neg.neg h
  exact pair_ne_neg_one hrho h'.symm

private theorem negOne_ne_neg_rho
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    (-1 : ℂ) ≠ -rho := by
  intro h
  have h' : (1 : ℂ) = rho := by simpa using congrArg Neg.neg h
  exact pair_ne_one hrho h'.symm

private theorem pair_neg_rho_ne_rho {rho : ℂ} (hrho0 : rho ≠ 0) :
    -rho ≠ rho := by
  intro h
  have h2 : rho - -rho = 0 := by
    rw [h]
    ring
  have h3 : rho + rho = 0 := by
    rw [← sub_neg_eq_add]
    exact h2
  have h4 : (2 : ℂ) * rho = 0 := by
    rw [two_mul]
    exact h3
  exact hrho0 (((mul_eq_zero (b := rho)).mp h4).resolve_left (by norm_num))

/-! ### The target values at all seven nodes -/

private theorem pairNodeTarget_at_rho (rho : ℂ) :
    pairNodeTarget rho (⟨rho, by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)) = 1 := by
  dsimp [pairNodeTarget]
  exact if_pos rfl

private theorem pairNodeTarget_at_neg_rho {rho : ℂ} (hrho0 : rho ≠ 0) :
    pairNodeTarget rho (⟨-rho, by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)) = -1 := by
  dsimp [pairNodeTarget]
  rw [if_neg (pair_neg_rho_ne_rho hrho0), if_pos rfl]

private theorem pairNodeTarget_at_zero
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    pairNodeTarget rho (⟨0, by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)) = 0 := by
  dsimp [pairNodeTarget]
  rw [if_neg (Ne.symm (pair_ne_zero hrho)),
    if_neg (pair_zero_ne_neg_rho (pair_ne_zero hrho))]

private theorem pairNodeTarget_at_half
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    pairNodeTarget rho (⟨1 / 2, by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)) = 0 := by
  dsimp [pairNodeTarget]
  rw [if_neg (Ne.symm (pair_ne_half hoff)), if_neg (half_ne_neg_rho hrho)]

private theorem pairNodeTarget_at_neg_half
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    pairNodeTarget rho (⟨-(1 / 2 : ℂ), by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)) = 0 := by
  dsimp [pairNodeTarget]
  rw [if_neg (Ne.symm (pair_ne_neg_half hrho)), if_neg (negHalf_ne_neg_rho hoff)]

private theorem pairNodeTarget_at_one
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    pairNodeTarget rho (⟨1, by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)) = 0 := by
  dsimp [pairNodeTarget]
  rw [if_neg (Ne.symm (pair_ne_one hrho)), if_neg (one_ne_neg_rho hrho)]

private theorem pairNodeTarget_at_neg_one
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    pairNodeTarget rho (⟨-1, by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)) = 0 := by
  dsimp [pairNodeTarget]
  rw [if_neg (Ne.symm (pair_ne_neg_one hrho)), if_neg (negOne_ne_neg_rho hrho)]

/-! ### The main theorem: the explicit even/odd pair exists -/

/-- THE EXPLICIT EVEN/ODD PAIR.  For every off-line source zero there is a
pair of compact-log tests such that `f` is even, `g` is odd, the three nodal
sums vanish (`lap f 0 = 0`, the half and one sums), the sum detects `rho`
with value `2`, the combined support sits in the closed root window, and the
record-1082 rescue gate follows from the two-term anchor positivity alone.
Kernel (a) of consumer 3 is thereby reduced EXACTLY to
`0 < arch f.convSq + arch g.convSq` on a CONSTRUCTED pair. -/
theorem exists_evenOddPair_of_offLineZero
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ∃ f g : CompactLogTest,
      (∀ x : ℝ, f.test (-x) = f.test x) ∧
        (∀ x : ℝ, g.test (-x) = -g.test x) ∧
          CompactLogTest.laplaceAt f 0 = 0 ∧
            (CompactLogTest.laplaceAt f (1 / 2 : ℂ) +
                CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0 ∧
              CompactLogTest.laplaceAt f 1 + CompactLogTest.laplaceAt g 1 = 0 ∧
                CompactLogTest.laplaceAt (sumTest f g) rho ≠ 0 ∧
                  Function.support (sumTest f g).test ⊆
                    Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) ∧
                    (0 < C1SameOwnerWeil.archimedeanTerm f.convolutionSquare +
                        C1SameOwnerWeil.archimedeanTerm g.convolutionSquare →
                      rootSupportedHealthyDetectorGate rho)) := by
  classical
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlower : -(Real.log 2 / 2) < 0 := by linarith
  have hupper : (0 : ℝ) < Real.log 2 / 2 := by linarith
  have hrho0 : rho ≠ 0 := pair_ne_zero hrho
  rcases CompactLogTest.exists_residualWindow_correction (pairNodeSet rho)
      (lower := -(Real.log 2 / 2)) (upper := Real.log 2 / 2) hlower hupper
      (pairNodeTarget rho) with ⟨h, hwin, hvalues⟩
  have heven : ∀ x : ℝ, (evenPart h).test (-x) = (evenPart h).test x :=
    test_even_evenPart h
  have hodd : ∀ x : ℝ, (oddPart h).test (-x) = -(oddPart h).test x :=
    test_neg_oddPart h
  have hf0 : CompactLogTest.laplaceAt (evenPart h) 0 = 0 := by
    rw [laplaceAt_evenPart, laplaceAt_reflection, neg_zero,
      hvalues (⟨0, by simp [pairNodeSet]⟩ :
        FiniteMellinNode (pairNodeSet rho)),
      pairNodeTarget_at_zero hrho]
    simp
  have hhalf : CompactLogTest.laplaceAt (evenPart h) (1 / 2 : ℂ) +
      CompactLogTest.laplaceAt (oddPart h) (1 / 2 : ℂ) = 0 := by
    rw [laplaceAt_evenPart, laplaceAt_oddPart, laplaceAt_reflection,
      hvalues (⟨1 / 2, by simp [pairNodeSet]⟩ :
        FiniteMellinNode (pairNodeSet rho)),
      pairNodeTarget_at_half hrho hoff,
      hvalues (⟨-(1 / 2 : ℂ), by simp [pairNodeSet]⟩ :
        FiniteMellinNode (pairNodeSet rho)),
      pairNodeTarget_at_neg_half hrho hoff]
    simp
  have hone : CompactLogTest.laplaceAt (evenPart h) 1 +
      CompactLogTest.laplaceAt (oddPart h) 1 = 0 := by
    rw [laplaceAt_evenPart, laplaceAt_oddPart, laplaceAt_reflection,
      hvalues (⟨1, by simp [pairNodeSet]⟩ :
        FiniteMellinNode (pairNodeSet rho)),
      pairNodeTarget_at_one hrho,
      hvalues (⟨-1, by simp [pairNodeSet]⟩ :
        FiniteMellinNode (pairNodeSet rho)),
      pairNodeTarget_at_neg_one hrho]
    simp
  have hdet : CompactLogTest.laplaceAt
      (sumTest (evenPart h) (oddPart h)) rho ≠ 0 := by
    intro hcontra
    rw [laplaceAt_sumTest, laplaceAt_evenPart, laplaceAt_oddPart,
      laplaceAt_reflection,
      hvalues (⟨rho, by simp [pairNodeSet]⟩ :
        FiniteMellinNode (pairNodeSet rho)),
      pairNodeTarget_at_rho rho,
      hvalues (⟨-rho, by simp [pairNodeSet]⟩ :
        FiniteMellinNode (pairNodeSet rho)),
      pairNodeTarget_at_neg_rho hrho0] at hcontra
    norm_num at hcontra
  have hsupp : Function.support (sumTest (evenPart h) (oddPart h)).test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) := by
    refine Set.Subset.trans (support_sumTest_subset (evenPart h) (oddPart h))
      (Set.union_subset ?_ ?_)
    · exact support_evenPart_subset_Icc h (Real.log 2 / 2) hwin
    · exact support_oddPart_subset_Icc h (Real.log 2 / 2) hwin
  exact ⟨evenPart h, oddPart h, heven, hodd, hf0, hhalf, hone, hdet, hsupp,
    fun hpos =>
      rootSupportedGate_of_evenBase_oddCorrection heven hodd hf0 hhalf hone
        hdet hsupp hpos⟩

end C1HealthyDetectorEvenOddPair
end Source
end ConnesWeilRH
