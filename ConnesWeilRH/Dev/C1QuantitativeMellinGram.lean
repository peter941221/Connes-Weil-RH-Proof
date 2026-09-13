/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1CompactLogL2Export
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# C1QuantitativeMellinGram - one-node quantitative interpolation lower bound

The existing finite Mellin interpolation engine is existential.  This leaf
starts the N2beta quantitative layer on the genuine `CompactLogTest` owner.
For one evaluation node it exports the exact diagonal Gram cost and proves
that every interpolant has at least that much squared L2 mass.  A strict
comparison with an independently supplied N1c budget is an honest no-go
certificate for that specified window, node, and budget only.

Design records: docs/map/009_n2beta_core_bone_completion_contract.md and
docs/proofs/1381_l2_export_and_lemma_a.md.
-/

namespace ConnesWeilRH
namespace Source
namespace C1QuantitativeMellinGram

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1CompactLogL2Export

/-- The diagonal finite-Gram weight for evaluation at `s` on the window
`(a, b)`.  It is deliberately an integral: the exact antiderivative and every
interval certificate can be supplied by an independent consumer. -/
noncomputable def oneNodeGramWeight (a b : ℝ) (s : ℂ) : ℝ :=
  ∫ x : ℝ in a..b, Real.exp (2 * s.re * x) ∂volume

/-- The minimum possible squared L2 cost forced by one prescribed Laplace
value, provided the diagonal Gram weight is positive. -/
noncomputable def oneNodeRequiredCost (a b : ℝ) (s y : ℂ) : ℝ :=
  ‖y‖ ^ 2 / oneNodeGramWeight a b s

/-- Data for one finite interpolation problem.  A `Finset` is the canonical
deduplicated node owner.  Positivity, invertibility, feasibility, and budget
claims intentionally remain outside this structure. -/
structure FiniteMellinInterpolationConfig where
  lower : ℝ
  upper : ℝ
  nodes : Finset ℂ
  target : {z : ℂ // z ∈ nodes} → ℂ
  baseFactor : {z : ℂ // z ∈ nodes} → ℂ

/-- The finite, already-deduplicated index type of a configuration. -/
abbrev FiniteMellinInterpolationConfig.Node (cfg : FiniteMellinInterpolationConfig) :=
  {z : ℂ // z ∈ cfg.nodes}

/-- The abstract finite Gram matrix of a supplied evaluation-representer
family.  The forthcoming analytic brick identifies these vectors with the
windowed Laplace representers; this definition deliberately does not claim
that identification yet. -/
noncomputable def finiteMellinGram {E : Type*} [Inner ℂ E]
    (cfg : FiniteMellinInterpolationConfig)
    (representer : cfg.Node → E) : Matrix cfg.Node cfg.Node ℂ :=
  Matrix.gram ℂ representer

/-- Every supplied representer family has a Hermitian Gram matrix. -/
theorem finiteMellinGram_isHermitian {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (cfg : FiniteMellinInterpolationConfig)
    (representer : cfg.Node → E) : (finiteMellinGram cfg representer).IsHermitian :=
  Matrix.isHermitian_gram ℂ representer

/-- The finite Gram quadratic expression is exactly the squared norm of the
corresponding representer combination.  This is the complex-Hilbert-space
positivity interface: unlike an ordered-matrix predicate, it has the correct
meaning over complex scalars. -/
theorem finiteMellinGram_quadratic_eq_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (cfg : FiniteMellinInterpolationConfig)
    (representer : cfg.Node → E) (coeff : cfg.Node → ℂ) :
    dotProduct (star coeff) (Matrix.mulVec (finiteMellinGram cfg representer) coeff) =
      @inner ℂ E _ (∑ i, coeff i • representer i) (∑ i, coeff i • representer i) := by
  simpa only [finiteMellinGram] using
    (Matrix.star_dotProduct_gram_mulVec (𝕜 := ℂ) representer coeff coeff)

/-- The real part of every finite complex Gram quadratic expression is
nonnegative.  It is the literal squared norm of the represented vector, so
this theorem does not impose an invalid order on `ℂ`. -/
theorem finiteMellinGram_quadratic_re_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (cfg : FiniteMellinInterpolationConfig)
    (representer : cfg.Node → E) (coeff : cfg.Node → ℂ) :
    0 ≤ (dotProduct (star coeff)
      (Matrix.mulVec (finiteMellinGram cfg representer) coeff)).re := by
  rw [finiteMellinGram_quadratic_eq_inner]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_nonneg _

/-- In the linearly independent branch, every nonzero coefficient vector has
strictly positive real Gram quadratic cost.  This is the valid complex
replacement for treating a Hermitian Gram matrix as an ordered real matrix. -/
theorem finiteMellinGram_quadratic_re_pos_of_linearIndependent {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (cfg : FiniteMellinInterpolationConfig) (representer : cfg.Node → E)
    (hli : LinearIndependent ℂ representer) (coeff : cfg.Node → ℂ)
    (hcoeff : coeff ≠ 0) :
    0 < (dotProduct (star coeff)
      (Matrix.mulVec (finiteMellinGram cfg representer) coeff)).re := by
  rw [finiteMellinGram_quadratic_eq_inner]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  apply sq_pos_of_ne_zero
  rw [norm_ne_zero_iff]
  rw [Fintype.linearIndependent_iff] at hli
  exact mt (hli coeff) (mt funext hcoeff)

/-- In the rank-deficient branch, an attainable target vector must vanish
against every left Gram-kernel vector.  This is only a compatibility
predicate: it deliberately does not assert feasibility or manufacture a
pseudoinverse. -/
def FiniteMellinKernelCompatible {E : Type*} [Inner ℂ E]
    (cfg : FiniteMellinInterpolationConfig) (representer : cfg.Node → E) : Prop :=
  ∀ coeff : cfg.Node → ℂ,
    Matrix.mulVec (finiteMellinGram cfg representer) coeff = 0 →
      dotProduct (star coeff) cfg.target = 0

/-- The finite normal equations for a target vector.  In the nonsingular
branch they have the usual inverse solution; in the singular branch this
predicate keeps solvability separate from any unjustified inverse. -/
def FiniteMellinGramSolvable {E : Type*} [Inner ℂ E]
    (cfg : FiniteMellinInterpolationConfig) (representer : cfg.Node → E) : Prop :=
  ∃ coeff : cfg.Node → ℂ,
    Matrix.mulVec (finiteMellinGram cfg representer) coeff = cfg.target

/-- Solvability of the finite normal equations forces the target to pass the
kernel-compatibility test. -/
theorem FiniteMellinGramSolvable.kernelCompatible {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (cfg : FiniteMellinInterpolationConfig) (representer : cfg.Node → E)
    (hsolvable : FiniteMellinGramSolvable cfg representer) :
    FiniteMellinKernelCompatible cfg representer := by
  intro kernel hkernel
  obtain ⟨coeff, hcoeff⟩ := hsolvable
  have hself :
      dotProduct (star kernel)
        (Matrix.mulVec (finiteMellinGram cfg representer) kernel) = 0 := by
    simp [hkernel]
  have hinner :
      @inner ℂ E _ (∑ i, kernel i • representer i)
        (∑ i, kernel i • representer i) = 0 := by
    rw [← finiteMellinGram_quadratic_eq_inner]
    exact hself
  have hsum : (∑ i, kernel i • representer i) = 0 :=
    inner_self_eq_zero.mp hinner
  rw [← hcoeff]
  calc
    dotProduct (star kernel)
        (Matrix.mulVec (finiteMellinGram cfg representer) coeff) =
        @inner ℂ E _ (∑ i, kernel i • representer i)
          (∑ i, coeff i • representer i) := by
      simpa only [finiteMellinGram] using
        (Matrix.star_dotProduct_gram_mulVec (𝕜 := ℂ) representer kernel coeff)
    _ = 0 := by
      rw [hsum]
      exact inner_zero_left _

/-- The Hilbert-space vector synthesized from finite Gram coefficients. -/
noncomputable def finiteMellinSynthesis {E : Type*} [AddCommMonoid E] [Module ℂ E]
    {cfg : FiniteMellinInterpolationConfig} (representer : cfg.Node → E)
    (coeff : cfg.Node → ℂ) : E :=
  ∑ i, coeff i • representer i

/-- A vector realizes the target finite moments, with the convention that the
inner product is linear in its second argument. -/
def FiniteMellinMomentMatches {E : Type*} [Inner ℂ E]
    (cfg : FiniteMellinInterpolationConfig) (representer : cfg.Node → E)
    (x : E) : Prop :=
  ∀ i, @inner ℂ E _ (representer i) x = cfg.target i

/-- A Gram matrix-vector product is exactly the moment vector of the
corresponding synthesized Hilbert vector. -/
theorem finiteMellinGram_mulVec_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (cfg : FiniteMellinInterpolationConfig)
    (representer : cfg.Node → E) (coeff : cfg.Node → ℂ) (i : cfg.Node) :
    Matrix.mulVec (finiteMellinGram cfg representer) coeff i =
      @inner ℂ E _ (representer i) (finiteMellinSynthesis representer coeff) := by
  classical
  -- This Mathlib `dotProduct` is plain bilinear (no hidden `star`), and the
  -- inner product is linear in its second argument (`inner_smul_right` has no
  -- conjugation).  The proof stays inside `calc` with explicit `Finset.sum`
  -- congruences: `rw` pattern matching is capture-sensitive when a summation
  -- bound variable shadows the free node index.
  simp only [finiteMellinGram, finiteMellinSynthesis, Matrix.mulVec, dotProduct,
    Matrix.gram_apply]
  -- A `trans` chain, not `calc`: the calc step parser fights the `∑ x, ...`
  -- binder comma and the nested `by` indentation.  Each intermediate identity
  -- is an explicit `Finset.sum` congruence, so no `rw` ever matches under a
  -- binder that shadows the free node index.
  trans (∑ x, coeff x * inner ℂ (representer i) (representer x))
  · apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm]
  trans (∑ x, inner ℂ (representer i) (coeff x • representer x))
  · apply Finset.sum_congr rfl
    intro x _
    rw [inner_smul_right]
  exact (inner_sum Finset.univ (fun x => coeff x • representer x)
    (representer i)).symm

/-- Any coefficient vector solving the finite normal equations synthesizes a
Hilbert vector that realizes exactly the target moments.  This converts the
algebraic predicate `FiniteMellinGramSolvable` into the analytic matching
relation consumed by the minimum-norm theorem below. -/
theorem finiteMellinSynthesis_momentMatches_of_isSolution {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (cfg : FiniteMellinInterpolationConfig)
    (representer : cfg.Node → E) (coeff : cfg.Node → ℂ)
    (hsolution : Matrix.mulVec (finiteMellinGram cfg representer) coeff = cfg.target) :
    FiniteMellinMomentMatches cfg representer (finiteMellinSynthesis representer coeff) := by
  intro i
  have hpoint := congr_fun hsolution i
  exact (finiteMellinGram_mulVec_apply cfg representer coeff i).symm.trans hpoint

/-- Abstract minimum-norm certificate.  If the finite normal equations are
solved by `coeff`, then the synthesized Hilbert vector has squared norm at
most the squared norm of every vector realizing the same target moments:
the cross inner product collapses to `‖synthesis‖²`, and Pythagoras
(`norm_sub_sq`) leaves a nonnegative square.  Later L2 consumers export this
as the CompactLogTest interpolation cost lower bound; it is the mechanism
that replaces the purely existential correction engine. -/
theorem norm_sq_finiteMellinSynthesis_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (cfg : FiniteMellinInterpolationConfig)
    (representer : cfg.Node → E) (coeff : cfg.Node → ℂ) (y : E)
    (hy : FiniteMellinMomentMatches cfg representer y)
    (hsolution : Matrix.mulVec (finiteMellinGram cfg representer) coeff = cfg.target) :
    ‖finiteMellinSynthesis representer coeff‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  classical
  -- The matching hypothesis must be exposed as a plain `∀`: `simp` will not
  -- unfold the `FiniteMellinMomentMatches` wrapper on its own.
  have hys : ∀ i, @inner ℂ E _ (representer i) y = cfg.target i := hy
  have hcross :
      @inner ℂ E _ (finiteMellinSynthesis representer coeff) y
        = dotProduct (star coeff) cfg.target := by
    simp only [finiteMellinSynthesis]
    rw [sum_inner]
    simp [inner_smul_left, hys, dotProduct]
  have hnorm :
      dotProduct (star coeff) cfg.target
        = (‖finiteMellinSynthesis representer coeff‖ : ℂ) ^ 2 := by
    rw [← hsolution, finiteMellinGram_quadratic_eq_inner,
      inner_self_eq_norm_sq_to_K]
    rfl
  have hcrossz :
      @inner ℂ E _ (finiteMellinSynthesis representer coeff) y
        = (‖finiteMellinSynthesis representer coeff‖ : ℂ) ^ 2 := by
    rw [hcross, hnorm]
  -- The field parameter of `norm_sub_sq` is not determined by the two vectors
  -- (a complex space is also a real one), so it is annotated explicitly.
  have hpyth := norm_sub_sq (𝕜 := ℂ) (finiteMellinSynthesis representer coeff) y
  rw [hcrossz] at hpyth
  have hre : RCLike.re ((‖finiteMellinSynthesis representer coeff‖ : ℂ) ^ 2)
      = ‖finiteMellinSynthesis representer coeff‖ ^ 2 :=
    (congrArg (fun z : ℂ => RCLike.re z)
      (RCLike.ofReal_pow ‖finiteMellinSynthesis representer coeff‖ 2).symm).trans
      (RCLike.ofReal_re _)
  have hnonneg : 0 ≤ ‖finiteMellinSynthesis representer coeff - y‖ ^ 2 := sq_nonneg _
  linarith

/-- The correction value required to obtain the assembled target when the
base factor is nonzero. -/
noncomputable def FiniteMellinInterpolationConfig.correctionTarget
    (cfg : FiniteMellinInterpolationConfig) : {z : ℂ // z ∈ cfg.nodes} → ℂ :=
  fun z => cfg.target z / cfg.baseFactor z

/-- The target/base-factor division is exact at every node whose base factor
is nonzero.  This is the algebraic interface used by the existing full-product
Laplace readback. -/
theorem FiniteMellinInterpolationConfig.correctionTarget_mul_baseFactor
    (cfg : FiniteMellinInterpolationConfig) (z : {z : ℂ // z ∈ cfg.nodes})
    (hbase : cfg.baseFactor z ≠ 0) :
    cfg.correctionTarget z * cfg.baseFactor z = cfg.target z := by
  simpa only [FiniteMellinInterpolationConfig.correctionTarget] using
    div_mul_cancel₀ (cfg.target z) hbase

/-- A zero base factor cannot realize a nonzero assembled target, regardless
of the chosen correction.  This is a scoped algebraic no-go, not a claim about
other bases, node sets, or detector families. -/
theorem FiniteMellinInterpolationConfig.no_correction_of_baseFactor_zero
    (cfg : FiniteMellinInterpolationConfig) (z : {z : ℂ // z ∈ cfg.nodes})
    (hbase : cfg.baseFactor z = 0) (htarget : cfg.target z ≠ 0) :
    ¬ ∃ correction : ℂ, cfg.baseFactor z * correction = cfg.target z := by
  intro h
  obtain ⟨correction, hcorrection⟩ := h
  rw [hbase, zero_mul] at hcorrection
  exact htarget hcorrection.symm

/-- On the critical line the diagonal Gram weight is exactly the window
width.  This is the first exact, symbolic regime certificate; it contains no
floating-point parameter or sampled zero. -/
theorem oneNodeGramWeight_eq_width_of_re_zero (a b : ℝ) (s : ℂ)
    (hs : s.re = 0) : oneNodeGramWeight a b s = b - a := by
  simp [oneNodeGramWeight, hs]

/-- The exact critical-line diagonal weight is positive on a nonempty
window. -/
theorem oneNodeGramWeight_pos_of_re_zero {a b : ℝ} (hab : a < b) (s : ℂ)
    (hs : s.re = 0) : 0 < oneNodeGramWeight a b s := by
  rw [oneNodeGramWeight_eq_width_of_re_zero a b s hs]
  linarith

/-- Every compact-log interpolant with a prescribed value at one node pays at
least the diagonal Gram cost.  Positivity of the exact window weight is an
explicit analytic premise, not stored source data. -/
theorem oneNodeRequiredCost_le_compactLogL2sq (f : CompactLogTest) {a b : ℝ}
    (hab : a < b) (hsupp : Function.support f.test ⊆ Set.Ioo a b) (s y : ℂ)
    (hvalue : laplaceAt f s = y) (hweight : 0 < oneNodeGramWeight a b s) :
    oneNodeRequiredCost a b s y ≤ compactLogL2sq f := by
  unfold oneNodeRequiredCost
  rw [div_le_iff₀ hweight]
  have heval := laplaceAt_sq_le f hab hsupp s
  rw [hvalue] at heval
  simpa only [oneNodeGramWeight, mul_comm] using heval

/-- A strict lower-cost/upper-budget clash is a formal no-go certificate for
the stated one-node interpolation problem.  It says nothing about other
windows, nodes, detector families, or the B5 route. -/
theorem oneNode_noGo_of_budget_lt_requiredCost (f : CompactLogTest) {a b : ℝ}
    (hab : a < b) (hsupp : Function.support f.test ⊆ Set.Ioo a b) (s y : ℂ)
    (hvalue : laplaceAt f s = y) (hweight : 0 < oneNodeGramWeight a b s)
    (budget : ℝ) (hbudget : compactLogL2sq f ≤ budget)
    (hgap : budget < oneNodeRequiredCost a b s y) : False := by
  have hcost := oneNodeRequiredCost_le_compactLogL2sq f hab hsupp s y hvalue hweight
  linarith

/-- An explicitly scoped no-go predicate for exact regime certificates. -/
def OneNodeBudgetNoGo (a b budget : ℝ) (s y : ℂ) : Prop :=
  budget < oneNodeRequiredCost a b s y

/-- The predicate form is consumed only through the same one-node theorem;
it cannot manufacture a no-go without a value, support, and positive-weight
proof for the actual `CompactLogTest`. -/
theorem oneNode_noGo_of_regime (f : CompactLogTest) {a b budget : ℝ} (s y : ℂ)
    (hab : a < b) (hsupp : Function.support f.test ⊆ Set.Ioo a b)
    (hvalue : laplaceAt f s = y) (hweight : 0 < oneNodeGramWeight a b s)
    (hbudget : compactLogL2sq f ≤ budget)
    (hregime : OneNodeBudgetNoGo a b budget s y) : False := by
  exact oneNode_noGo_of_budget_lt_requiredCost f hab hsupp s y hvalue hweight
    budget hbudget hregime

end C1QuantitativeMellinGram
end Source
end ConnesWeilRH
