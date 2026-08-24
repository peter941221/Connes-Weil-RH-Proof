/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1PositiveTraceCutoffGrowth
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Source.CC20Concrete.GlobalLogConvolution
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Source.CC20YoshidaConvolution
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# C1 Stage-3 bare Hilbert--Schmidt obstruction

The Stage-3 frontier currently assumes that the whole-line convolution factor
`F_g = cc20GlobalLogConvolution g.involution.test` is Hilbert--Schmidt.  This
file closes that assumption in the only honest direction available here:
for every nonzero compact-log test, the assumption is contradictory.

The proof uses one fixed owner throughout:

```text
bare convolution
  -> finite output restriction/zero-extension
  -> cutoff positive square
  -> exact cutoff trace growth
```

The restriction and zero-extension are contractions, so a bare Hilbert--Schmidt
bound would give a uniform upper bound for every cutoff square.  The existing
cutoff readback gives a strictly growing lower bound, hence contradiction.

No RH statement is made here.  This is a diagnostic/obstruction theorem for
the bare FRONTIER-HS premise; a windowed or renormalized owner remains a
separate analytic problem.

## Step② (FRONTIER-CRUX) as a theorem, not an axiom

The last section of this file discharges the second named Stage-3 analytic
lemma — the readback `∑' ‖F_g e_i‖² = qw g` — directly from the bare
obstruction.  The per-test Hilbert--Schmidt premise already forces
`g.test = 0`; at that zero test both sides of the readback vanish, so the
identity holds without any independent power-spectrum axiom.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3BareHSObstruction

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedCrossingOperatorBridge
open Dev.C1PositiveTraceCutoffAdapter
open Dev.C1PositiveTraceWindowProducer
open Dev.C1PositiveTraceCutoffGrowth
open Dev.Wall14Plateau
open Filter
open scoped InnerProduct InnerProductSpace Topology BigOperators ENNReal Classical FourierTransform

noncomputable section

variable {nu : Type*}
variable (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)

/-- The concrete Stage-3 self-pair factor `F_g = cc20GlobalLogConvolution (g.involution.test)`, defined locally so
this module owns the bare obstruction **without importing the crux module** — that is what breaks their import cycle.
It is definitionally equal to `C1Stage3FrontierCrux.stage3FamilyFactor` (identical body, separate declaration), so a
Hilbert--Schmidt hypothesis stated on one discharges on the other. -/
noncomputable def stage3FamilyFactor (g : CompactLogTest) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20GlobalLogConvolution g.involution.test

/-! ## The finite cutoff postcomposition is a contraction -/

theorem norm_cutoffWindowPostcomp_le_one
    (g : CompactLogTest) (n : Nat) :
    ‖(fullBoundaryOutputZeroExtension (cutoffLower g n) (cutoffUpper g n)) ∘L
        globalL2ToKernelInterval (-cutoffUpper g n) (-cutoffLower g n) 0‖ ≤ 1 := by
  let a : ℝ := cutoffLower g n
  let c : ℝ := cutoffUpper g n
  let restriction := globalL2ToKernelInterval (-c) (-a) 0
  let extension := fullBoundaryOutputZeroExtension a c
  have hrestriction : ‖restriction‖ ≤ 1 := by
    rw [← ContinuousLinearMap.adjoint.norm_map]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    rw [norm_globalL2ToKernelInterval_adjoint_apply]
    simp
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖extension (restriction u)‖ ≤ 1 * ‖u‖
  have hextension : ‖extension (restriction u)‖ = ‖restriction u‖ := by
    simpa only [extension, fullBoundaryOutputZeroExtension]
      using norm_kernelIntervalL2ZeroExtension (-c) (-a) 0 (restriction u)
  rw [hextension]
  calc
    ‖restriction u‖ ≤ ‖restriction‖ * ‖u‖ := restriction.le_opNorm u
    _ ≤ 1 * ‖u‖ := by gcongr

/-! ## The cutoff operator has the same owner as a postcomposed bare factor -/

theorem cutoffPositiveBasisData_operator_eq_postcomp
    (g : CompactLogTest) (n : Nat) :
    (cutoffPositiveBasisData g globalBasis n).operator =
      ((fullBoundaryOutputZeroExtension (cutoffLower g n) (cutoffUpper g n)) ∘L
        globalL2ToKernelInterval (-cutoffUpper g n) (-cutoffLower g n) 0) ∘L
        stage3FamilyFactor g := by
  change fullBoundaryPositiveOperator g (cutoffLower g n) (cutoffUpper g n) = _
  unfold fullBoundaryPositiveOperator
  rw [fullBoundaryRootFactor_eq_globalConvolution g
    (cutoffLower g n) (cutoffUpper g n)
    (support_subset_cutoffWindow g n)]
  rfl

/-! ## Bare HS gives a uniform bound for every cutoff energy -/

theorem cutoffEnergy_le_bareHS_mass
    (g : CompactLogTest)
    (hHS : Summable (fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2))
    (n : Nat) :
    ∑' i, ‖(cutoffPositiveBasisData g globalBasis n).operator
        (globalBasis i)‖ ^ 2 ≤
      ∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 := by
  let bounded : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
    fullBoundaryOutputZeroExtension (cutoffLower g n) (cutoffUpper g n) ∘L
      globalL2ToKernelInterval (-cutoffUpper g n) (-cutoffLower g n) 0
  have hbounded : ‖bounded‖ ≤ 1 := by
    simpa only [bounded] using norm_cutoffWindowPostcomp_le_one g n
  have hpost : Summable (fun i =>
      ‖(bounded ∘L stage3FamilyFactor g) (globalBasis i)‖ ^ 2) :=
    summable_normSq_postcomp globalBasis (stage3FamilyFactor g) bounded hHS
  have hle : ∀ i,
      ‖(bounded ∘L stage3FamilyFactor g) (globalBasis i)‖ ^ 2 ≤
        ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 := by
    intro i
    rw [ContinuousLinearMap.comp_apply]
    calc
      ‖bounded (stage3FamilyFactor g (globalBasis i))‖ ^ 2 ≤
          (‖bounded‖ * ‖stage3FamilyFactor g (globalBasis i)‖) ^ 2 := by
        gcongr
        exact bounded.le_opNorm _
      _ ≤ (1 * ‖stage3FamilyFactor g (globalBasis i)‖) ^ 2 := by
        gcongr
      _ = ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 := by ring
  have hsum :
      (∑' i, ‖(bounded ∘L stage3FamilyFactor g) (globalBasis i)‖ ^ 2) ≤
        ∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 :=
    hpost.tsum_le_tsum hle hHS
  rw [cutoffPositiveBasisData_operator_eq_postcomp globalBasis g n]
  exact hsum

/-! ## The bare premise is impossible for every nonzero test -/

theorem not_bare_hilbertSchmidt_of_test_ne_zero
    (g : CompactLogTest)
    (hg : g.test ≠ 0) :
    ¬ Summable (fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) := by
  intro hHS
  let boundValue : ℝ := ∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2
  obtain ⟨n, hn⟩ :=
    cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero
      g globalBasis hg boundValue
  have henergy := cutoffEnergy_le_bareHS_mass globalBasis g hHS n
  have htraceMass :
      (ordinaryTraceAlong globalBasis
        (cutoffPositiveBasisData g globalBasis n).positiveComposition).re =
        ∑' i, ‖(cutoffPositiveBasisData g globalBasis n).operator
          (globalBasis i)‖ ^ 2 := by
    rw [BasisHilbertSchmidtData.ordinaryTrace_positiveComposition]
    norm_cast
  rw [htraceMass] at hn
  exact (not_lt_of_ge henergy) (by simpa [boundValue] using hn)

/-! ## The universal FRONTIER-HS premise is therefore false -/

theorem not_forall_bare_hilbertSchmidt :
    ¬ (∀ g : CompactLogTest,
      Summable (fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2)) := by
  intro hAll
  exact not_bare_hilbertSchmidt_of_test_ne_zero globalBasis
    Dev.Wall14Plateau.bumpPlateauTest Dev.Wall14Plateau.bumpPlateauTest_ne_zero
    (hAll Dev.Wall14Plateau.bumpPlateauTest)

/-! ## The bare FRONTIER-CRUX premise only survives at the zero test -/

/-- **Route-kill for the bare detector.** The per-test Hilbert–Schmidt premise of the concrete bare
FRONTIER-CRUX readback forces the test to be trivial.  This is the contrapositive content of
`not_bare_hilbertSchmidt_of_test_ne_zero`: for a fixed compact-log test, if its whole-line convolution
factor `stage3FamilyFactor g = cc20GlobalLogConvolution g.involution.test` is assumed Hilbert–Schmidt
(summable diagonal norm squares in an orthonormal basis), then the test must vanish identically.

Consequence: the step② readback `C1Stage3FrontierCrux.frontierCrux_powerSpectrum_eq_weilValue` — whose own premise is
exactly this per-test summability, and which is discharged below precisely from it — reduces to the zero test, where both
the Hilbert–Schmidt mass and `qw g` are `0`.  Every **nontrivial** detector readback therefore has to pass through a
windowed or renormalized owner (the cutoff `C† K C` projection route), not the bare factor. -/
theorem hsPremise_forces_zero_test (g : CompactLogTest)
    (hHS : Summable fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) :
    g.test = 0 := by
  by_contra hgzero
  exact not_bare_hilbertSchmidt_of_test_ne_zero globalBasis g hgzero hHS

/-! ## Step② is discharged by the bare obstruction (the readback is not an independent axiom) -/

/-- The involution test of a zero compact-log test is pointwise zero (`f*(x) = conj (f(-x))`). -/
theorem stage3Involution_test_pointwise_zero_of_test_zero (g : CompactLogTest)
    (hzero : g.test = 0) (x : ℝ) : ((g.involution).test : ℝ → ℂ) x = 0 := by
  have hfn : (g.test : ℝ → ℂ) = (fun _ => 0) := funext fun y => by
    simpa using congrArg (fun t : TestFunction => (t : ℝ → ℂ) y) hzero
  rw [CCM25Concrete.CompactLogConvolution.CompactLogTest.involution_apply, hfn]
  simp

/-- The half-density square of a zero compact-log test is pointwise zero. -/
theorem stage3ConvolutionSquare_test_pointwise_zero_of_test_zero (g : CompactLogTest)
    (hzero : g.test = 0) (x : ℝ) : ((g.convolutionSquare).test : ℝ → ℂ) x = 0 := by
  rw [CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_apply]
  have hfn : (g.test : ℝ → ℂ) = (fun _ => 0) := funext fun y => by
    simpa using congrArg (fun t : TestFunction => (t : ℝ → ℂ) y) hzero
  simp [hfn]

/-- For a zero compact-log test the Fourier-multiplier symbol of `stage3FamilyFactor g` is the
pointwise-zero function, so its bounded (top-exponent) multiplier element is the zero in `Lp ℂ ⊤`. -/
theorem stage3Multiplier_toLpTop_zero_of_test_zero (g : CompactLogTest)
    (hzero : g.test = 0) :
    ((FourierTransform.fourier (g.involution.test)).toLp ⊤) = 0 := by
  -- the involution test is pointwise zero, so its Schwartz-map form is the zero map.
  have hswz : ((g.involution.test) : SchwartzMap ℝ ℂ) = 0 := by
    ext x
    simpa using stage3Involution_test_pointwise_zero_of_test_zero g hzero x
  -- 𝓕 of that (coerced) inv test is the zero Schwartz map; an Lp element of a pointwise-zero
  -- Schwartz map is the zero element — after unfolding `SchwartzMap.toLp` to `(f.memLp p μ).toLp`,
  -- its function argument is definitionally `0` (`SchwartzMap.coeFn_zero` is rfl), so the simp lemma
  -- `MemLp.toLp_zero` closes it.
  have hfz : (FourierTransform.fourier (g.involution.test)) = (0 : SchwartzMap ℝ ℂ) := by
    rw [hswz]
    exact FourierTransform.fourier_zero
  rw [hfz]
  · simp [SchwartzMap.toLp]

/-- A zero compact-log test makes the Stage-3 self-pair factor `F_g` the zero operator on `L²(ℝ)`. -/
theorem stage3FamilyFactor_zero_of_test_zero (g : CompactLogTest) (hzero : g.test = 0) :
    stage3FamilyFactor g = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  dsimp only [stage3FamilyFactor]
  rw [cc20GlobalLogConvolution_apply, cc20FourierMultiplier_apply]
  -- goal: 𝓕⁻ (((𝓕h).toLp ⊤) • (𝓕 u)) = 0 u   with h := g.involution.test : 𝓢.
  have hmult : ((FourierTransform.fourier (g.involution.test)).toLp ⊤) = 0 :=
    stage3Multiplier_toLpTop_zero_of_test_zero g hzero
  rw [hmult]   -- goal: Zinv ((0 : L^inf) • Zu) = 0 u; left operand of the product is the zero of Lp C top volume.
  · simp   -- Lp.zero_smul + LinearMap.zero_apply (both @[simp]) reduce both sides to the zero of L2.

/-- A zero compact-log test has Weil value `qw g = 0`: every component of `psi` reads pointwise values
and integrals of the (pointwise-zero) half-density square, hence vanishes. -/
theorem qw_zero_of_test_zero (g : CompactLogTest) (hzero : g.test = 0) :
    C1SameOwnerWeil.qw g = 0 := by
  let F : CompactLogTest := g.convolutionSquare
  have hFzero : ∀ x : ℝ, F.test x = 0 := fun x =>
    stage3ConvolutionSquare_test_pointwise_zero_of_test_zero g hzero x
  -- pole term: each bilateral Laplace integral is the integral of a pointwise-zero function.
  have hpole : C1SameOwnerWeil.poleTerm F = 0 := by
    unfold C1SameOwnerWeil.poleTerm
    have hzeroLap (s : ℂ) : CC20YoshidaConvolution.CompactLogTest.laplaceAt F s = 0 := by
      unfold CC20YoshidaConvolution.CompactLogTest.laplaceAt
      have hintegrandZero :
          (fun x : ℝ => (CC20YoshidaConvolution.CompactLogTest.exponentialWeight F s).test x) = fun _ => 0 := by
        ext x
        rw [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply, hFzero]
        simp
      rw [hintegrandZero]
      simp
    simp only [hzeroLap (1 / 2), hzeroLap (-1 / 2)]
    norm_num
  -- archimedean term: constant part reads F.test 0; integrand numerator reads pointwise values.
  have hpt : ∀ y, C1SameOwnerWeil.archimedeanIntegrand F y = 0 := by
    intro y
    unfold C1SameOwnerWeil.archimedeanIntegrand
    have hnum : C1SameOwnerWeil.archimedeanNumerator F y = 0 := by
      unfold C1SameOwnerWeil.archimedeanNumerator
      simp [hFzero]
    rw [hnum]
    norm_num
  have harch : C1SameOwnerWeil.archimedeanTerm F = 0 := by
    unfold C1SameOwnerWeil.archimedeanTerm
    have hintegZero : ∫ y in Set.Ioi (0 : Real), C1SameOwnerWeil.archimedeanIntegrand F y = 0 := by
      have hfn : (fun y => C1SameOwnerWeil.archimedeanIntegrand F y) = fun _ => 0 := funext hpt
      rw [hfn]
      simp
    have hconstZero :
        ((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : ℂ) * F.test 0 = 0 := by
      simp [hFzero]
    rw [hintegZero, hconstZero]
    norm_num
  -- finite-prime sum: every visible term reads F.test (log n) + F.test (-log n), all zero.
  have hfprime : C1SameOwnerWeil.finitePrimeSum F = 0 := by
    unfold C1SameOwnerWeil.finitePrimeSum
    apply Finset.sum_eq_zero
    intro n hn
    simp [C1SameOwnerWeil.finitePrimeTerm, C1SameOwnerWeil.finitePrimeTermComplex, hFzero]
  rw [C1SameOwnerWeil.qw_eq_psi_square, C1SameOwnerWeil.psi_eq_components]
  rw [hpole, harch, hfprime]
  norm_num

/-! ## The bare FRONTIER-HS premise holds exactly at the zero test -/

/-- **The obstruction in one line.** On the concrete *bare* self-pair factor
`stage3FamilyFactor g = cc20GlobalLogConvolution (g.involution.test)`, per-test Hilbert--Schmidt
summability `Summable (i => ‖F_g (basis i)‖²)` holds **iff** the test is trivial:

  * forward — `hsPremise_forces_zero_test`: a nonzero compact-log test has an unbounded
    cutoff-trace lower bound that no bare HS mass can uniformly upper-bound, so HS forces `g.test = 0`;
  * reverse — at `g.test = 0` the factor is the zero operator (`stage3FamilyFactor_zero_of_test_zero`)
    and every diagonal norm square is `0`, a summable series.

Route consequence: Route B's closure consumes a **uniform-in-`g`** premise `∀ g, Summable …`. On the bare
owner that universal is already refuted by one nonzero witness (`not_forall_bare_hilbertSchmidt`, via the
explicit plateau test), so every *nontrivial* detector readback must pass through a windowed or renormalized
factor (where `C1Stage3FrontierHS` supplies HS) — not the bare convolution. -/
theorem bareHS_iff_zero_test (g : CompactLogTest) :
    Summable (fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) ↔ g.test = 0 := by
  constructor
  · exact hsPremise_forces_zero_test globalBasis g
  · intro hzero
    have hfz : stage3FamilyFactor g = 0 := stage3FamilyFactor_zero_of_test_zero g hzero
    -- pointwise-zero diagonal at the zero test (same idiom as `frontierCrux_step2_powerSpectrum_eq_weilValue`).
    have hterm : ∀ i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 = 0 := fun i => by
      rw [show stage3FamilyFactor g (globalBasis i) = 0 from by rw [hfz]; simp]
      norm_num
    have hfzfn : (fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) = fun _ => 0 :=
      funext hterm
    rw [hfzfn]
    exact summable_zero   -- a constant-zero series is summable over any index type.

-- Axiom-cleanliness audit: the iff reuses only existing obstruction lemmas, so `#print axioms` reports
-- exactly the three ambient axioms (no self-root, no `sorryAx`).
#print axioms bareHS_iff_zero_test

/-! ## The main theorem — step② follows from the bare obstruction alone -/

/-- **Step② as a theorem (not an axiom).** Under the per-test Hilbert–Schmidt premise `hHS`, the
bare obstruction forces `g.test = 0`; at that zero test both sides of the readback vanish, so the
power-spectrum mass equals `qw g`.  This discharges FRONTIER-CRUX's root assumption on exactly the
inputs its own hypothesis allows. -/
theorem frontierCrux_step2_powerSpectrum_eq_weilValue (g : CompactLogTest)
    (hHS : Summable fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) :
    ∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 = C1SameOwnerWeil.qw g := by
  have hzero : g.test = 0 := hsPremise_forces_zero_test globalBasis g hHS
  have hfz : stage3FamilyFactor g = 0 := stage3FamilyFactor_zero_of_test_zero g hzero
  -- LHS: every term is the norm square of `0 (basis i)`, hence each term is `0`; summable, so tsum `= 0`.
  have hlhs : ∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 = 0 := by
    have hterm : ∀ i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 = 0 := fun i => by
      rw [show stage3FamilyFactor g (globalBasis i) = 0 from by rw [hfz]; simp]
      norm_num
    have hfzfn : (fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) = fun _ => 0 :=
      funext hterm
    rw [hfzfn]
    simp
  -- RHS: qw g = 0 at the zero test.
  have hrhs : C1SameOwnerWeil.qw g = 0 := qw_zero_of_test_zero g hzero
  rw [hlhs, hrhs]

end
end C1Stage3BareHSObstruction
end Source
end ConnesWeilRH
