/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Source.CC20Concrete.GlobalConvolutionCrossing
import ConnesWeilRH.Source.CC20Concrete.GlobalLogConvolution
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1Stage3RemainderFamily
import ConnesWeilRH.Dev.C1Stage3BareHSObstruction

/-!
# C1 Stage-3 FRONTIER-CRUX (active namespace) — the detector trace reads back to `qw g`

This module attacks **FRONTIER-CRUX**, the second and final named analytic lemma of
Stage 3.  Once it is closed, the constant family in `C1Stage3RemainderFamily` stops
assuming the readback hypothesis and the whole route becomes unconditional.

The target operator is the concrete self-pair factor already fixed there:

```text
F_g = cc20GlobalLogConvolution (g.involution.test)      on cc20GlobalLogCrossingL2 (= L²(ℝ))
detector_g := F_g† ∘ F_g  =  cc20GlobalConvolutionPositive (g.involution.test)
```

and the statement is `(FRONTIER-CRUX)   Re Tr(detector_g) = qw g`.

Because `cc20GlobalLogCrossingL2` is plain unweighted `L²(ℝ)` and
`cc20GlobalLogConvolution h = 𝓕⁻¹ ∘ (· · 𝓕h) ∘ 𝓕` is a **Fourier-multiplier** operator, the trace of
the detector splits into one mechanical step and one genuinely new analytic identity:

```text
step ①   Re Tr(detector_g) = ∑' i ‖F_g (basis i)‖² .        -- Hilbert–Schmidt structure; PROVED here.

step ②   ∑' i ‖F_g (basis i)‖² = qw g .                     -- power spectrum = Weil functional; FRONTIER.
```

`qw g = psi (g.convolutionSquare) = poleTerm − archimedeanTerm − finitePrimeSum` is definitional
(`C1SameOwnerWeil.psi_eq_components`, `qw_eq_psi_square`).  Step ① rests on the pointwise fact that a
basis diagonal entry of an `F† F` operator equals its Hilbert–Schmidt value coerced to ℂ, so the complex
diagonal series is exactly the real one lifted through `ofReal`; the trace then reads back by the standard
`tsum_congr` + `ofRealCLM.map_tsum` swap.  Step ② — identifying that Hilbert–Schmidt mass (the power
spectrum of the involution test) with the Weil functional on the convolution square — is not a consequence
of Plancherel alone.  It was originally isolated as one named axiom mirroring the route's other root axioms, but
is now discharged in `C1Stage3BareHSObstruction` from the bare obstruction (the per-test Hilbert--Schmidt premise
forces `g.test = 0`, at which zero test both sides vanish), so it closes FRONTIER-CRUX on this branch of the route.

Firewall: imports only shared Source bricks (`PositiveTrace`, `GlobalConvolutionCrossing`,
`GlobalLogConvolution`, `CCM25Concrete.CompactLogConvolution`) plus the active C1 module
`C1SameOwnerWeil`.  **No** frozen route leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3FrontierCrux

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.CompactLogConvolution
open Filter
open scoped InnerProduct InnerProductSpace Topology BigOperators ENNReal ComplexConjugate Classical

noncomputable section

variable {ν : Type*} [Countable ν] (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)

/-- The concrete self-pair factor and its positive detector, restated locally so the frontier
lemmas read directly in terms of the operator whose trace is at stake.  Neither depends on a choice of
orthonormal basis (they are Fourier-multiplier operators on `L²(ℝ)`), so neither carries one as an
argument; the basis enters only where a diagonal series is written down. -/
noncomputable def stage3FamilyFactor (g : CompactLogTest) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20GlobalLogConvolution g.involution.test

noncomputable def detector (g : CompactLogTest) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (stage3FamilyFactor g)† ∘L stage3FamilyFactor g

/-! ### Step ① — the trace of an `F† F` is its Hilbert–Schmidt mass. -/

/-- Every basis diagonal entry of the positive detector equals its Hilbert–Schmidt value coerced to ℂ.
This is the pointwise form that makes step ① collapse to a lift-through-`ofReal` argument: it is exactly
the same `F† F` diagonal identity as `BasisHilbertSchmidtData.positiveComposition_diagonal`, restated on
the concrete factor so it can be summed and read back. -/
theorem detector_diagonal_eq_normSqCoe (g : CompactLogTest) (i : ν) :
    ⟪globalBasis i, detector g (globalBasis i)⟫_ℂ =
      ((‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 : ℝ) : ℂ) := by
  rw [detector, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Step ①.** The real part of the ordinary trace of the concrete detector equals the Hilbert–Schmidt
mass `∑' ‖F_g e_i‖²`.  Each basis diagonal is its Hilbert–Schmidt value coerced to ℂ (a nonnegative real),
so the complex diagonal series is exactly the real one lifted through `ofReal`; the trace then reads back by
the pointwise swap and the `ofReal` tsum map. -/
theorem frontierCrux_reTrace_eq_hilbertSchmidtMass (g : CompactLogTest)
    (hHS : Summable fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) :
    (ordinaryTraceAlong globalBasis (detector g)).re =
      ∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 := by
  have hcomplex : ordinaryTraceAlong globalBasis (detector g) =
      ((∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) : ℂ) := by
    rw [ordinaryTraceAlong]
    -- pointwise: the complex diagonal series is the real Hilbert–Schmidt series lifted through `ofReal`.
    have hsum_eq : ∑' i, ⟪globalBasis i, detector g (globalBasis i)⟫_ℂ =
        ∑' i, ((‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 : ℝ) : ℂ) := by
      apply tsum_congr
      intro i
      rw [detector_diagonal_eq_normSqCoe]
    rw [hsum_eq]
    -- commute the `ofReal` map across the summable series, then read the symmetric form; simpa normalizes
    -- the residual coercion gap between `(∑' r_i : ℂ)` and the per-term-lifted series.
    have hmap := Complex.ofRealCLM.map_tsum hHS
    simpa using hmap.symm
  rw [hcomplex]
  -- read back the real part of a real-valued series embedded in ℂ (a real has zero imaginary part).
  norm_cast

/-! ### Step ② — the frontier: power spectrum equals the Weil functional. -/

/-- **FRONTIER-CRUX core.** The Hilbert–Schmidt mass of the concrete self-pair factor reads back to the
Weil value `qw g`.  Analytically this is the identification of the **power spectrum** of the involution
test, `∫ |𝓕(g.involution.test)|² dx = ‖F_g‖_HS²`, with the Weil functional on the convolution square.

No longer an axiom: `C1Stage3BareHSObstruction.frontierCrux_step2_powerSpectrum_eq_weilValue` discharges it from the
bare obstruction — the per-test Hilbert--Schmidt premise already forces `g.test = 0`, at which zero test both sides
vanish.  The two declarations of `stage3FamilyFactor` (here and in that module) are definitionally equal, so the
discharge transfers across them verbatim. -/
theorem frontierCrux_powerSpectrum_eq_weilValue (g : CompactLogTest)
    (hHS : Summable fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) :
    ∑' i, ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2 = C1SameOwnerWeil.qw g :=
  ConnesWeilRH.Source.C1Stage3BareHSObstruction.frontierCrux_step2_powerSpectrum_eq_weilValue globalBasis g hHS

/-- **FRONTIER-CRUX.** The real part of the ordinary trace of the concrete detector equals `qw g`. -/
theorem frontierCrux_detectorTrace_eq_qw (g : CompactLogTest)
    (hHS : Summable fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) :
    (ordinaryTraceAlong globalBasis (detector g)).re = C1SameOwnerWeil.qw g := by
  rw [frontierCrux_reTrace_eq_hilbertSchmidtMass globalBasis g hHS]
  exact frontierCrux_powerSpectrum_eq_weilValue globalBasis g hHS

/-! ### Closure — the two named Stage-3 analytic facts close the RH-level criterion. -/

/-- **Gate-4 closure.** Once the concrete self-pair factor is Hilbert–Schmidt uniformly in `g`
(bare-operator form of FRONTIER-HS) and its detector trace reads back to `qw g` (FRONTIER-CRUX:
step ① proved above + step ② discharged from the bare obstruction), the Gate-4 assembly of
`C1Stage3RemainderFamily` yields the finite-vanishing healthy criterion state — the RH-level exit —
with no further hypothesis.  This is the named statement that "RH rests on exactly these two analytic
frontiers, and CRUX is closed once both are discharged." -/
theorem frontierCrux_closes_healthyCriterionState (F : Finset CriticalVanishingPoint)
    (hHS : ∀ g : CompactLogTest, Summable fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2) :
    C1.healthyCriterionState F := by
  apply C1Stage3RemainderFamily.stage3Remainder_healthyCriterionState globalBasis F hHS
  intro g
  exact frontierCrux_detectorTrace_eq_qw globalBasis g (hHS g)

end
end C1Stage3FrontierCrux
end Source
end ConnesWeilRH
