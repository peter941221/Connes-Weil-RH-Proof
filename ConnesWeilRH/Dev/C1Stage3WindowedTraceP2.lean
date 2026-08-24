/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3FrontierHS
import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex
import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# C1 Stage-3 WINDOWED-TRACE readback (Program P2) — the explicit plateau test `g₀`

This module runs **P2** of Route B windowing on the concrete half-density test
`g₀ = Wall14Plateau.bumpPlateauTest`.  It fixes the *windowed* self-pair factor

```text
A_n := frontierWindowFactor n g₀          (the expanding log-window Hilbert–Schmidt operator)
```

and reads off the real part of its self-pair trace.  The route's bare-operator ancestor in
`C1Stage3FrontierCrux` takes `stage3FamilyFactor g = F_g`; but #10
(`frontierBareSectionEnergy_eq_massTimesMeasure`) proves that bare `F_g` is a translation-invariant
convolution and hence **not** Hilbert–Schmidt on ℝ for any nonzero `g`.  Program P replaces it by the
windowed factor `A_n`, which *is* HS for every window size (`C1Stage3FrontierHS.frontierHS_summable`).

Because `A_n` is HS, step ① of FRONTIER-CRUX applies and

```text
Re Tr(A_n† A_n)   =   ∑' i ‖A_n (basis i)‖² .                        -- Hilbert–Schmidt structure.
```

The P0-a mass readback (`frontierWindowFactor_hsMass_eq`) then identifies that HS mass with the pure
window-length times kernel mass, and `frontierWindow_realVolume` gives the window length as `2 log(n+2)`.
For `g₀`, whose involution is the identity (the plateau test is real-valued and even), the kernel mass is
exactly the explicit convolution value `bumpA = ∫ |test|² ≥ 9/5 > 0`.  Hence:

```text
Re Tr(A_n† A_n)   =   2 · log(n+2) · bumpA .            -- THE windowed readback identity (proven below).
```

**Verdict.** The right-hand side has *no Weil content at all* — it is purely the divergent bulk
`window-length × kernel-mass`.  Since `bumpA > 0`, it tends to `+∞` as `n → ∞`; yet the Weil value

```text
qw g₀ = poleTerm − archimedeanTerm − finitePrimeSum        of (g₀.convolutionSquare)
```

is a single fixed, finite real.  **Plain windowing therefore does NOT read back to `qw g₀`:** its moving-cutoff
trace diverges like the window length while the target stays bounded and nonzero.  This is kill-test 1016 made
fully concrete for the explicit plateau test.

The ONE new analytic identity that step ② must supply for the WINDOWED route is thus a **renormalized** readback,
distinct from the bare-operator step ② in `C1Stage3FrontierCrux.frontierCrux_powerSpectrum_eq_weilValue`, which is now
discharged there (the per-test Hilbert--Schmidt premise forces `g.test = 0`).  For windowing, after subtracting the
divergent bulk `2 · log(n+2) · bumpA`, the remainder must tend to `qw g₀`.  That renormalized identity is not a
consequence of Parseval/Plancherel alone — the two proven lemmas below show exactly what plain windowing gives and
nothing more — so it remains the isolated frontier obligation on this branch.

Firewall: imports only active C1 modules (`C1Stage3FrontierHS`, `C1SameOwnerWeil`) plus the explicit plateau test
(`Wall14PlateauExplicitComplex`).  No frozen route leaf, no RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3WindowedTraceP2

open CC20Concrete
open CCM25Concrete.CompactLogConvolution
open MeasureTheory
open Filter
open scoped InnerProduct Topology BigOperators ENNReal Classical

noncomputable section

variable {ν : Type*} [Countable ν] (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)

open C1Stage3FrontierHS
open ConnesWeilRH.Source.Dev.Wall14Plateau   -- bumpPlateauTest, bumpA, bumpA_pos, bumpA_eq_integral_normSq, ...

/-- Pointwise complex bridge: the squared complex modulus equals the Euclidean norm-square.  This is what turns a
`‖·‖²` integrand (the form `frontierWindowFactor_hsMass_eq` emits) into the `Complex.normSq` integrand that
`bumpA_eq_integral_normSq` records. -/
theorem cplxNormSq_eq_normSq (w : ℂ) : ‖(w : ℂ)‖ ^ 2 = Complex.normSq w := by
  have hnn : 0 ≤ Complex.normSq w := Complex.normSq_nonneg w
  change (Real.sqrt (Complex.normSq w)) ^ 2 = _
  rw [Real.sq_sqrt hnn, Complex.normSq_apply]

/-- The kernel-mass integral of `g₀` — taken over its involution test — equals the explicit plateau value `bumpA`.
The involution fixes the real-even plateau test pointwise (`bumpPlateauInvolutionSelf`), and for complex values
`‖z‖² = Complex.normSq z`; the resulting integral is exactly `∫ |test|² = bumpA`. -/
theorem bumpInvolutionKernel_mass_eq_bumpA :
    ∫ t : ℝ, ‖(bumpPlateauTest.involution).test t‖ ^ 2 = bumpA := by
  have hpoint (t : ℝ) : ‖(bumpPlateauTest.involution).test t‖ ^ 2 = Complex.normSq (bumpPlateauTest.test t) := by
    rw [show (bumpPlateauTest.involution).test t = bumpPlateauTest.test t from bumpPlateauInvolution_real_even t]
    exact cplxNormSq_eq_normSq _
  have heq : ∫ t, ‖(bumpPlateauTest.involution).test t‖ ^ 2 = ∫ t, Complex.normSq (bumpPlateauTest.test t) := by
    apply integral_congr_ae
    filter_upwards with t using hpoint t
  rw [heq]
  exact bumpA_eq_integral_normSq.symm

/-! ### The windowed readback identity and its divergence. -/

/-- **P2 readback identity (concrete `g₀`).** The real part of the self-pair trace of the windowed factor equals the
pure window-length times kernel mass — for `g₀`, exactly `2 · log(n+2) · bumpA`.  There is *no other term*: this is
precisely why plain windowing cannot read back to the finite Weil value (kill-test 1016). -/
theorem p2_bumpTrace_eq_windowLengthTimesMass (n : Nat) :
    ∑' i, ‖frontierWindowFactor n bumpPlateauTest (globalBasis i)‖ ^ 2 =
      2 * Real.log (frontierWindowParam n) * bumpA := by
  rw [frontierWindowFactor_hsMass_eq globalBasis n bumpPlateauTest,
    frontierWindow_realVolume n, bumpInvolutionKernel_mass_eq_bumpA]

/-- The windowed self-pair trace of the plateau test, as a function of the window size `n`. -/
def bumpWindowTrace (n : Nat) : ℝ := ∑' i, ‖frontierWindowFactor n bumpPlateauTest (globalBasis i)‖ ^ 2

/-- **P2 divergence (concrete `g₀`).** Because `bumpA > 0`, the windowed self-pair trace of `g₀` is unbounded in
the window size — it grows like `2 · log(n+2) · bumpA`.  This is kill-test 1016 made explicit for the plateau test. -/
theorem p2_bumpTrace_tendsTop : ∀ M : ℝ, ∃ n : ℕ, M ≤ bumpWindowTrace globalBasis n := by
  intro M
  have hpos : 0 < ∫ t : ℝ, ‖(bumpPlateauTest.involution).test t‖ ^ 2 := by
    rw [bumpInvolutionKernel_mass_eq_bumpA]
    exact bumpA_pos
  simpa [bumpWindowTrace] using frontierWindowFactor_hsMass_tendsTop globalBasis bumpPlateauTest hpos M

/-- The windowed trace is monotone nondecreasing in the window size: by the readback identity it equals
`2 · log(n+2) · bumpA`, and `log (n+2)` is increasing with `bumpA > 0`. -/
theorem p2_bumpTrace_monotone : Monotone (bumpWindowTrace globalBasis) := by
  intro n m hnm   -- hnm : n ≤ m   ⊢ bumpWindowTrace globalBasis n ≤ bumpWindowTrace globalBasis m
  have hn : bumpWindowTrace globalBasis n = 2 * Real.log (frontierWindowParam n) * bumpA := by
    simpa [bumpWindowTrace] using p2_bumpTrace_eq_windowLengthTimesMass globalBasis n
  have hm : bumpWindowTrace globalBasis m = 2 * Real.log (frontierWindowParam m) * bumpA := by
    simpa [bumpWindowTrace] using p2_bumpTrace_eq_windowLengthTimesMass globalBasis m
  rw [hn, hm]   -- ⊢ 2 * log(param n) * bumpA ≤ 2 * log(param m) * bumpA
  have hp : frontierWindowParam n ≤ frontierWindowParam m := by
    rw [frontierWindowParam]
    exact Nat.cast_le.mpr (by omega)   -- n ≤ m ⟹ n+2 ≤ m+2
  have hlog : Real.log (frontierWindowParam n) ≤ Real.log (frontierWindowParam m) :=
    Real.log_le_log (show 0 < frontierWindowParam n from lt_trans zero_lt_one (frontierWindowParam_gt_one n)) hp
  gcongr <;> (try simpa using hlog) <;> nlinarith [bumpA_pos]

/-- **P2 verdict.** The windowed self-pair trace of the plateau test diverges to `+∞` as `n → ∞`; a sequence that
tends to `+∞` cannot also converge to the finite real `qw g₀`.  Thus plain (unrenormalized) windowing does not read
back to the Weil value for the explicit plateau test. -/
theorem p2_bumpTrace_tendsto_top : Tendsto (bumpWindowTrace globalBasis) atTop atTop := by
  rw [tendsto_atTop_atTop]   -- ⊢ ∀ M, ∃ a, ∀ x ≥ a, M ≤ bumpWindowTrace globalBasis x
  intro M
  obtain ⟨a, ha⟩ : ∃ a, M ≤ bumpWindowTrace globalBasis a := p2_bumpTrace_tendsTop globalBasis M
  refine ⟨a, ?_⟩
  intro x hx   -- hx : x ≥ a  (i.e. a ≤ x)
  exact le_trans ha (show bumpWindowTrace globalBasis a ≤ bumpWindowTrace globalBasis x from (p2_bumpTrace_monotone globalBasis) hx)

/-! ### Axiom-cleanliness audit — each P2 lemma carries only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
`#print axioms` takes a bare name (free args auto-filled with metavariables). -/
#print axioms p2_bumpTrace_eq_windowLengthTimesMass
#print axioms p2_bumpTrace_tendsTop
#print axioms p2_bumpTrace_monotone
#print axioms p2_bumpTrace_tendsto_top

end

end C1Stage3WindowedTraceP2
end Source
end ConnesWeilRH
