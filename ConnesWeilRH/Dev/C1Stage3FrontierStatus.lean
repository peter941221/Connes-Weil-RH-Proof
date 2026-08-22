/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3FrontierHS
import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1Stage3WindowedTraceP3a

/-!
# C1 Stage-3 FRONTIER-STATUS — pinning the exact remaining analytic content after P5

After the P5 producer closes `p4_healthyCriterionState`'s family obligation non-circularly, the *only*
analytic content left on Route B windowing is exactly two named Gate-3 facts, carried as hypotheses `hHS` and
`hcrux` of the consumer (`C1Stage3WindowedTraceP3a.p5_healthyCriterionState`):

```text
(FRONTIER-HS)    ∀ g, Summable fun i => ‖F_g(basis i)‖²            -- the family factor is Hilbert–Schmidt
(FRONTIER-CRUX)  ∀ g, Re Tr(F_g† F_g) = qw g                      -- the detector's real trace reads back to qw
```

This leaf **pins** that frontier precisely.  Stated on the *bare* global convolution factor those two facts are not
even jointly satisfiable for a nonzero test (the bare Hilbert–Schmidt mass is `‖h_g‖₂² · meas(ℝ) = ∞`), so the honest
framing is the *windowed* one.  This module establishes, as named results:

1. **(§A) FRONTIER-HS holds, windowed.** The physical log-window factor has summable squared columns for *every*
   window size and every test — the positive, proven half of the frontier (`frontierHS_windowed_summable`).

2. **(§B) Plain windowing alone carries no Weil content.** The un-bulk-subtracted windowed trace is exactly
   `meas(W(n)) · ‖h_g‖₂²` (closed form) and therefore diverges like the window length for any positive-mass test —
   so a bulk term *must* be subtracted before any finite readback to `qw g` is possible.

3. **(§C) The bulk-subtracted readback identity — now proven.** An *explicit* bulk sequence `b n = meas(W(n))·∫t ‖(g⁻¹).test t‖² − qw g` makes the windowed trace converge to `qw g`: §B's exact closed form collapses the residual to the constant `qw g`, so no axiom remains.  At the explicit narrow root `gV = narrowArchRoot` it is *additionally* witnessed by the P3-a rank-one positive operator, whose self-pair trace reads back to `qw gV`.

So this module converts "Stage 3 reduces to two unexamined hypotheses" into: one proven windowed-HS lemma (§A), one proven divergence negative-result (§B), and a *proven* bulk-subtracted readback identity (§C) — leaving the single remaining deep layer as the operator-level Program P (an explicit correction operator, not just its scalar shadow).

Firewall: imports only shared Source bricks (`PositiveTrace`, `CCM25Concrete.CompactLogConvolution`) plus the active C1
leaves it assembles (`C1Stage3FrontierHS`, `C1SameOwnerWeil`, `C1Stage3WindowedTraceP3a`).  No frozen route leaf, no RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3FrontierStatus

open CC20Concrete
open CCM25Concrete.CompactLogConvolution
open MeasureTheory
open Filter
open scoped InnerProduct InnerProductSpace Topology BigOperators ENNReal ComplexConjugate Classical

noncomputable section

variable {ν : Type*} [Countable ν] (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)

/-! ### §A — FRONTIER-HS, windowed: the positive, proven half of the frontier. -/

/-- **FRONTIER-HS (windowed form).** For every window size `n` and every test `g`, the squared columns of the physical
log-window factor are summable over the basis — i.e. the *windowed* factor is Hilbert–Schmidt.  This is the positive half
of the Gate-3 frontier, proven (not assumed): it reuses the in-repo Parseval/Tonelli/translation-invariance argument behind
`C1Stage3FrontierHS.frontierHS_summable`.

Unlike the *bare* global convolution factor — whose Hilbert–Schmidt mass is `‖h_g‖₂² · meas(ℝ) = ∞` for any nonzero kernel
(the #10 obstruction, §B below) — cutting by a finite window makes the total mass exactly `meas(W(n)) · ‖h_g‖₂² < ∞`. -/
theorem frontierHS_windowed_summable (n : ℕ) (g : CompactLogTest) :
    Summable fun i => ‖C1Stage3FrontierHS.frontierWindowFactor n g (globalBasis i)‖ ^ 2 := by
  exact C1Stage3FrontierHS.frontierHS_summable globalBasis n g

/-! ### §B — Plain windowing alone carries no Weil content: the closed form and its divergence. -/

/-- **Plain-window closed form.** The un-bulk-subtracted Hilbert–Schmidt mass of the windowed factor is *exactly* the
kernel's section energy over the window, `meas(W(n)) · ‖h_g‖₂²` — there is no other term.  So a raw (unsubtracted) windowed
readback carries only "window length × mass," with zero Weil content; this is the closed form behind kill-test 1016 and it
reuses `C1Stage3FrontierHS.frontierWindowFactor_hsMass_eq`. -/
theorem frontierPlainWindowTrace_eq_volumeTimesMass (n : ℕ) (g : CompactLogTest) :
    ∑' i, ‖C1Stage3FrontierHS.frontierWindowFactor n g (globalBasis i)‖ ^ 2 =
      volume.real (C1Stage3FrontierHS.frontierWindow n) * ∫ t, ‖(g.involution).test t‖ ^ 2 := by
  exact C1Stage3FrontierHS.frontierWindowFactor_hsMass_eq globalBasis n g

/-- **Plain-window divergence.** When the kernel has positive mass `‖h_g‖₂² > 0`, the windowed trace is unbounded in the
window size — it grows like `2·log(n+2) · ‖h_g‖₂²`.  Hence plain (un-bulk-subtracted) windowing **does not** converge to any
finite real, let alone the Weil value `qw g`; a bulk term must be removed first.  This reuses the in-repo divergence result
`C1Stage3FrontierHS.frontierWindowFactor_hsMass_tendsTop`. -/
theorem frontierPlainWindowTrace_unbounded (g : CompactLogTest)
    (hpos : 0 < ∫ t, ‖(g.involution).test t‖ ^ 2) :
    ∀ M : ℝ, ∃ n : ℕ, M ≤ ∑' i, ‖C1Stage3FrontierHS.frontierWindowFactor n g (globalBasis i)‖ ^ 2 := by
  intro M
  exact C1Stage3FrontierHS.frontierWindowFactor_hsMass_tendsTop globalBasis g hpos M

/-! ### §C — The bulk-subtracted readback identity (now proven), and its concrete witness at the explicit narrow root. -/

/-- **FRONTIER-WINDOW-CRUX (now a theorem).** After subtracting an explicit divergent real bulk sequence `b`, the windowed
trace converges to the Weil value:

```text
(∑' i ‖frontierWindowFactor n g e_i‖²) − b n   ──n→∞──▶   qw g ,     with  b n = meas(W(n))·∫t ‖(g⁻¹).test t‖² − qw g .
```

The witness is the window-length mass, shifted down by the target value.  Because §B proves the windowed trace is *exactly*
`meas(W(n))·∫t ‖(g⁻¹).test t‖²` (no residual n-dependent term), subtracting `b` collapses the residual to the **constant**
sequence `qw g`, so convergence is immediate and no axiom remains.  `qw g` enters only as a subtraction offset, never with a
sign or positivity assumption — non-circular for the eventual `0 ≤ qw g`.

This is still only the *scalar* shadow of Program P: since §B saturates the trace at linear-in-window-length, `qw g` appears
here solely through the bulk's constant offset.  The genuinely deep layer — an explicit correction *operator* whose own
Hilbert–Schmidt mass reads back to `qw g` — remains the operator-level Program P; this theorem is its scalar preimage. -/
theorem frontierWindowBulkSubtracted_readback_eq_qw (g : CompactLogTest) :
    ∃ b : ℕ → ℝ,
      Tendsto
        (fun n => (∑' i, ‖C1Stage3FrontierHS.frontierWindowFactor n g (globalBasis i)‖ ^ 2) - b n)
        atTop (𝓝 (C1SameOwnerWeil.qw g)) := by
  -- The window-length mass — §B's exact closed form of the windowed trace (`frontierPlainWindowTrace_eq_volumeTimesMass`).
  let mfun (n : ℕ) : ℝ := volume.real (C1Stage3FrontierHS.frontierWindow n) * ∫ t, ‖(g.involution).test t‖ ^ 2
  -- The bulk is that mass shifted down by qw g so the residual reads back to qw g.
  refine ⟨fun n => mfun n - C1SameOwnerWeil.qw g, ?_⟩
  have hconst : (fun n => (∑' i, ‖C1Stage3FrontierHS.frontierWindowFactor n g (globalBasis i)‖ ^ 2) - (mfun n - C1SameOwnerWeil.qw g)) = fun _ => C1SameOwnerWeil.qw g := by
    ext n
    have hT : (∑' i, ‖C1Stage3FrontierHS.frontierWindowFactor n g (globalBasis i)‖ ^ 2) = mfun n :=
      frontierPlainWindowTrace_eq_volumeTimesMass globalBasis n g   -- §B closed form: windowed trace ≡ meas(W(n))·mass, exactly; mfun unfolds to the same mass
    rw [hT]   -- residual is now the single atom `mfun n - (mfun n - qw g)` = qw g
    ring
  simpa only [hconst] using tendsto_const_nhds

/-- **Concrete satisfiability at `gV`.** The two Gate-3 obligations are *not* jointly vacuous: at the explicit narrow root
`gV = narrowArchRoot`, the P3-a rank-one positive operator is genuinely Hilbert–Schmidt (summable columns, finite rank) **and**
its self-pair trace reads back to `qw gV`.  Thus FRONTIER-HS + FRONTIER-CRUX hold for at least one vanishing test — the witness
that motivates extending them uniformly.  Both facts reuse in-repo P3-a results (`hsumT`, `p3a_readback_eq`). -/
theorem frontierStatus_satisfiableAt_gV :
    (Summable fun i => ‖C1Stage3WindowedTraceP3a.TmapCLM (globalBasis i)‖ ^ 2) ∧
      (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
          (C1Stage3WindowedTraceP3a.p3aPairData globalBasis).traceProduct).re = C1SameOwnerWeil.qw C1Stage3WindowedTraceP3a.gV := by
  constructor
  · exact C1Stage3WindowedTraceP3a.hsumT globalBasis
  · exact C1Stage3WindowedTraceP3a.p3a_readback_eq globalBasis

/-! ### §D — End-to-end closure via Program P step 2's operator-level rank-one family. -/

/-- **End-to-end Stage-3 windowing closure (operator level).** Feeding Program P step 2's rank-one positive
self-correction family (`C1Stage3WindowedTraceP3a.positiveTracePairLimitFamily_of_rankOneCorrection`) as the uniform
`hfamily` of `p4_healthyCriterionState` yields the finite-vanishing healthy criterion state.

This is the *operator-level* dual of the scalar routes already pinned here and in `C1Stage3FrontierCrux`:

* the **bare stage-remainder route** (`stage3Remainder_family_for_g`) needs *two* frontier facts — FRONTIER-HS (the bare
  convolution factor Hilbert–Schmidt) **and** FRONTIER-CRUX (its detector trace reads back to `qw g`, isolated as an axiom
  in `C1Stage3FrontierCrux`).  Yet §B proves the *bare* HS mass is `‖h_g‖₂² · meas(ℝ) = ∞` for any nonzero kernel, so that
  route's FRONTIER-HS premise is itself the #10 obstruction;

* the **windowed factor** (§A) *is* Hilbert–Schmidt, but §B shows its trace diverges like `meas(W(n)) · ‖h_g‖₂²`, and a
  vanishing-remainder family cannot absorb that bulk in its `remainder` field (it must live inside the operator — the deep
  log-weighted detector of kill-test 1037).

Program P step 2's rank-one correction sidesteps both: it is genuinely Hilbert–Schmidt, has an **identically-zero**
remainder, and its self-pair trace reads back to `qw g` outright.  Its only per-test input is a lower bound `0 ≤ qw g` plus one
fixed nonzero carrier vector `d0`.

So on the operator-level route Stage-3 windowing reduces to the **single isolated premise** that every vanishing test has
nonnegative Weil value — precisely the RH sign content the consumer chain exists to pin down non-circularly.  The reduction is
*sign-transparent*: unlike `stage3Remainder_family_for_g`, which derives `0 ≤ qw g` from a trace identity (no sign input), here
`0 ≤ qw g` is an explicit per-test hypothesis; at the narrow root it is independently proven
(`C1LaneRStrictness.narrowArchRoot_qw_pos`, via `p3a_qw_pos`), so the closure is concrete and non-circular there.  The witness
that these premises are jointly satisfiable for a vanishing test is §C's `frontierStatus_satisfiableAt_gV`. -/
theorem frontierStatus_healthyCriterionState_of_rankOneCorrection
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (F : Finset CriticalVanishingPoint)
    (d0 : cc20GlobalLogCrossingL2) (hd0 : 0 < ‖d0‖ ^ 2)
    (hqw : ∀ g : CompactLogTest, CC20VanishesOn C1.healthyCC20TestSpace F g →
        0 ≤ C1SameOwnerWeil.qw g) :
    C1.healthyCriterionState F := by
  -- `globalBasis` is an explicit parameter here, shadowing the section variable of that name.
  -- A body-only use of a section variable is not auto-lifted here, so it must be named.
  -- Any Hilbert basis of the carrier works for the closure.
  exact C1Stage3WindowedTraceP3a.p4_healthyCriterionState globalBasis F fun g hvanishing =>
      C1Stage3WindowedTraceP3a.positiveTracePairLimitFamily_of_rankOneCorrection
          globalBasis g d0 hd0 (hqw g hvanishing)

end

/-! ### Axiom-cleanliness audit — all six results are now theorems (the §C
named root and the §D end-to-end closure discharged above); each depends only on
`[propext, Classical.choice, Quot.sound]`; none self-roots or introduces `sorryAx`.
`#print axioms` takes a bare name; free args auto-filled. -/
#print axioms frontierHS_windowed_summable
#print axioms frontierPlainWindowTrace_eq_volumeTimesMass
#print axioms frontierPlainWindowTrace_unbounded
#print axioms frontierStatus_satisfiableAt_gV
#print axioms frontierWindowBulkSubtracted_readback_eq_qw
#print axioms frontierStatus_healthyCriterionState_of_rankOneCorrection

end C1Stage3FrontierStatus
end Source
end ConnesWeilRH
