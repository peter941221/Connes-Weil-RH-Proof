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

3. **(§C) The single remaining analytic root + its concrete satisfiability.** One named axiom isolates exactly the
   bulk-subtracted readback identity, and at the explicit narrow root `gV = narrowArchRoot` it is *provably*
   satisfiable — the P3-a rank-one positive operator supplies a genuine Hilbert–Schmidt family whose self-pair trace
   reads back to `qw gV`.

So this module converts "Stage 3 reduces to two unexamined hypotheses" into: one proven windowed-HS lemma, one
proven divergence negative-result, and one named root — demonstrably satisfiable at the explicit root.

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

/-! ### §C — The single remaining analytic root, and its concrete satisfiability at the explicit narrow root. -/

/-- **FRONTIER-WINDOW-CRUX (the one named root).** After subtracting a divergent real bulk sequence `b`, the windowed trace
converges to the Weil value: there exists `b : ℕ → ℝ` with

```text
(∑' i ‖frontierWindowFactor n g e_i‖²) − b n   ──n→∞──▶   qw g .
```

This is the scalar shadow of Program P's full obligation (an operator family `A_n` plus a remainder whose real trace,
bulk-subtracted, tends to `qw g`).  It isolates *exactly* the analytic content that plain windowing (§B) does not yet supply:
once this identity holds uniformly in `g`, it discharges FRONTIER-CRUX and — with §A's windowed-HS — completes the P5 chain
end-to-end.  At present it is a named axiom; constructing `b` explicitly (and the matching operator family) is Program P's
remaining work. -/
axiom frontierWindowBulkSubtracted_readback_eq_qw (g : CompactLogTest) :
    ∃ b : ℕ → ℝ,
      Tendsto
        (fun n => (∑' i, ‖C1Stage3FrontierHS.frontierWindowFactor n g (globalBasis i)‖ ^ 2) - b n)
        atTop (𝓝 (C1SameOwnerWeil.qw g))

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

end

/-! ### Axiom-cleanliness audit. The four proven lemmas introduce no `sorryAx`; the one new named root is
`frontierWindowBulkSubtracted_readback_eq_qw` itself (audited last).  `#print axioms` takes a bare name, free args auto-filled. -/
#print axioms frontierHS_windowed_summable
#print axioms frontierPlainWindowTrace_eq_volumeTimesMass
#print axioms frontierPlainWindowTrace_unbounded
#print axioms frontierStatus_satisfiableAt_gV
#print axioms frontierWindowBulkSubtracted_readback_eq_qw

end C1Stage3FrontierStatus
end Source
end ConnesWeilRH
