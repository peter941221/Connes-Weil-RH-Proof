# Map 046 — Formal status after wave 1735: three leaves of the 1734 page landed

Supersedes the formal-status section of map 045 (the paper-level claim of
map 045 is unchanged). Scope: mass face only; the gate's sign face stays on
the map-047 two-premise exit; `0 ≤ qw` untouched; RH not claimed; stop word
= gate certificate.

```text
  [ 1734 paper page: B(N) = C_k^2/(4(a+N)^4) + ||theta''||_1^2/(32 pi^4 (a+N)^2) -> 0 ]
                  |                          |                          |
    +-------------v------+    +--------------v--------------+    +--------v---------+
    | k0 tail (Schwartz) |    | v tail (two IBPs)           |    | kernel readback  |
    | committed TailDecay|    | LANDED 1735: TwoIBP         |    | LANDED 1735:     |
    | + 1735 rig C check |    |   |v(s)| <= M/(4 pi^2 s^2)  |    | sourceKernel-    |
    | (envelopes hold,   |    |   lintegral <= M^2/(32pi^4X)|    | Readback_ae      |
    |  F59 slack law)    |    | LANDED 1734: moment leaf    |    | (pairing k_t)    |
    +--------------------+    +-----------------------------+    +------------------+
                  |                          |                          |
                  |             +------------v-------------+    +-------v---------+
                  |             | digamma growth (Lemma B) |    | committed       |
                  |             | LANDED 1735: linear      |    | Schwartz face   |
                  |             |   ||psi(w)|| <= const +  |    | toLp bridge     |
                  |             |   (12/5)||w||, Re w>=1/4 |    +-----------------+
                  |             +--------------------------+
                  |                          |
    +-------------v--------------------------v-------------+
    |  STILL OWED (in dependency order)                    |
    |  1. theta-W^{2,1} page: Lemma A (abs conv) +         |
    |     identify the differentiated series with psi';    |
    |  2. translation-tail integral identities             |
    |  3. 1723-consumer instantiation (blocked on 1)       |
    |  4. v-representative outside Schwartz class          |
    |     (no Young, no a.e. bridge in Mathlib — priced)   |
    +------------------------------------------------------+
```

## What is now machine-checked (all standard axioms, all paired-audited)

| Leaf | File | Statement |
|---|---|---|
| two-IBP decay | `Dev/C1G8R3AnnularTwoIBP.lean` | `\|∫ θ e\| ≤ ‖θ''‖₁/(4π²s²)`; tail `≤ ‖θ''‖₁²/(32π⁴X²)` |
| digamma line (Lemma B) | `Dev/C1DigammaVerticalLine.lean` | `‖ψ(w)‖ ≤ (‖ψ(1/2)‖+4+6/5) + (12/5)‖w‖` on `Re w ≥ 1/4` |
| kernel readback | `Dev/C1G8R3KernelReadback.lean` | `(C u) =ᵐ fun t => ∫ u x * conj(test (x-t)) dx` |

Rig C (`scripts/annular_bN_calibration_1735.py`,
`results/annular_bN_calibration_1735_results.json`): all four verdicts
green; `‖θ''‖₁ = 124.456`, `C_k = 1.674` (Gaussian test); law F59 —
in-class Schwartz θ gives super-polynomial `B_v` decay (slope −7.72), so
the `X⁻²` envelope is a worst-case bound, not a decay law.

## Order of attack (next waves)

1. Lemma C first (uniform `ψ' ≤ 20`): it needs only the termwise square
   bound and the decreasing-series integral comparison — no new machinery.
2. Lemma A (absolute convergence) — same M-test face.
3. Assemble `θ ∈ W^{2,1} ∩ C₀` and push the 1723 consumer.

## Formal update 1779 (2026-09-21)

The first half of Lemma C is now formal: `hasDerivAt_halfAnchorReciprocalSeries_of_re_ge_quarter`
proves termwise differentiation of the half-anchor reciprocal series on
`Re z > 1/4`, with the summable uniform majorant
`(n + 1/4)^(-2)`.  The paired audit builds with only
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

Record 1780 completes the same Lemma-C leaf.  The reciprocal series is now
identified with `Complex.digamma` by local equality on `Re z > 0`, and the
telescoping adjacent-reciprocal comparison proves
`sum (n + 1/4)^(-2) <= 20`.  Consequently the derivative norm is bounded by
20 on the quarter half-plane.

This is FORMAL evidence for Lemma C.  The next consumer is the M-test/
absolute-convergence face and the `theta in W^{2,1}` assembly.

## Formal update 1775 (2026-09-21)

The row-interface part of the remaining kernel readback is now formally
closed for Schwartz L2 approximations.  The theorem
`sourceKernelRow_integral_tendsto_of_schwartz_l2_tendsto` converts L2
convergence into the exact real square-root integral majorant using the
existing `frontierLp2normEqIntegralSqrt` and `frontierLp2normToReal` identities,
then applies the Holder row estimate.  Together with records 1773 and 1774,
the live readback chain is now:

```text
Schwartz L2 approximation
  -> pointwise kernel-row convergence
  -> a.e. limiting kernel readback
  -> annular kernel-diagonal / Tonelli consumer
```

This is FORMAL evidence only.  The Schwartz approximation sequence still has
to be instantiated for the selected source owner, and the uniform annular
kernel-diagonal majorant and S3 positivity remain open.

Record 1776 now composes the 1774 and 1775 interfaces into
`sourceKernelReadback_ae_of_schwartz_l2_tendsto`; the consumer no longer
requires a separately supplied pointwise-row hypothesis.  The remaining S3
formal wiring is therefore the selected-owner approximation instantiation and
the annular kernel-diagonal majorant.

Record 1777 discharges the approximation instantiation at the ambient L2
level: `exists_schwartz_l2_tendsto` selects a Schwartz sequence converging to
every global L2 input from the committed dense-range theorem.  Thus the
formal readback chain is complete for arbitrary L2 inputs; the remaining
obligation is now the annular kernel-diagonal majorant and its selected-owner
S3 consumer instantiation.  This is FORMAL evidence and does not prove S3
positivity or RH.

Record 1778 packages that chain as
`sourceKernelReadback_ae_arbitrary_l2`, so the actual root convolution has the
honest kernel-row formula for every `MemLp` input.  The readback interface is
now closed independently of the annular estimate.
