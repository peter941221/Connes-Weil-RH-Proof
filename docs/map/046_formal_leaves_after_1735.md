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
    |  1. scattering-symbol x profile product in W^{2,1}; |
    |     the bare CCM24 profile is now an actual consumer |
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

1. Assemble the scattering-symbol times critical-profile `theta` in
   `W^{2,1} intersect C_0`; the bare profile consumer is now landed.
2. Prove the translation-tail integral identities.
3. Instantiate and push the 1723 consumer.

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

This is FORMAL evidence for Lemma C.  The next consumer is the actual
scattering-symbol and `theta in W^{2,1}` assembly.

## Formal update 1781 (2026-09-21)

Lemma A is now also formal.  The theorem
`summable_digamma_canonical_series_of_re_ge_quarter` derives the canonical
series with anchor 1 by adding the existing half-anchor series at 1 and at
`z`; its norm-series corollary supplies the absolute-convergence interface.
The paired audit for the combined A/C module is green with standard axioms
only.

The remaining mass-face work is the actual scattering-symbol derivative
formula, Schwartz weighted-integrability, and the `theta` assembly consumed
by the annular tail bound.

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

## Formal update 1782 (2026-09-21)

`annular_ccm24CriticalMellinLogProfile_v_tail_le` instantiates the already
proved two-integration-by-parts tail bound with the concrete CCM24 critical
Mellin profile. Its first derivative is read back from the carrier, its second
derivative from the formal chain-rule formula, and all three profiles are
integrable. The paired Audit build is green with exactly the standard three
axioms and no `sorryAx`.

This is FORMAL evidence for the profile leg only. It does not assert the
scattering multiplier product; the next shortest brick is its second-derivative
and weighted-Schwartz product readback.

## Formal update 1783 (2026-09-21)

`ccm24CriticalGammaRLogDeriv_eq_digamma` now gives the exact CCM24 critical
line readback of the GammaR logarithmic derivative at `1/2 - 2*pi*i*xi` as
the digamma value at `1/4 - pi*i*xi`. The proof uses the existing GammaR
identity and exact complex arithmetic; its paired Audit build is green with
the standard three axioms and no `sorryAx`.

This is FORMAL interface evidence, not yet the phase second-derivative bound.
The next brick differentiates this readback using the already landed digamma
derivative series.

## Formal update 1784 (2026-09-21)

The apparent endpoint mismatch is now closed formally. The theorem
`hasDerivAt_digamma_criticalQuarterLine` reaches the actual line
`Re z = 1/4` by applying the digamma recurrence once, differentiating at
`z + 1` where the strict quarter-half-plane theorem applies, and reading the
inverse correction back. Consequently
`hasDerivAt_ccm24CriticalGammaRLogDeriv` gives the real-frequency derivative
of the GammaR log symbol in terms of `digamma'` on the critical line.

The paired Audit build is green with only the standard three axioms and no
`sorryAx`. This is still a symbol derivative interface; the phase product's
weighted W2,1 estimate and the S3 sign remain open.

## Formal update 1785 (2026-09-21)

`hasDerivAt_ccm24ArchimedeanFactor_logDeriv` now differentiates the actual
CCM24 archimedean factor along the real frequency axis and reads its
logarithmic derivative back through the GammaR symbol. The proof uses the
nonvanishing of GammaR on the positive-real-part line and the previously
closed critical GammaR log-derivative interface. The paired Audit build is
green with only the standard three axioms and no `sorryAx`.

This is FORMAL evidence for the first factor derivative in the scattering
phase product. The weighted product estimate, S3 positivity, and RH remain
open.

## Formal update 1786 (2026-09-21)

`hasDerivAt_digamma_deriv_of_re_ge_quarter` now differentiates the already
read-back reciprocal series once more on the strict quarter half-plane. The
new cubic majorant is summable, and the result identifies the derivative of
`deriv Complex.digamma` with the explicit negative cubic reciprocal series.
The paired Audit build is green with only the standard three axioms and no
`sorryAx`.

This is FORMAL evidence for the second-order special-function interface that
the scattering-factor W2,1 assembly needs. It does not yet prove the weighted
product estimate, the S3 kernel-diagonal majorant, semi-local positivity, or
RH.

## Formal update 1787 (2026-09-21)

`hasDerivAt_deriv_digamma_criticalQuarterLine` transports the new cubic
digamma series through the one-step recurrence to the actual line
`Re z = 1/4`, then differentiates it along the real frequency parameter.
The paired Audit build is green with only the standard three axioms and no
`sorryAx`.

This closes the critical-line special-function leg needed for a second
GammaR-log-derivative estimate. The Archimedean scattering product's full
W2,1 bound, the S3 kernel-diagonal majorant, semi-local positivity, and RH
remain open.

## Formal update 1788 (2026-09-21)

`hasDerivAt_deriv_ccm24CriticalGammaRLogDeriv` now composes the critical-line
second Digamma derivative with the exact GammaR logarithmic-derivative
readback. Thus the real-frequency derivative of the GammaR log symbol's
derivative is available in explicit cubic-series form. The paired Audit build
is green with only the standard three axioms and no `sorryAx`.

This closes the second-order GammaR-log-symbol interface. The actual
Archimedean scattering-factor W2,1 product estimate, S3 kernel-diagonal
majorant, semi-local positivity, and RH remain open.

## Formal update 1789 (2026-09-21)

`hasDerivAt_deriv_ccm24ArchimedeanFactor` now differentiates the derivative
of the actual CCM24 Archimedean factor. It combines the GammaR log-symbol
derivative and the factor's first derivative by the product rule, preserving
the exact factor owner and avoiding any unproved division or growth claim.
The paired Audit build is green with only the standard three axioms and no
`sorryAx`.

This closes the actual factor-level second-order interface. The full
scattering-product W2,1 estimate, S3 kernel-diagonal majorant,
detector-specific semi-local positivity, and RH remain open.
