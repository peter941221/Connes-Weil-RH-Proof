# 2240 — The multiplicity constant is the Lean formal constant, bitwise

Date: 2026-09-30

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: **audit closed — the screened constant is exact**. The
`spectralMultiplicityConstant_proxy` carried since 2234 in the high-shell
budget `tail <= 4 * mult * B` is a binary64 evaluation of the Lean
constant `spectralMultiplicityConstant`, bitwise equal at
`301.83032993648527` (relative deviation `0.0`). The multiplicity item is
therefore **not a numerics lever**: the envelope already charges the
formal constant. The only slack inside it is the flat `+ 192` allowance
in the Lean definition, which is a proof-side object, not a measurement.

## Definition chain (all in-repo)

```text
ConnesWeilRH/Source/CC20ZetaCounting.lean:85
  completedRiemannXiKernelTailConstant := 2 / (1 - Real.exp (-Real.pi))

ConnesWeilRH/Dev/C1SpectralSummability.lean:29
  kernelSmallMomentConstant := (1 / Real.pi) ^ (1/4) * Real.Gamma (1/4)

ConnesWeilRH/Dev/C1SpectralSummability.lean:38
  xiGrowthFixedConstant := 2 * completedRiemannXiKernelTailConstant
                             * (kernelSmallMomentConstant + 1)

ConnesWeilRH/Dev/C1SpectralSummability.lean:303
  spectralMultiplicityConstant
    := (xiGrowthFixedConstant + 1 + |Real.log ‖completedRiemannXi 2‖|
        + 192) / Real.log 2

ConnesWeilRH/Dev/C1RouteAWeightedZeroMeasure.lean:219
  exists_weightedZeroMeasure_highShell_tsum_bound :
    exists B >= 0, tsum tail <= 4 * spectralMultiplicityConstant * B
```

The `4 *` factor is the geometric-series assembly: shell multiplicity
`3^n` against the `4^-n` shell mass, ratio `3/4`, sum `1/(1 - 3/4) = 4`.
The pipeline's `mult = (xi_growth + 1 + |log(pi/6)| + 192)/log 2` followed
by `tail = 4 * mult * B` mirrors that assembly exactly.

## Bitwise verification

`‖completedRiemannXi 2‖` is exactly `pi/6`: `xi(2) =
(1/2) * 2 * 1 * pi^-1 * Gamma(1) * zeta(2) = zeta(2)/pi = pi/6`. All
components evaluated in binary64:

```text
kernelSmallMomentConstant        2.7232882163306713
completedRiemannXiKernelTail     2.0903314107273685
xiGrowthFixedConstant            15.56581261957416
|log(pi/6)|                      0.6470295833786549
192 / log 2                      276.997447850681
rest / log 2                     24.832882085804286
mult                             301.83032993648527
stored proxy (2236 artifact)     301.83032993648527
bitwise equal                    True
```

The `192/log 2` part is `91.77%` of the constant. The stored tail of 2236
satisfies `tail/4/mult = 107454936.62043658` against the stored
`B = 107454936.62043647` (one-ulp-class agreement from the `up_many(3)`
chain, not a discrepancy).

## Consequence for the lever ledger

```text
before 2240  lever: "multiplicity proxy (still 2197's)" — expected to be a
             numerics item
after  2240  the pipeline charges the formal constant; the only remaining
             slack inside `mult` is the flat `192` (277.00 of 301.83 in
             log2 units), a Lean-side allowance that a sharper xi-growth
             estimate could in principle replace; that is a proof task,
             not a numerics one, and it is registered as such
```

All envelopes 2234-2239 should be read with "multiplicity = the Lean
formal constant, binary64-evaluated" in place of "proxy". No numerical
re-run is needed: the value is bitwise what every artifact already used.

## Nonclaims

- the audit is an evaluation check and a definition chase, not a Lean
  build; the quoted theorems are cited from the committed sources;
- no statement about whether the `192` can be reduced;
- complete-owner transfer and the signed producer margin remain open;
- no producer or RH claim.

## Provenance

- sources: `ConnesWeilRH/Source/CC20ZetaCounting.lean`,
  `ConnesWeilRH/Dev/C1SpectralSummability.lean`,
  `ConnesWeilRH/Dev/C1RouteAWeightedZeroMeasure.lean`
- numbers: re-evaluated in the verification environment against
  `results/2236_direct_product_solve_floor.json` (stored proxy and tail)