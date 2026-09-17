# 1568 — Phase wave pre-registration: the (★) tail and the B4 Hardy tail

Date: 2026-09-17.

Status: PREREG / PAPER SCREEN. Zero Lean, zero digits. This record buys no
mathematical claim; it fixes the entry conditions, the screening exponent
computation, and the typed stop rules for the only named analytic engines
feeding the two remaining square-sum obligations, so that wave spending is
priced before it is incurred (map 010 admission gates; law F15; law F21).

## 1. The two consumers

```text
(★)   Summable i, || P C J e_i ||^2          (single leg, records 1513/1514)
B4    Summable i, || D E H (I-E) H E M_p J e_i ||^2   (Hardy radial tail, record 1536)
```

Both live on carriers of two-sided infinite measure (record 1503: the
carrier is radial-support inf comap(HT) radial-support; no finite-window
collapse). The Hardy-pressure finding (1503) types any successful estimate:
at constant multiplier phase the two-sided carrier collapses toward {0}, so
all nontriviality is carried by the phase `theta` of the committed
Hardy-Titchmarsh multiplier `m`, `|m| = 1`.

## 2. Committed phase data (beat-0 inputs, transcribed not reconstructed)

From `logDeriv_GammaR_eq_log_pi_add_digamma` and record 1511 section 6:

```text
theta'(xi) = -2*pi * ( Re psi(1/4 - pi*i*xi) - log pi )
```

plus `|m| = 1`, `m(-xi) = conj m(xi)`, and the involution law. What does NOT
exist anywhere committed: any quantitative bound on `psi` on the vertical
line, hence any bound on `theta'` or `theta''`. The wave's first and only
unconditional deliverable is the pair

```text
(T0a)  | theta'(xi) + 2*pi*log|xi| | <= C1 / xi^2      for |xi| >= 2
(T0b)  | theta''(xi) - 2*pi/xi     | <= C2 / xi^2     for |xi| >= 2
```

with explicit absolute constants, via the Stieltjes/Binet expansion of
`digamma` on the right half-plane (the repo's exact-Fraction `digamma`
certificate engine in `scripts/yoshida_intervals/` is the numerics oracle for
sanity-checking the constants, not the proof). No Lean brick may be spent on
T1+ until T0a/T0b exist on paper with their error terms.

## 3. Screening exponent computation (paper, kills designs before spend)

Model the tail kernel after HT conjugation as an oscillatory integral with
phase `Phi(x,y;xi) = 2*pi*(x-y)*xi + theta(xi)` and amplitude carrying the
root-symbol decay. Two levers, and the divergence test on the 2D shell:

```text
square-integrable off-diagonal |x-y|^{-beta} on R^2  <=>  2*beta > 2  <=>  beta > 1

van der Corput (second-derivative test, |d^2 Phi / dxi^2| ~ 1/xi at scale xi):
    gain per stationary scale ~ xi^{-1/2}  ->  single-vdc beta_effective = 1/2   (FAILS)

root symbol on the Fourier side: |root^(xi)| ~ (1+|xi|)^{-k}, k = 2 for the
committed unit-detector root (finite exponential combination, rational decay).
Multiplier modulus 1 does not change k (Hardy-pressure lemma 1503).

open question T1: does (vdc 1/2) + (symbol decay k on the dual scale) add to
an effective beta > 1 on BOTH off-diagonal directions of the two-sided
carrier, or does the infinite measure of the carrier consume it?
```

This is the precise paper target of step T1: an exponent ledger, not a hope.
If T1 closes with `beta > 1` the wave promotes to Cotlar/almost-orthogonality
across Sonin scales; if T1 closes with `beta <= 1` for every symbol decay the
committed carrier allows, the typed stop fires (below) and the finding is
recorded as a TYPED impossibility for multiplier-phase routes into (★) -
which is itself a deliverable (bone-foundry rule: dead with a typed reason).

## 4. Order of battle (paper-first)

1. T0: digamma quantitative asymptotics (T0a, T0b) with explicit constants.
2. T1: exponent ledger for the single-column tail kernel on the two-sided
   carrier; verdict promotes or kills.
3. T2 (only if T1 > 1): Cotlar almost-orthogonality across the Sonin-scale
   family with phase-derived constants; this is what feeds (★).
4. T-B4 (parallel after T0): instantiate the 1536 radial-tail consumer for
   the actual forward-Euler-exposed columns; the boundary columns carry the
   same `m`, so T0 is their shared entry fee.
5. Lean bricks only after T2/T-B4 have paper names with explicit constants;
   acceptance remains whole-basis square sums, never vectorwise limits.

## 5. Stop rules and guards

- Constant-phase routes are structurally dead (1503 Hardy pressure): no
  attempt may replace `theta` by a stepwise-constant approximation without a
  proven residual bound feeding Cotlar.
- `|m|`-decay-only routes remain typed dead (1503/1505); `|m| = 1` exactly.
- Taper/density routes do not apply: F21 prices this gate at the PHASE
  level; every density-only input is precluded by the 1511 §6 transcription.
- No sign premise and no `qw` input may appear in any tail estimate feeding
  (★); the R5 gate is pinned separately (record 1567) and stays open
  independently of this wave.
- If T1 kills multiplier-phase routes, the wave records the exponent proof
  and re-prices (★) from the remaining routes (AO) before any further spend.

## 6. Boundary

Nothing here advances the gate: (★), B4, the rho5 combined-row identity, the
source/ambient transport, and the R4 wrapper all stay OPEN exactly as
recorded in map 042. RH not claimed.
