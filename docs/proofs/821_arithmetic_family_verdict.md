# Proof-717 / Gate-3U: 821 — outer channel non-zero on every real arithmetic family (route-a negative)

Date: 2026-08-06
Status: arithmetic-scale negative — the outer channel `(I−R)∘D` leaks O(1) on
*every* realistic prime family tested; no real finite-S arithmetic set makes it
vanish.  This closes route (a) ("the genuine arithmetic finite-S primes beyond
toy {2,3,5} save it") at the level of the operator geometry.
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/815_rh_route_conditional_boundary.md`, `816`, `817`, `818`, `819`, `820`

## 1. What the real arithmetic family is

The transport factor is `(I − p^(−1/2) · shift_{−log p})` (coefficient `p^(−1/2)`,
`CCM24EulerTransport.lean:32-52`), one factor per **visible prime** `p` (`p>1`,
deduplicated bases).  The stored `FinitePrimePowerFamily` exponent is arithmetic
ownership only; the operator runs over visible primes
(`CCM24FiniteSProjectionTrace.lean:46`).  So route (a) = vary the prime *set*, not
the exponent.  Probe output at `logλ=0` on boundary probe, adequate box to avoid
artifacts.

## 2. Result (corrected, box-adequate)

```
family            outer leak
{2}               0.28
{97}              0.099       <-- large-prime: non-zero (0.10), NOT 0
{101}             0.098
{101,103}         0.134
{2,3,5}           0.38
{3,5,7}           0.42
{7,11,13,17}      0.41
{2,3,5,7,11,13}   0.39
```

Single primes leak 0.24–0.32 (small primes) down to 0.10 (large primes).  Larger
prime sets push the leak UP toward 0.41.  **Every family is non-zero.**

## 3. Trap caught and corrected

Naive run (box `Lt=4`) printed `{101}` → `0.000`.  That was a **box-truncation
artifact**: `log(101) = 4.6 > Lt`, so the shift leaves the box, the transport
acts trivially, and `D` compresses to the identity near the boundary → leak 0.
Growing the box to `Lt≥6` reveals the true `0.098`.  Small-prime controls are
box-stable (0.28).  **Coordinate-trap lesson: always verify a "0" is not the
window clipping the shift.**

## 4. Verdict

```
Route (a) does NOT rescue Gate-3U at the numeric/operator scale:
  - small primes: 0.28
  - large primes: 0.10  (smaller, but > 0)
  - prime sets of any realistic magnitude: 0.28–0.42, never 0.
  The outer channel is not made to vanish by the real arithmetic family choice.
```

This is a numeric finding (not Lean, not RH). The genuinely-larger arithmetic
structure (the actual critical-line sums over an *infinite* family, or prime
powers with von-Mangoldt–type weights in the full product) would need the full
RH-scale object, not a finite prime set — but within every finite-S family we can
trigger numerically, the outer channel leaks.

## 5. Conclusion for the gate

The outer channel is now falsified at 4 independent scales: simple (815), band
-limited (816), exact-Slepian (817), and every-arithmetic-family (821).  The
inner (band/second) channels remain unreachable by the 818/819 grid method.  The
true remaining hope is the full RH-scale (infinite/critical-line) structure or a
genuinely analytic transported-Sonin/prolate calculation (route b).