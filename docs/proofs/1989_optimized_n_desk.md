# Record 1989 — Optimized-n desk study LANDED: exact B_n recursion verified against rungs 1-3, calibrated endpoint-saddle model N_n ~ C(k)·Γ(2n-1)·k^{1-n}, vertical optimum n* = sqrt(kT)/2 with c_ach = 1/sqrt(c_0) — the family brick's constant budget is c_0 <= 4

- **Date**: 2026-09-26
- **Status**: LANDED (desk wave — no Lean brick; script + record, 1632/1633
  convention)
- **Script**: `scripts/check_optimized_n_1989.py` (mpmath, 25 dps,
  Gauss-Legendre on saddle-flank-split panels; log-only acceptance) —
  log `build-logs/r1989_check1.log`
- **Feeds**: the optimized-n family brick (ladder stage after rung 3,
  record 1988) and the k-shape accounting: at WHICH (k, T) the priced
  target `exp(-c·sqrt(k|T|))` is reachable by the ladder.

## 1. What landed

**(a) Exact derivative recursion (hand-derived first, F27; machine-checked).**

    phi_k(u) = exp(-k/s),  s = 1 - u^2
    phi^(n)  = exp(-k/s) * B_n,   B_0 = 1,
    B_{n+1} = B_n' + g' * B_n,    g' = -2ku/s^2

`B_n` is a finite sum of monomials `coeff * k^p * u^a * s^-b` with rational
coefficients.  The recursion is exact on coefficient dicts and reproduces
the committed rung-1/2/3 formulas

    n=1: -2ku s^-2                                    (rung 1)
    n=2: 4k^2u^2 s^-4 - 8ku^2 s^-3 - 2k s^-2          (rung 2 / 1987)
    n=3: 12k^2u s^-4 - 8k^3u^3 s^-6 + 48k^2u^3 s^-5
         - 24ku s^-3 - 48ku^3 s^-4                    (rung 3 / 1988)

**exactly, coefficient by coefficient — 3/3 PASS** (log check (1)).

**(b) Support sizes: the Lean-architecture verdict.**

    +------+------------+
    |  n   | |supp B_n| |
    +------+------------+
    |  1   |  1         |
    |  2   |  3         |
    |  3   |  5         |
    |  4   |  9         |
    |  8   |  30        |
    |  12  |  63        |
    |  16  |  108       |
    |  24  |  234       |
    +------+------------+

Quadratic growth (~n^2/2.5) kills the closed-form per-n encoding used by
rungs 1-3: the family brick MUST be a coefficient-induction over the
recursion, not a per-n formula.

**(c) True masses** (log check (3); quadgl, ~1%-level at working n):

    k= 1: N_1=0.7358 N_2=3.194 N_3=35.645 N_4=1076.6 N_5=59550 N_6=5.32e6
    k= 3: N_1=0.0996 N_2=0.395 N_3=2.263  N_4=23.12  N_5=424.0 N_6=1.277e4
    k=10: N_1=9.08e-5 ... N_6=3.854
    k=30: N_1=1.87e-13 ... N_6=8.93e-8

Cross-rig anchor: **N_3(1) = 35.6455** matches record 1988's independently
derived outer true mass ~35.6 at k=1 (two different paths, same number).

## 2. Mechanism: the calibrated saddle model and the constant budget

    [ recursion B_{n+1} = B_n' + g'B_n ]  (exact, verified)
                |
                v
    [ endpoint layer: u -> 1, s ~ 2x; leading path (g')^n phi:
      |phi^(n)| ~ (2k/s^2)^n e^{-k/s} ]
                |
                v
    [ y = k/s:  int s^{-2n} e^{-k/s} ds = k^{1-2n} Gamma(2n-1)
      -> raw model  2^n Gamma(2n-1) k^{1-n} ]
                |
                v
    [ CALIBRATION (log check (4)): model/true drifts by ~x2 per n
      => the raw model's 2^n overcounts; the calibrated shape is
      N_n(k) ~ C(k) * Gamma(2n-1) * k^{1-n},  C(k) = O(1)
        C(1) = 1.48  (stable to 2% over n = 3..6)
        C(3) = 0.855 (stable over n = 4..6) ]
                |
                v
    [ vertical bound |L_phi(iT)| <= N_n(k)/T^n ; minimize over n:
      d/dn[2n log(2n/e) - n log(kT/c_0)] = 0  =>
        n* = sqrt(kT/c_0)/2      (c_0 = 1: scan-confirmed on all
                                  16 grid rows, e.g. (10,200): 23 vs 22.4;
                                  (30,200): 39 vs 38.7)
        achieved exponent = -sqrt(kT/c_0)  i.e.  c_ach = 1/sqrt(c_0) ]

**The constant-budget theorem** (the record's actionable pricing):

    if the family brick certifies  N_n(k) <= c_0^n * Gamma(2n-1) * k^{1-n},
    then the vertical ladder certifies  |L_phi(iT)| <= e^{-sqrt(kT/c_0)},

so the priced-target exponent budget is

    +--------------------+-----------+
    | certified constant |  c_ach    |
    +--------------------+-----------+
    | c_0 = 1            |  1.000    |
    | c_0 = 1.5 (C(1))   |  0.816    |
    | c_0 = 4            |  0.500    |
    | c_0 = 25           |  0.200    |
    +--------------------+-----------+

**c_0 <= 4 is the family brick's constant budget for c >= 1/2.**

## 3. The optimization table (log checks (5), (6))

True masses — c_ach over the grid: **1.06 .. 1.58** (trending to the
asymptote c = 1 as kT grows; the (30, 14.13) boost to 1.58 is the
middle regime's e^{-30} suppression):

    k= 1 T=  14.13: n*=3  c=1.163 | k= 3 T=  14.13: n*=4  c=1.145
    k= 1 T=    50 : n*=4  c=1.226 | k= 3 T=     50: n*=7  c=1.155
    k= 1 T=   200 : n*=8  c=1.190 | k= 3 T=    200: n*=13 c=1.120
    k= 1 T=  1000 : n*=17 c=1.123 | k= 3 T=   1000: n*=28 c=1.076
    k=10 T=  14.13: n*=7  c=1.224 | k=30 T=  14.13: n*=3  c=1.577
    k=10 T=    50 : n*=12 c=1.160 | k=30 T=     50: n*=20 c=1.240
    k=10 T=   200 : n*=23 c=1.101 | k=30 T=    200: n*=39 c=1.127
    k=10 T=  1000 : n*=48 c=1.055 | k=30 T=   1000: n*=48 c=0.939*

    (* = n-scan cap 48 hit; saddle n* ~ 61 — the reported c is a LOWER
    bound on the achievable one.)

With N_n inflated 100x (valid-not-sharp stand-in): c_ach100 ranges
**-0.06 .. 1.35**.  The weak cell is (k, T) = (1, 14.13): the 100x-ladder's
best is val = 1.26 > 1 — NOTHING is certified there.  The landed rungs'
real constant ratios are comparable (rung 2 at k=1 sits ~107x above true),
so at small k AND small T only the low rungs contribute; constant
tightness is the family brick's one real risk.

## 4. The two regimes (branch condition)

The saddle sits at s* = k/(2n); at the optimum n* = sqrt(kT/c_0)/2 this is
s* ~ k/sqrt(kT) = sqrt(k/T):

- **T > k (annulus regime)**: s* < 1, the peak is inside the annulus, the
  Gamma-model branch applies and the ladder is k-SHARP (k^{1-n}).
  14 of 16 grid rows live here.
- **T < k (middle regime)**: the optimum stays at small n; the mass is
  e^{-k}-suppressed (row (30, 14.13): c = 1.58).  A crude middle bound
  carries k^{+n} growth (the k^p monomials with the exponential capped at
  a constant), which would cap the family at exp(-cT/k) — losing the sqrt
  law at large k.  The family brick's middle theorem must keep e^{-k/s}
  unfixed (or decompose by s-levels).

## 5. Honesty box

- **Calibrated model, not theorem.**  C(k) = 1.48/0.855 are measured
  constants over n = 3..6; the family brick must PROVE an n-uniform
  `c_0^n Gamma(2n-1) k^{1-n}` envelope with c_0 <= 4 by coefficient
  induction.  Nothing here is Landau-blessed; it is priced, not certified.
- **Quadrature.**  |phi^(n)| has kinks at the zeros of B_n, so per-panel
  Gauss-Legendre tops out at percent level for large n (log docstring).
  Harmless: an x% value error moves c by x/sqrt(kT) <~ 0.001, and the
  n-scan minima sit at smooth cells.
- **n-scan capped at 48**: rows (10, 1000) and (30, 1000) hit the cap;
  reported c values there are conservative (lower bounds).
- **Vertical bound only** (w = iT, a = 1); the strip factor e^{|Re w|} and
  any horocyclic comparison are not priced here.
- **No Lean brick, no new axiom surface, no gate sign; RH not claimed.**

## 6. Consequence for the lane

    rung 1 -> rung 2 -> rung 3 -> [family brick: uniform-in-n envelope]
              -> resolution certificate -> re-bracket the 1985-class register.

The family brick's SPEC is now priced and two-piece:

    (i)   annulus/endpoint theorem:
            int_annulus |phi^(n)| <= c_0^n * Gamma(2n-1) * k^{1-n}
          with c_0 <= 4 (budget from section 2), via the y = k/s
          substitution — the Gamma shape IS the ladder's engine and must
          not be degraded to a k^{+n} polynomial;
    (ii)  middle theorem keeping e^{-k/s} unfixed (s-level decomposition),
          NOT a flat e^{-k} * poly(k)^n cap;

both driven by B_{n+1} = B_n' + g'B_n via coefficient induction (support
quadratic — closed forms are out).  The consumer theorem is then one line:

    |L_phi(iT)| <= c_0^n Gamma(2n-1) k^{1-n} / T^n  for all n
    =>  |L_phi(iT)| <= e^{-sqrt(kT/c_0)}   (choose n = sqrt(kT/c_0)/2).

No gate sign is proved here; RH is not claimed.
