# 944 - Lane (a): in-repo Gamma Weierstrass developable, brick 1+2

Date: 2026-08-10. Status: first milestone of the "Gamma-route" divide-and-conquer.
RH NOT claimed.

## Context
Lane (a) target (docs/940): close `arg(Gamma(1+i/2)) = -gamma/2 - atan(1/2) + S`
in-repo, i.e. connect the integral-defined `Complex.Gamma` to the Weierstrass
series/product so that `|arg Gamma(1+I/2)| < pi/8` becomes a closed uniform
proposition. mathlib has NO Complex.Gamma Weierstrass product, so this is a
self-contained real/complex-analysis developable, attacked brick-by-brick.

## Bricks plan (this module: RealWeierstrassProd)
  1. Per-factor bounds: 0 < w(n) <= 1 for w(n)=(1+x)exp(-x), x=s/(n+1), 0<=s.  [CLOSED]
  2. Partial products P_N = prod_{n<N} w(n) : strictly positive, <= 1, and
     non-increasing (P_{N+1} <= P_N).                                   [CLOSED]
  3. Monotone convergence: P_N -> some limit L (existence), the skeleton for
     identifying L with 1/Real.Gamma s.                                  [NEXT]

## Verified this milestone
Dev/RealWeierstrassProd.lean: webfac_bounds / partialP_pos / partialP_le_one /
partialP_mono.  axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry,
WSL green (1916 jobs).  No claim that the limit equals 1/Gamma yet.

## Next
Close brick 3 (monotone convergence -> exists L, Tendsto ...) via the
monotone/bounded-below => limit real-analysis lemma; then connect P_N to
Real.Gamma via the Weierstrass/Gauss product formula.
