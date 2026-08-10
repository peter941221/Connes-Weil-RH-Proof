# 944 - Lane (a): in-repo Gamma Weierstrass developable, bricks 1-3

Date: 2026-08-10. Status: first-bricks milestone of the "Gamma-route"
divide-and-conquer. RH NOT claimed.

## Context
Lane (a) target (docs/940): close `arg(Gamma(1+i/2)) = -gamma/2 - atan(1/2) + S`
in-repo, i.e. connect the real Gamma to the Weierstrass series/product so that
`|arg Gamma(1+I/2)| < pi/8` becomes a closed uniform proposition. mathlib has
NO Complex.Gamma Weierstrass product, so this is a self-contained
real/complex analysis developable, attacked brick-by-brick.

## Bricks plan (this module: Dev/RealWeierstrassProd)
  1. Per-factor bounds: 0 < w(n) <= 1 (x = s/(n+1), 0 <= s).                 [CLOSED]
  2. Partial products P_N = prod_{n<N} w(n): positive, <= 1, non-increasing.  [CLOSED]
  3. Monotone convergence: P_N -> some limit L (skeleton for 1/Real.Gamma).   [CLOSED]
  4. Identify the limit with 1/Real.Gamma (Weierstrass/Gauss formula), then
     lift to Complex.Gamma and close |arg Gamma(1+I/2)| < pi/8.               [NEXT]

## Verified
webfac_bounds / partialP_pos / partialP_le_one / partialP_mono / partialP_ant /
partialP_bddBelow / partialP_converges.  axiom-clean [propext, Classical.choice,
Quot.sound], 0 sorry, WSL green.  No claim that the limit equals 1/Gamma yet.

## Next
Identify the real limit with 1/Real.Gamma, then lift to Complex.Gamma (docs/940).