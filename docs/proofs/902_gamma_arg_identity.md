# 902 - Euler-log parameter identity for arg Gamma(1+I/2) (verified)

Date: 2026-08-08.  This nails the analytic identity behind the C2 real-phase gate,
as part of the in-repo (no external dependency) push.

## The identity (numerically verified, 60 significant digits)

With `s = 1 + I/2` and `mpmath` (used only as a *sanity check*; the Lean closure is
the goal, mpmath is not part of it):

    arg Gamma(1+I/2) = -0.2440582989054277626...

    S := sum_{k>=0} [ 1/(2(k+1)) - atan(1/(2(k+2))) ]   (this is our a-series in SSeriesSandwich)
        = 0.5081971425461447838...

    -gamma/2 - atan(1/2) + S  =  -0.2440582990...   (matches arg to ~1.9e-62)

so

    arg Gamma(1+I/2)  =  -gamma/2 - atan(1/2) + S        (docs888 identity)
    and  |arg Gamma(1+I/2)| ~ 0.244  <  pi/8 ~ 0.3927.

## Why this is the open analytic step (not a one-liner in mathlib)

To prove the identity inside Lean one needs the **logarithm of Gamma** as an Euler /
Weierstrass series (`log Gamma(1+z) = -gamma*z + sum_n (z/n - log(1+z/n))`), or the
equivalent Euler product limit. mathlib provides `Complex.Gamma_mul_Gamma_one_sub`
(reflection), `Complex.Gamma_conj`, `Complex.digamma`, and Bohr-Mollerup convexity,
but **no** ready Euler-product/logarithm expansion of `Complex.Gamma`.  Hence the gate
needs a real derivation + formalization of that expansion (heavy, multi-step analytic;
not something a single turn can just put a sorry on — AGENTS forbids placeholders).

## Two paths (tentative)

1. **Euler-Weierstrass product**: show `1/Gamma(1+s) = e^{gamma s} * prod_n (1+s/n)
   e^{-s/n}`, take log and imaginary part, get the `atan` telescoping that sums to `S`.
2. **Reflection + duplication** to reach half-integer line and express `|Gamma(1+i/2)|`
   exactly (this closes the modulus); the arg still needs path 1 anyway.

## Current Lean status supporting this

- SSeriesSandwich.S with 1/2 <= S <= 1/2+1/32           (axiom-clean, done)
- PhaseGateSandwich.D and |D| < pi/8                     (axiom-clean, done)
- PhaseGateSandwich.gamma_conj_half (Gamma(1-I/2)= conj Gamma(1+I/2))  (done)
- Gamma magnitude identity (the log-Gamma product) ...   OPEN (heavy)

RH is not claimed.
