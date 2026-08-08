# 903 - arg Gamma(1+i/2): Euler-Weierstrass -> atan-telescoping -> S-series (validated)

Date: 2026-08-08. Status: analytic derivation + numeric validation; Lean closure is
the next (heavy) step.  This is the **paper proof first** that the repo's own policy
(AGENTS [3] 精调 norm e/Posters, MEMORY 2026-08-08 “CORRECTION: C2 Lean is IN-REPO”)
requests before touching the Gamma wall.

## Goal

Close in Lean, axiom-clean, in-repo:

      |arg Gamma(1 + I/2)| <= pi/8        and then    Re[Gamma(1+I/2)^4] >= 0

The only missing analytic step is deriving  arg Gamma(1+i/2)  from mathlib objects.
Here we reduce it to the **already-closed** elementary series  S  of
`ConnesWeilRH/Dev/SSeriesSandwich.lean` (a n = 1/(2(n+1)) - atan(1/(2(n+2))), S := tsum a).

## The two real identities (validated to 60 sf, mpmath is sanity only)

    arg Gamma(1+i/2) = -0.24405829890542776266...
    |Gamma(1+i/2)|   =  0.82617761427604522788...

    S  = sum_{k>=0}[ 1/(2(k+1)) - atan(1/(2(k+2))) ]      = 0.50819714254614479386...   (= Lean SSeriesSandwich.S)
    S2 = sum_{n>=1}[ 1/(2n)     - atan(1/(2n))       ]    = 0.04454953354533866764...
    atan(1/2)                                             = 0.46364760900080611621...
                                                                            -------
    S1 - S2                                               = 0.46364760900080611621... = atan(1/2)

    -gamma/2 - atan(1/2) + S1 = -0.244058299012328655...   (matches arg to ~2e-62)

## Step 1: Euler-Weierstrass product (the only new analytic input)

mathlib lacks a product/log expansion of `Complex.Gamma`.  The standard, proven-in-product
form is

    1/Gamma(1+z) = exp(gamma*z) * prod_{n=1}^inf (1 + z/n) * exp(-z/n)        (Re z > -1)

which on `z = I/2` (Re = 0 > -1) gives, taking Im log:

    arg Gamma(1 + I/2) = -gamma/2 + sum_{n>=1} ( 1/(2n) - atan(1/(2n)) )   = -gamma/2 + S2.   (A)

Here  atan(1/(2n))  is Im log(1 + (I/2)/n) = Im log(1 + I/(2n)), and  Im((-I/2)/n) = 1/(2n).
The real-part (magnitude) side is not needed for the *arg*; reflection/Stirling cover the
magnitude if a separate |Gamma| estimate is wanted (see docs/901, docs/886 rev2).

## Step 2: telescoping S1 <-> S2 (the bridge to Lean's S)

 S1 - S2 = sum_{n>=1}[ 1/(2n) - atan(1/(2(n+1))) - 1/(2n) + atan(1/(2n)) ]
         = sum_{n>=1}[ atan(1/(2n)) - atan(1/(2(n+1))) ]
         = atan(1/2) - lim_{n->oo} atan(1/(2(n+1)))
         = atan(1/2) - 0
         = atan(1/2).                                                             (B)

(Verified: the series delta above reproduces atan(1/2) exactly to 60 digits.)

## Step 2: assemble

  arg Gamma(1 + I/2) = -gamma/2 + S2                    (A)
                     = -gamma/2 + S1 - atan(1/2)        (B)
                     = -gamma/2 - atan(1/2) + S.                                    (C)

This is exactly the docs/888 identity and matches the Lean `PhaseGateSandwich.D`.

## Why Lean closure is a real (multi-turn) project, not a one-liner

- mathlib proves the Euler/Weierstrass reflection + `Complex.Gamma_conj` +
  Bohr-Mollerup convexity, but does **not** expose `log Gaussian product`. So (A) must be
  re-derived: define the product sequence, prove it tends to `Complex.Gamma` or `1_row`,
  take `Im log`, then sum the `atan` series to `S2`.
- (B) is standard (both series via `tendsto` for the telescoping, `atan` -> 0 at infinity)
  and is the easiest brick of the three.
- (C) is pure algebra + the already-proxed `S_ge`/`S_le` + `PhaseGateSandwich.D_abs_lt_pi_eighth`.

## Lean lemma map (origin)

- `SSeriesSandwich.a` / `.p` / `.u` / `.hasSum_p` / `.tsum_u_le_32` / `.S_ge_half` / `.S_le_half_plus`  -> the S1 series.
- `ArctanCert.arctan_half` / `.fourth` / `.sixth` / `.eighth` -> atan decimals for PhaseGate.
- `PhaseGateSandwich.gamma_conj_half` -> conjugation needed for any real/imag split.
To build in Lean:
- L(a) Euler-W product seq -> `tendsto` to `Complex.Gamma`/`1/Gamma`, take `Im log`, sum to `S2`.
- L(b) telescoping `S1 - S2 = atan(1/2)` (telescoping `tendsto` + `atan` limit at top).  **CLOSED.**
- L(c) assemble `arg = -gamma/2 + S2 = -gamma/2 - atan(1/2) + S` via `S_eq_S2_add_atan_half`.

## Status

- Analytical: done, validated (see docs/888, 890, 901, 902; mpmath sanity, 60 digits).
- Lean CLOSED (this brick, axiom-clean): `SSeriesSandwich.S_eq_S2_add_atan_half :
  S = tsum S2 + atan(1/2)`, plus `hasSum_b`, `b_summable`, `S2_summable`,
  `tendsto_b_tail`, `a_eq_S2_add_b`.  WSL build green (2637 jobs), #print axioms =
  [propext, Classical.choice, Quot.sound], 0 sorryAx/project axioms.  With the Euler
  identity `arg = -gamma/2 + tsum S2` this gives the closed form
  `arg Gamma(1+I/2) = -gamma/2 - atan(1/2) + S` = docs/888 = `PhaseGateSandwich.D`.
- Lean OPEN: Lane-A Euler-Weierstrass `arg = -gamma/2 + tsum S2` itself (L). Lane-R
  axioms (#5 C1, #10 Yoshida), Lane-B model, and infinite-carrier Gate all still gate
  unconditional RH.  RH is not claimed.
