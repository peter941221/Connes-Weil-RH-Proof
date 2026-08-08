# 890 - PhaseGateSandwich: the arch-phase shift |D| < pi/8 (axiom-clean)

Date: 2026-08-08.  Building on `SSeriesSandwich` (brick 2/2b) this module closes
the numeric phase bound needed by the real-phase gate `|arg Gamma(1+I/2)| <= pi/8`.

## Definition

    D := SSandwich.S - gamma/2 - atan(1/2)          (gamma = Real.eulerMascheroniConstant)

where `SSandwich.S := tsum a` with `a n = 1/(2(n+1)) - atan(1/(2(n+2)))`.

## Proven (Lean, `ConnesWeilRH/Dev/PhaseGateSandwich.lean`)

    gamma/2 <= (2/3)/2                       (gamma < 2/3, eulerMascheroniConstant_lt_two_thirds)
    1/4 <= gamma/2                            (one_half_lt_eulerMascheroniConstant)
    8/3 < pi                                  (pi > 3, pi_gt_three)
    1/3 < pi/8
    D_lower           : -(pi/8) < D
    D_upper           : D < pi/8
    D_abs_lt_pi_eighth: |D| < pi/8

Bounds used:
  - SSandwich.S :  1/2 <= S <= 1/2 + 1/32                     (S_ge_half, S_le_half_plus)
  - atan(1/2)  :  2/5 <= atan(1/2) <= 1/2                     (ArctanCert.arctan_half)
  - gamma      :  1/2 < gamma < 2/3                           (mathlib)
  - pi         :  pi > 3                                       (mathlib)

## Axiom audit

`#print axioms` on D_lower / D_upper / D_abs_lt_pi_eighth = `[propext,
Classical.choice, Quot.sound]`; 0 sorry / 0 project axiom.  Build 2653 jobs green.

## What this buys

`D` equals `-argGamma`-like shift:  `arg Gamma(1+I/2) = -gamma/2 - atan(1/2) + S`
is the Gamma **magnitude identity** (docs/888).  With that identity, |D| < pi/8
directly gives `Re[Gamma(1+i/2)^4] >= 0` i.e. the arch-phase gate.  The equiprovable
Sand E / |D| portion is now fully in Lean; the Gamma magnitude identity itself
remains OPEN (separate analytic step, docs/888/859).  RH not claimed.
