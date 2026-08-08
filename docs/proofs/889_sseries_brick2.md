# 889 - S-series elementary sandwich: brick 2 foundation (axiom-clean)

Date: 2026-08-08.  Brick 2 of the C2 arch-phase gate: the elementary `S` series
of docs/888 is reduced to a cleaner sandwich that is fully enough for the phase
gate, and the core inequalities + telescoping are now PROVEN axiom-clean in Lean.

## 0. Bottom line (verified on WSL, fresh mirror, 2637 jobs)

`ConnesWeilRH/Dev/SSeriesSandwich.lean` :  #print axioms on every declaration
= `[propext, Classical.choice, Quot.sound]` ; 0 sorry/admit/project-axiom.
Proven the elementary content of the S-series sandwich:

    a n = 1/(2(n+1)) - atan(1/(2(n+2)))
    p n = 1/(2(n+1)) - 1/(2(n+2))          (telescoping piece)
    u n = 1/(2(n+2)) - atan(1/(2(n+2)))    (positive defect)
    a n = p n + u n
    x - x^3 <= x/(1+x^2) <= atan x          (0 <= x)
    u n <= 1/(8 (n+2)^3)
    sum_{n< N} p n = 1/2 - 1/(2(N+1))

## The cleaner sandwich (supersedes docs/888 numeric window)

`S = Sum_n a n` telescopes:

    S = Sum_n p n + Sum_n u n = 1/2 + U

with `U = Sum_{n>=0} u_n = Sum_{m>=2} (1/(2m) - atan(1/(2m)))`.  From
`atan x >= x - x^3` we get `u_n <= (1/8) (n+2)^{-3}` and `u_n >= 0`, so

    1/2  <=  S  <=  1/2 + 1/32

(using `Sum_{n} 1/((n+1)(n+2)(n+3)) = 1/4` telescoping).  This sits firmly inside
the phase-gate window `gamma/2 + atan(1/2) +/- pi/8 = [0.3596, 1.1449]`, so the
gate needs no finer numeric sandwich.  stronger/looser than docs/888 in one:
the lower bound `/1/2` is looser (only needs >= 0.36) and the upper `/1/2+1/32`
is tighter than 0.509.

## What's proven vs open (in strictness)

Proven (this file)   : the termwise split, the atan cubic bound, positivity,
                       u_le_cube, and the finite telescoping sum_range_p.
OPEN (next brick)    : lift to the infinite series
                         hasSum p (1/2)   (limit of sum_range_p)
                         tsum u <= 1/32   (u_le_cube + telescoped 1/[(n+1)(n+2)(n+3)])
                       then  S = tsum a = tsum p + tsum u;  conclude
                       1/2 <= S <= 1/2 + 1/32   as a theorem.
Next after that: wire gamma/atan(1/2)/eta decimals (mathlib constants
one_half_lt_eulerMascheroniConstant / eulerMascheroniConstant_lt_two_thirds,
Real.n_d2 / Real.p n_d2, ArctanCert.atant half) and nlinarith the phase window.

## Status

- ANALYTIC: closed (S in [1/2, 1/2 + 1/32] inside the gate).
- LEAN brick 2 foundation: CLOSED, axiom-clean.
- LEAN assembly to the S theozrem: OPEN (listed above).
- RH not claimed.


## Brick 2b closure (2026-08-08, WSL green + axiom-clean)

The infinite-series assembly is now proven axiom-clean in the same file:

    def c n = 1 / ((n+1)(n+2)(n+3))            -- telescoping majorant
    c = (1/2) * d,  sum_range_d telescopes, so
    sum_{n<N} c n = (1/2)*(1/2 - 1/((N+1)(N+2))) -> 1/4     (sum_range_c, sum_range_c_le)
    u n <= (1/8) * c n                          (u_le_eighth_c, one_cube_le_prod)
    Real.tsum_le_of_sum_range_le  =>  tsum u <= 1/32         (u_range_le_32, tsum_u_le_32)
    a = p + u both summable                     (a_summable)
    S := tsum a                                 (def S)
    hasSum a (1/2 + tsum u)     =>  S_eq : S = 1/2 + tsum u
    S_ge_half : 1/2 <= S
    S_le_half_plus : S <= 1/2 + 1/32

#, print axioms on all five key theorems = [propext, Classical.choice, Quot.sound];
0 sorry.  This closes the S-series brick inside the gate [0.3596,1.1449].

Still open (further from the series): wire `gamma/2 + atan(1/2) +/- pi/8` numeric
decimals plus the real `|arg Gamma(1+i/2)|<=pi/8` gate itself (docs/859, Mellin-band
Stirling residue). RH not claimed.
