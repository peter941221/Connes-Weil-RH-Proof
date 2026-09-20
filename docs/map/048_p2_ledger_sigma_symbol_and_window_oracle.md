# 048 - P2 ledger, sigma symbol, and the window falsifier oracle

Date: 2026-09-20.

Authority: audit + rig verdicts under 003/004/006/007. The two-premise exit,
the 1735 formal leaves, and map 047's detector screen are unchanged. This map
registers the P2 ledger audit and the arch-symbol rig from
[1740](../proofs/1740_p2_ledger_audit_and_f70_width_law.md). No sign theorem,
no carrier object, RH not claimed.

## The P2 ledger (all links machine-checked)

    P2  <=>  arch(F) + finite(F) <= 0   for every triple-vanishing g,
             F = g star g~,
    arch(F)   = (log 4pi + gamma) F(0)
                + int_0^inf [e^{y/2}(F(y)+F(-y)) - 2 F(0)]
                  / (e^y - e^{-y}) dy,
    finite(F) = sum Lambda(n)/sqrt(n) (F(log n) + F(-log n)).

The pole is dead on the whole triple class (Hermitian square law,
`C1HealthyYoshidaDetector.lean:48-51`, `:92-110`); Gate 2 is unconditional
(`C1CenterTwoCriterionBridge.lean:28-32`). The prime book is the only
obstacle on the full class; on the window slice (`supp g` inside
`(-log 2/2, log 2/2)`) `finite = 0` by
`C1SameOwnerWeil.lean:161-167` and the machine-checked consumer
`C1HealthyYoshidaDetector.lean:165-175` turns `arch <= 0` into `0 <= qw`.

## The arch symbol (new, paper + rig-validated)

    sigma(xi) = log pi - Re psi(1/4 - i xi/2),
    sigma(0) = 5.372183,   zero crossing xi* = 6.289836.

Legal derivation via the convergent difference series of digamma. Out-of-band
negativity is theorem-grade through `C1DigammaVerticalLine.lean`
(linear digamma growth on `Re w >= 1/4`).

## Verdicts (rig `scripts/p2_ledger_rig_1740.py`, v3)

- F70 width-free: REFUTED (smooth band-pass at w = 3, arch/F0 = +2.10 /
  +1.39 / +0.69, E4).
- F70 on the window class, RECT basis: FAILS — top triple eigenvalue
  +0.8421, matrix = exact to 4e-7 (E2/E2s/E2t); law F72: no sign statement
  transfers between the rect class and C_c^infinity in either direction.
- Smooth window probes: 8/8 negative (E5); random triple directions:
  120/120 qw > 0 (E3). No smooth positive direction found.
- Instrument law F71: rect-class kink-cell contribution; the y=0 right
  limit of the arch integrand is `F0(1/2 - 1/du)`, not `F0/2`; three-way
  validation (matrix / direct / exact) mandatory before reading signs.

## The window oracle (law F73)

On the prime-free window slice RH is equivalent to `arch <= 0` for smooth
triple-vanishing g: a single C_c^infinity counterexample would disprove RH
itself; every negative probe is a consistency check RH passes (128/128 so
far). The lane is simultaneously the cheapest formal P2 target and the
cheapest direct RH attack surface.

## Open order

1. Smooth-class adjudication with a C^infinity-faithful basis (the single
   most valuable number: the sign of the window triple eigenvalue).
2. F70-with-width threshold w0(sigma) on band-limited probes, paper version.
3. Lean oracle lemma `RH -> window arch <= 0` from committed pieces.
4. Theorem-grade sigma tail bound from the committed digamma leaf.
