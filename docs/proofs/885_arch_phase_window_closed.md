# 支路 3b: arch phase window closed axiom-free; a=1 exactly reduces to the window

Date: 2026-08-08. Status: **phase window CLOSED axiom-clean in Lean; the concrete a=1
bound is a single open inequality (needs Stirling arg bound).**

## 1. What is now settled (all Lean, #print axioms = [propext, Classical.choice, Quot.sound])

New module `ConnesWeilRH/Dev/ArchPhaseWindow.lean` proves, for any nonzero complex w,

```
  Re[w^4] >= 0  <->  (Re[w / star w])^2 >= 1/2            pow_four_re_sign_of_phase
```

`w / star w = e^(2 i arg w)` is the doubled-phase unit, so the right hand side is the
classical `cos^2 >= 1/2` phase window.  The four supporting identities are
`phase_ratio_re`, `re_pow_four`, `pow_four_handshake` (all real-image, `ring_nf`),
i.e. `Re[w^4] = normSq(w)^2 * (2 cos^2 - 1)`.

## 2. Wired to the arch gate / route-1 sign slot

```
  gammaPhase_window (a) :  0 <= Re[Gamma(a+i/2)^4]
        <->  1/2 <= (Re[Gamma(a+i/2) / conj(Gamma(a+i/2))])^2
  archPhase_at_one       :  the a = 1 instance (exact reduction, no extra assumption)
  archPhase_at_one_nonvacuous :  Gamma(1 + i/2) != 0  (slot is a real gate, AGENTS 6/11)
```

These chain `pow_four_re_sign_of_phase` with `Complex.Gamma_conj` and
`Complex.Gamma_ne_zero_of_re_pos`. `conj(Gamma(a+i/2)) = Gamma(a-i/2)`.

## 3. Honest limit: the a in the band but the phase bound is open

The positive band (docs/873) is `a in (0.815, 2.7)`, and a=1 is inside it:

```
  a=1 :  Re[Gamma(1+i/2)^4] = 0.26097 > 0
         Re[Gamma/ conj Gamma] = 0.8832, square 0.7801 >= 1/2     (exact mpmath, 40-digit)
```

So `one` IS a witness in the protected-by-window regime. But producing a Lean theorem
`0 <= Re[Gamma(1+i/2)^4]` needs a real *phase bound* (`Re[w/w] > 1/sqrt 2`), which requires
a Stirling / arg-Gamma estimate. mathlib v4.30.0 has no Stirling; that alone is the
remaining open item (the same wall as the whole arch-sign lane). No RH is claimed.

## 4. Wiring note (route-1 consumer)

The Hilbert-carrier arch sign slot (`HilbertCarrierReTypedSymbols.reTyped.
archimedeanSignNormalized`, currently `False`) is exactly the value of
`Re[Gamma(a+i/2)^4]` for the chosen band test. This module shows the slot reduces
to the `cos^2 >= 1/2` window and is non-vacuous; closing the specific value still
needs the Stirling phase bound. Name references: `MellinBandGamma`.
