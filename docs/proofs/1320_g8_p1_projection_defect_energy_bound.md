# 1320 — G8 P1 projection-defect energy bound

Date: 2026-09-11.

Status: FORMAL Lean brick. It supplies the exact Cauchy--Schwarz reduction of
the sole signed P1 defect term; it does not supply either required cutoff
energy estimate, a limit, metric-to-radial transport, P2, P3, or RH.

## Statement

Let `X` be the ordered projected--complement defect channel and let
`E_left(n)`, `E_right(n)` be the squared Hilbert--Schmidt basis energies of
the two legs in its existing same-owner pair. The new leaf proves

```text
|Re Tr(X_n)| <= sqrt(E_left(n)) * sqrt(E_right(n)).
```

Using record 1319, the left-hand side is equivalently the real ordinary trace
of the source-projection commutator channel

```text
C† J† [P, G] D.
```

The energy definitions retain the literal cutoff, healthy source basis, G8
Gram, and complement leg; no replacement by a normalized/additive carrier is
made.

## Evidence

`ConnesWeilRH/Dev/C1G8P1ProjectionDefectEnergyBound.lean` and its paired audit
prove both the original-channel and commutator-spelled estimates using only
`[propext, Classical.choice, Quot.sound]`. Resource-controlled owning/audit
build: `1534_g8_p1_projection_defect_energy_bound_retry2.log`, 3932 jobs,
zero `error:` and zero `sorryAx`.

## Consequence for P1

The next substantive analytic theorem must bound the explicit energies in a
way that makes their geometric mean harmless in the intended cutoff/radial
comparison. Trace-class legality and generic Cauchy--Schwarz are now closed;
they cannot be reused as a substitute for that missing estimate.
