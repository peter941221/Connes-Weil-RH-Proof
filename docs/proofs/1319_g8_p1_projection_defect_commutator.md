# 1319 — G8 P1 projection-defect commutator localization

Date: 2026-09-11.

Status: FORMAL Lean brick. It localizes the sole signed P1 defect scalar; it
does not prove a sign, a limiting estimate, metric-to-radial transport, P2,
P3, or RH.

## Statement

With the same healthy source owner and notation as record 1318, let

```text
X = C† J† G D,       P = J J†,
```

where `D` is the literal source-cutoff complement. The new leaf proves

```text
J† D = 0,
P D = 0,
X = C† J† (P G - G P) D = C† J† [P, G] D.
```

Thus the one signed real quantity from record 1318 is not a generic
projection-loss term: it is precisely the off-diagonal source-projection
commutator of the G8 Gram acting on the complement leg. The positive diagonal
defect remains separate.

## Evidence

`ConnesWeilRH/Dev/C1G8P1ProjectionDefectCommutator.lean` and its paired audit
prove all three declarations with only `[propext, Classical.choice,
Quot.sound]`. Resource-controlled owning/audit build:
`1531_g8_p1_projection_defect_commutator_retry6.log`, 3931 jobs, zero
`error:` and zero `sorryAx`.

## Consequence for P1

The next P1 brick must be analytic rather than another algebraic ledger: a
same-owner quantitative estimate for
`Re ordinaryTraceAlong (C† J† [P, G] D)`, strong enough to vanish in the
cutoff limit or be absorbed by the radial comparison. The identity supplies
no such estimate. In particular, ROOT-window positivity has no automatic
arrow to this orbit-supported detector without that transport.
