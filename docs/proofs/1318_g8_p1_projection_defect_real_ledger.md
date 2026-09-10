# 1318 — G8 P1 projection-defect real ledger

Date: 2026-09-11.

Status: FORMAL Lean brick. It narrows the analytic P1 obligation; it does not
prove a finite-cutoff sign, a metric-to-radial transport theorem, P2, P3, or
RH.

## Statement

For the literal same-owner G8 source-cutoff projection split, write the three
defect channels as

```text
X = C† J† G D,
X† = D† G J C,
Y = D† G D,
```

where `G = g8AdjointShearGram` is positive, `C` is the projected cutoff leg,
`J` the source inclusion, and `D` its complement. The new leaf proves:

```text
X† is literally the Hilbert-space adjoint of X,
Tr(X + X†) = 2 Re Tr(X),
Re Tr(Y) >= 0.
```

All traces are `ordinaryTraceAlong` on the named healthy source basis; the
already-landed Hilbert--Schmidt pair data supplies legality. Thus P1's
projection defect has a single unconstrained real cross scalar plus a
nonnegative diagonal scalar. No cancellation or bound for that cross scalar
is assumed or derived.

## Evidence

`ConnesWeilRH/Dev/C1G8P1ProjectionDefectRealLedger.lean` and its paired audit
prove the three declarations with only `[propext, Classical.choice,
Quot.sound]`. Resource-controlled owning/audit build:
`1524_g8_p1_projection_defect_real_ledger_clean.log`, 3930 jobs, zero
`error:` and zero `sorryAx`.

## Consequence for P1

The next mathematical target is now precise: establish a same-owner analytic
bound for `Re Tr(X)` strong enough to compare the raw cutoff trace with the
literal metric cutoff. The unweighted Schur/coframe orthogonality does not by
itself provide that detector-weighted bound. No numerical experiment is an
admissible substitute.
