# Record 1173 — P2 bare Stage-3 no-go

Date: 2026-09-06

## Formal correction

The whole-line factor
`stage3FamilyFactor g = cc20GlobalLogConvolution (g.involution.test)`
cannot be used as the Hilbert–Schmidt factor in the P2 positive-trace route
for a nontrivial detector.  The existing theorem
`C1Stage3BareHSObstruction.bareHS_iff_zero_test` proves, for every fixed basis,

```text
Summable (i ↦ ‖stage3FamilyFactor g (basis i)‖²)
    ↔ g.test = 0.
```

The obstruction comes from cutoff trace growth versus the contraction bound
that a bare Hilbert–Schmidt mass would impose.  A healthy detector is intended
to detect a zero and is therefore not the zero test, so the premise is
incompatible with the active B5 owner.

## Route consequence

The provisional record-1172 P2 exit was removed from the live module.  The
positive-trace route must be rebuilt with a windowed or renormalized operator;
the scalar P2 signed-range route and the Bombieri owner-bridge route remain
the live alternatives.  P2/RH remain open.
