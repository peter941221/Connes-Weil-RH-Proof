# Proof 718: Endpoint Contraction Obstruction

The endpoint coframe `D_S` has the exact right-inverse identity

```text
J^* D_S = I,
```

where `J` is the isometric source-Sonin inclusion.  The new Lean guard proves
the sharp consequence

```text
||D_S|| <= 1
  -> D_S = J
  -> D_S - J = 0.
```

The proof uses the norm equality criterion for an orthogonal projection.  The
right-inverse identity gives `||u|| <= ||D_S u||`; the assumed contraction
gives the reverse inequality.  Equality of the endpoint and its source-Sonin
projection then puts every endpoint value in the source-Sonin carrier.

This is an obstruction to treating Proof 717's endpoint contraction as an
ordinary boundedness estimate.  In the existing ledger,

```text
D_S - J
  = forward actual-band coframe + metric coframe leakage.
```

Thus the contraction premise would require exact cancellation of the complete
combined leakage.  It is a valid sufficient condition for the energy consumer,
but it is not a plausible replacement for the missing signed Gate 3U physical
producer.  Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

The focused source build and audit use only the standard Lean axioms
`[propext, Classical.choice, Quot.sound]`.
