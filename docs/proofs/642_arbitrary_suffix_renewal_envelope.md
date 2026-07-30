# Proof 642: arbitrary-suffix renewal envelope

## Result

Proof 638's renewal split is valid for every visible prime `p` and every
suffix `S`.  Proof 642 proves that its correction term always satisfies

```text
||sqrt(q_p) ReducedRow_(p,S) RenewedColumn_(p,S)||
  <= 2 q_p ||ReducedRow_(p,S)||.
```

Equivalently,

```text
||Interior_(p,S) - rho_p ReducedRow_(p,S) newFrame_S||
  <= 2 q_p ||ReducedRow_(p,S)||.
```

No route-validity or primality premise is used.  The theorem is therefore
stronger than a restriction to route-valid suffixes.

## Two-sided envelope

Lean also proves

```text
||Interior_(p,S)||
  <= ||ReducedRow_(p,S) newFrame_S||
     + 2 q_p ||ReducedRow_(p,S)||,

||ReducedRow_(p,S) newFrame_S||
  <= 8 ||Interior_(p,S)||
     + 16 q_p ||ReducedRow_(p,S)||.
```

The second inequality uses the exact uniform scalar lower bound
`rho_p >= 1/8`.

Thus, whenever `||ReducedRow_(p,S)||` has a common bound, the complete
numerator is `O(q_p)` if and only if the leading reduced column is `O(q_p)`,
up to the displayed fixed constants.

## Why the empty-suffix proof does not generalize automatically

For `S=[]`, the old boundary moment vanishes and the remaining one-prime
moment has the established estimate

```text
||ReducedRow_(p,[]) newFrame_[]||
  <= 196 q_p ||detector||,

||ReducedRow_(p,[])|| <= 24 ||detector||.
```

Those are exactly the two inputs consumed by the general envelope.

For a nonempty suffix, the exact split still contains

```text
rho_p ReducedRow_(p,S) newFrame_S,
```

and `rho_p` tends to `1`, not to `0`, as `p` grows.  Route validity cannot
remove this term: by definition it is only

```text
SuffixRouteValidStep p S = (p :: S).Nodup.
```

The existing orientation ledger further decomposes the reduced row into a
uniformly bounded inclusion/forward part and two metric pieces for which no
route-uniform bound is currently proved:

```text
reduced row
  = metric orientation row
    + metric residual row
    + bounded inclusion/forward row.
```

Consequently, Proof 638's full `O(q_p)` numerator decay does not currently
extend to arbitrary route-valid suffixes without a new source theorem.

## Proposed producer

A direct family-uniform producer is the pair of estimates

```text
||ReducedRow_(p,S)|| <= C_row ||detector||,

||ReducedRow_(p,S) newFrame_S||
  <= C_column q_p ||detector||,
```

for every route-valid `(p,S)`.  Proof 642 then returns immediately

```text
||Interior_(p,S)||
  <= (C_column + 2 C_row) q_p ||detector||.
```

The second estimate must retain the signed metric-orientation and metric-
residual pair until their source-specific cancellation is proved.  Bounding
the two pieces separately would discard the cancellation required by the
active Bone 1 geometry.

This pair is sufficient for the operator-norm route isolated here.  It is not
claimed to be logically necessary without the reduced-row bound, because a
different proof could retain cancellation between the leading and renewal
terms instead of estimating them separately.

## Boundary

Proof 642 isolates the arbitrary-suffix obstruction; it does not supply the
two producer bounds.  Bone 1, Gate 3U, the finite-S sign, Burnol's identity,
and RH remain open.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorSuffixRenewalEnvelope.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorSuffixRenewalEnvelopeAudit.lean
```

## Verification

The focused Ubuntu-24.04 WSL2 ext4 build passed under the shared Lake lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| arbitrary-suffix renewal source      |  3412 | PASS   |
| focused seven-declaration audit      |  3413 | PASS   |
+--------------------------------------+-------+--------+
```

All seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
