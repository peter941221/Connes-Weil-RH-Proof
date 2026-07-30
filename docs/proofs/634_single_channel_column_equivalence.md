# Proof 634: raw and renewed column equivalence

## Result

Proof 634 removes the normalized inverse from the Bone 1 denominator, up to
one universal constant.  The concrete Euler definitions imply

```text
L_p N_p = N_p L_p,
L_p^dagger N_p^dagger = N_p^dagger L_p^dagger.
```

Hence, pointwise on every actual suffix frame,

```text
||L_p^dagger N_p^dagger newFrame x||
  <= ||L_p^dagger newFrame x||
  <= 8 ||L_p^dagger N_p^dagger newFrame x||.
```

The route-uniform existence statements are therefore equivalent:

```text
exists C, A is dominated by the renewed column
  <->
exists C, A is dominated by the raw loss column.
```

The renewed-to-raw direction preserves `C`; the reverse direction costs at
most `8`.

## Why the commutation is legal

Proof 630 deliberately did not exchange `N_p` and `L_p`.  Proof 634 first
proves the concrete forward identity: both the Euler transport and loss
factor are polynomials in the same translation by `-log p`.  Only then does
it use invertibility to commute the normalized inverse and finally take
adjoints.  No abstract normality assumption is inserted.

Lean needed the two coercion forms of the translation, as an equivalence and
as a continuous linear map, to be normalized to one explicit expression
before the module calculation.

## Boundary

This removes an operator-order ambiguity and the renewal inverse as a
separate source of difficulty.  It does not dominate the complete numerator.
Bone 1 is now equivalent to the raw same-vector estimate

```text
||A_(p,S)x|| <= C ||L_p^dagger newFrame_(p,S)x||
```

uniformly on route-valid steps.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorSingleChannelColumnEquivalence.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorSingleChannelColumnEquivalenceAudit.lean
```

## Verification

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| column-equivalence source            |  3403 | PASS   |
| focused nine-declaration audit       |     - | PASS   |
| CCM25Concrete aggregate              |  3909 | PASS   |
| full repository                      |  3990 | PASS   |
+--------------------------------------+-------+--------+
```

All nine audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
