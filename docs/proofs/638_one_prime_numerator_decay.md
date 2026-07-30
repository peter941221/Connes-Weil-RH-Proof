# Proof 638: complete one-prime numerator decay

## Result

For every arithmetic visible prime `p`, Proof 638 strengthens the empty-suffix
bound from Proof 632 to

```text
||Interior_(p,[])||
  <= 244 q_p ||detector||,

q_p = p^(-1/2).
```

Consequently, the complete signed interior numerator tends to zero in
operator norm along the arithmetic-prime sequence.

This is a numerator estimate.  It does not compare the numerator with the
right co-defect on the same vector and therefore does not prove Bone 1.

## Exact renewal split

The normalized inverse adjoint satisfies

```text
N_p^dagger
  = rho_p I + sqrt(q_p) L_p^dagger N_p^dagger.
```

After inserting the actual old/new Schur frames, Lean proves the same-object
identity

```text
Interior_(p,S)
  = rho_p ReducedRow_(p,S) newFrame_S
    + sqrt(q_p) ReducedRow_(p,S) RenewedColumn_(p,S).
```

No Euler, loss, inverse, or frame factor is commuted in this step.

```text
                         +--> rho_p ReducedRow newFrame
 N_p^dagger newFrame ----+
                         +--> sqrt(q_p) ReducedRow RenewedColumn
                                      |
                                      v
                            L_p^dagger N_p^dagger newFrame
```

## Empty-suffix bounds

The existing one-prime boundary-moment estimate and the two contractive
frame factors give

```text
||ReducedRow_(p,[])|| <= 24 ||detector||.
```

The renewed column supplies the second square-root Euler gain:

```text
||sqrt(q_p) ReducedRow_(p,[])||
  <= 24 sqrt(q_p) ||detector||,

||RenewedColumn_(p,[])|| <= 2 sqrt(q_p).
```

Thus the renewal correction costs at most

```text
48 q_p ||detector||.
```

Proof 632's reduced-column estimate supplies the other
`196 q_p ||detector||`, giving the final constant `196 + 48 = 244`.

## Boundary

The scalar large-prime obstruction on the empty suffix is removed: the
complete numerator is genuinely `O(p^(-1/2))`, rather than merely `O(1)`.
The remaining obstruction is geometric.  Approximate antiresonant vectors
for the raw column `L_p^dagger newFrame_(p,[])` may still make the denominator
decay faster than this operator-norm numerator bound.

For nonempty suffixes, this proof supplies the exact renewal split and the
uniform renewed-column estimate, but not a suffix-uniform bound on the
reduced row.  Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH
remain open.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorOnePrimeNumeratorDecay.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorOnePrimeNumeratorDecayAudit.lean
```

The focused source and seven-declaration audit pass in the independent
Ubuntu-24.04 WSL2 ext4 verification tree.  Every audited declaration uses
exactly `[propext, Classical.choice, Quot.sound]`.
