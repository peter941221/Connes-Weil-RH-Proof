# Proof 627: antiresonant single-channel factorization

## Result

Proof 627 closes the algebraic and functional-analytic reduction from the
Proof 625 packed physical factor to one source-facing Douglas channel.  Bone 1
still needs a family-uniform relative-energy estimate for that channel.

Write

```text
B_(p,S) = (primeEulerAmbientLossFactor p)^dagger
          * (normalizedPrimeEulerInverse p)^dagger
          * newFrame_(p,S),

A_(p,S) = signedCompressedInteriorOwner_(p,S).
```

The remaining source statement is

```text
||A_(p,S) x||^2 <= C^2 ||B_(p,S) x||^2
```

with one `C` independent of every route-valid `(p,S)`.  The repository's
Douglas theorem converts this estimate into a readout `R_(p,S)`:

```text
R_(p,S) * B_(p,S) = A_(p,S),
||R_(p,S)|| <= C.
```

Taking adjoints gives the single-channel factor `H_(p,S)=R_(p,S)^dagger` in
the required noncommutative order:

```text
K_(p,S)^dagger * Transition_(p,S)
  = newFrame_(p,S)^dagger
      * normalizedPrimeEulerInverse(p)
      * primeEulerAmbientLossFactor(p)
      * H_(p,S).
```

The normalized inverse `N_p` precedes the ambient loss `L_p`.  No theorem in
this proof exchanges them.

## Packed factor

For one source channel `H`, Lean constructs the Proof 625 factor

```text
F_H x = (H x, -rho_p^-1 N_p L_p H x).
```

The packed old-carrier analysis has two rows:

```text
A_old y = (L_p^dagger y, Q_(p,S) U_p^dagger y),
Q_(p,S) = I - newFrame * newFrame^dagger.
```

The identities `N_p U_p = rho_p I` and
`newFrame^dagger Q_(p,S)=0` cancel the second packed coordinate after the
source compression.  Lean then proves the exact Proof 625 physical
factorization.

The norm ledger uses these bounds:

```text
+----------------------+-------+
| factor               | bound |
+----------------------+-------+
| rho_p^-1             |     8 |
| N_p                  |     1 |
| L_p                  |     2 |
| first packed row     |     1 |
+----------------------+-------+
```

Hence

```text
||F_H|| <= (1 + 8 * 1 * 2) ||H|| = 17 ||H||.
```

Lean timed out when it inferred the concrete Sonin carriers inside a
three-adjoint operator-norm estimate.  The packing module proves the same
estimate first for arbitrary Hilbert spaces and applies that opaque generic
lemma to the CCM24 carriers.  This removes the timeout without changing the
bound or increasing `maxHeartbeats`.

## Reverse recovery

Given a packed physical factor `F`, Proof 627 selects its first coordinate:

```text
H = WithLp.fstL * F.
```

The coordinate projection is contractive, so `||H|| <= ||F||`.  Adjointing
the exact two-row analysis gives

```text
A_old^dagger F
  = L_p H + U_p Q_(p,S) G,
```

where `G=WithLp.sndL * F`.  Applying `newFrame^dagger N_p` removes the second
term:

```text
newFrame^dagger N_p U_p Q_(p,S) G
  = rho_p newFrame^dagger Q_(p,S) G
  = 0.
```

Thus the reverse conversion preserves the bound.  The two directions are

```text
Physical(b)     -> SingleChannel(b),
SingleChannel(b)-> Physical(17*b).
```

A fixed numerical bound does not support an equivalence in both directions.
Proof 627 proves equivalence after existentially quantifying the bound for one
step, all prime/list pairs, and route-valid pairs.  The route-valid structure
also selects a single-channel factor for every genuine suffix of a
`FinitePrimePowerFamily`.

## Verification

Ubuntu-24.04 WSL2 built the Windows-source files in the existing ext4
verification copy:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| single-channel factorization         |  3397 | PASS   |
| single-channel recovery              |  3398 | PASS   |
| recovery audit + CCM25 aggregate     |  3901 | PASS   |
| full repository                      |  3981 | PASS   |
+--------------------------------------+-------+--------+
```

The audit checks ten public declarations.  Each declaration uses exactly

```text
[propext, Classical.choice, Quot.sound]
```

The new Lean files contain no `sorry`, `admit`, or user axiom.

## Boundary

Proof 627 identifies an equivalent producer; it does not supply the
route-uniform domination constant `C`.  Bone 1, Gate 3U, the finite-S sign,
Burnol's identity, and RH remain open.

The next source theorem has the exact shape

```text
exists C >= 0, forall route-valid (p,S) and source x,
  ||signedCompressedInteriorOwner_(p,S) x||^2
    <= C^2
       ||L_p^dagger N_p^dagger newFrame_(p,S) x||^2.
```

No closed-range premise, Gram inverse, or family-uniform spectral gap belongs
in that theorem.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorSingleChannelPacking.lean
  ...AntiresonantInteriorSingleChannelFactorization.lean
  ...AntiresonantInteriorSingleChannelRecovery.lean

ConnesWeilRH/Dev/
  ...AntiresonantInteriorSingleChannelRecoveryAudit.lean
```
