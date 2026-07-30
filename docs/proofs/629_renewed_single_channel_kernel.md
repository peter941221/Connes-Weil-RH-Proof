# Proof 629: renewed single-channel kernel

## Result

Proof 629 closes the exact kernel-compatibility condition for the Proof 628
denominator.  For every visible prime `p`, every suffix `S`, and every source
vector `x`, Lean proves

```text
B_(p,S) x = 0  <->  x = 0,

B_(p,S) = L_p^dagger * N_p^dagger * newFrame_(p,S).
```

Consequently the signed numerator automatically vanishes on the same fiber:

```text
B_(p,S) x = 0  ->  A_(p,S) x = 0,

A_(p,S) = signedCompressedInteriorOwner_(p,S).
```

The result is stronger than the active route statement because it needs no
`(p :: S).Nodup` premise.

## Proof mechanism

Set

```text
u = newFrame_(p,S) x,
y = N_p^dagger u.
```

The renewed-column equation and the two exact Euler identities give

```text
B x = 0
  -> L_p^dagger y = 0
  -> U_p^dagger y = y
  -> y = rho_p u.
```

The evidence for the last two arrows is the operator-level pair

```text
U_p^dagger - I = -sqrt(q_p) L_p^dagger,
U_p^dagger N_p^dagger = rho_p I.
```

Since `rho_p` is nonzero, `L_p^dagger u = 0`.  The new frame lies in the
genuine upper radial-support subspace.  On that subspace,

```text
L_p^dagger = c_p (I + translation_(log p))
```

has trivial kernel: the support boundary supplies an initial zero interval,
and the anti-periodic relation propagates that zero through every later
interval.  Hence `u = 0`; new-frame isometry then gives `x = 0`.

```text
 +------------------------+
 | Bx = L^dagger N^dagger |
 |      newFrame x = 0    |
 +-----------+------------+
             |
             v  exact Euler pairing
 +------------------------+
 | N^dagger newFrame x    |
 |   = rho * newFrame x   |
 +-----------+------------+
             |
             v  radial antiresonant propagation
 +------------------------+
 | newFrame x = 0         |
 +-----------+------------+
             |
             v  isometry
 +------------------------+
 | x = 0                  |
 +------------------------+
```

## What this rules out

There is no exact nonzero source vector on which the denominator vanishes
while the signed numerator survives.  Therefore a failed Bone 1 estimate
cannot be explained by an incompatible exact kernel.

This does not provide a closed range, a lower spectral bound, or a uniform
Douglas factor.  Approximate antiresonant kernels remain possible, so the
remaining theorem is still quantitative:

```text
exists C >= 0, forall route-valid (p,S), forall x,
  ||A_(p,S) x||^2 <= C^2 ||B_(p,S) x||^2.
```

## Verification

The Ubuntu-24.04 WSL2 ext4 verification copy passed the focused source build
and import-facing audit:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| renewed single-channel kernel        |  3398 | PASS   |
| kernel audit                         |     - | PASS   |
| CCM25Concrete aggregate              |  3902 | PASS   |
| full repository                      |  3983 | PASS   |
+--------------------------------------+-------+--------+
```

All six audited declarations use exactly

```text
[propext, Classical.choice, Quot.sound]
```

The source and audit contain no `sorry`, `admit`, or user axiom, and their
focused `git diff --check` passes.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorSingleChannelKernel.lean

ConnesWeilRH/Dev/
  ...AntiresonantInteriorSingleChannelKernelAudit.lean
```
