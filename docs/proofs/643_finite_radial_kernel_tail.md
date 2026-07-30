# Proof 643: finite radial-column kernel and exact tail

## Result

The result is negative for a fixed finite-column shortcut, but it is a
substantive reduction rather than a generic contract.

Proof 643 determines the kernel of Proof 639's actual column exactly.  Write

```text
q_p = ccm24PrimeEulerCoefficient(p) = p^(-1/2),
C_p = primeEulerRadialBoundaryStep,
V_p = primeEulerRadialTail.
```

Then

```text
FiniteColumn_(p,S,N) x = 0
  <-> forall n < N,
        C_p V_p^n newFrame_S x = 0.
```

The positive Euler weights do not change the kernel.  More importantly, the
complete geometric radial response has the exact finite-prefix identity

```text
G_p
  = sum_(n < N) q_p^(n+1) C_p V_p^n
    + q_p^N G_p V_p^N.
```

Therefore, on the finite-column kernel,

```text
G_p(newFrame_S x)
  = q_p^N G_p(V_p^N newFrame_S x).
```

The first `N` coordinates vanish, but the complete renewal becomes the
unobserved tail.  No algebraic recurrence makes that tail zero.

## Actual whole-line kernel

Proof 643 also works directly on the genuine whole-line `L2` carrier.  Define
an `N`-cell radial margin by

```text
u(t) = 0  for almost every
t < log(lambda) + N log(p).
```

One positive prime translation consumes one cell.  Induction gives

```text
margin_N(u)
  -> C_p V_p^n u = 0  for every n < N.
```

Hence every actual suffix-frame vector with this margin lies in the kernel:

```text
margin_N(newFrame_S x)
  -> FiniteColumn_(p,S,N) x = 0.
```

This is not a toy dimension argument.  It uses the literal CCM24 support
condition, the actual global logarithmic translation, the actual orthogonal
radial projection, and the actual boundary/tail operators.

```text
 support begins here
          |
          v
  [cell 0][cell 1] ... [cell N-1][cell N][cell N+1] ...
  +------------------------------+------------------------>
  |       finite column sees     |       unseen tail
  +------------------------------+------------------------>
                                  |
                                  v
                              q_p^N G_p V_p^N
```

## Consequence for Proof 641

A bounded factor through Proof 639's finite column would force

```text
CompleteCofactor_(p,S) x = 0
```

for every suffix-frame vector with the displayed `N`-cell margin.  Conversely,
one such vector on which the complete coupled cofactor survives rules out
every bounded readout through that fixed column, at every proposed bound.

The exact missing producer is therefore one of the following source results:

1. a genuine operator-level cutoff proving that the complete coupled
   outer/reflected/second-support/prolate cofactor annihilates the whole
   radial tail after some explicit `N`; or

2. a proof that no complete-cofactor survivor exists in the explicit
   deep-margin kernel.

Compactness and the uniform norm bound `32` prove neither statement.  Scalar
trace cancellation also does not imply operator annihilation.

## What was not proved

Proof 643 does not construct an actual complete-cofactor survivor.  It also
does not prove that a compact detector cuts off the second-support/prolate
owner at operator level.  Consequently it does not disprove every possible
finite-column factorization; it proves exactly why the existing source
geometry cannot establish one without a new tail-annihilation theorem.

The second-support and prolate branches remain coupled throughout the
complete cofactor.  Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and
RH remain open.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorFiniteRadialKernelTail.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorFiniteRadialKernelTailAudit.lean
```

The central audited declarations are

```text
finiteRadialColumn_eq_zero_iff_first_boundary_blocks_eq_zero
primeEulerRadialGeometricBoundary_eq_prefix_add_tail
geometricBoundary_apply_eq_tail_of_finiteRadialColumn_eq_zero
finiteRadialColumn_eq_zero_of_newFrame_hasPrimeRadialCellMargin
no_finiteRadialReadoutData_of_margin_cofactor_survivor
```

## Verification

The focused Ubuntu-24.04 WSL2 ext4 build passed under the shared Lake lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| finite radial kernel/tail source     |  3393 | PASS   |
| focused fourteen-declaration audit   |  3394 | PASS   |
+--------------------------------------+-------+--------+
```

All fourteen audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
