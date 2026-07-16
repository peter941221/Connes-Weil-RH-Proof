# Proof 314: unitary two-support Sonin producer

Date: 2026-07-16

Status: given a genuine unitary second-support transport `U`, the half-line
projection `P`, transported projection `Q_U`, Sonin intersection projection
`R_U`, and positive prolate remainder `K_U` are now axiom-clean Lean objects
on the same global logarithmic `L2` carrier.  Proof 313's complete signed
commutator and `-2` residue ledger are instantiated by those objects.

The actual CCM24 finite-`S` scattering transport `U_S` is not yet constructed.

## 1. What was missing

Before Proof 314, the existing indicator map

```text
P = cc20PositiveHalfLineProjection
```

was known to be bounded and idempotent, but it had no self-adjointness theorem.
Therefore it could not yet serve as a certified orthogonal support projection
inside the `E/Q/R/K_prol` geometry.

Proof 314 proves directly from the indicator kernel that

```text
P^2 = P,
P^dagger = P.
```

Hence `P` is a star projection, meaning an orthogonal projection represented
as a continuous linear map.

## 2. Unitary second-support construction

For any unitary coordinate transport

```text
U : globalLogL2 equiv globalLogL2,
```

define

```text
Q_U = U^dagger P U.
```

Lean proves that `Q_U` is again idempotent and self-adjoint.  The ranges of
`P` and `Q_U` are closed because they are ranges of continuous idempotents.

The two-support subspace is therefore the genuine closed intersection

```text
S_U = Ran(P) intersection Ran(Q_U).
```

Mathlib's Hilbert-space projection theorem supplies its orthogonal projection

```text
R_U = projection onto S_U.
```

The result is not a finite-dimensional surrogate.  `R_U` acts on the same
whole-line logarithmic Hilbert space as `P` and `Q_U`.

## 3. Positive prolate remainder

Define the remainder

```text
K_U = P Q_U P - R_U.
```

Since `Ran(R_U)` lies in both support ranges, Proof 314 proves all four
absorption identities:

```text
P R_U = R_U,    R_U P = R_U,
Q_U R_U = R_U,  R_U Q_U = R_U.
```

They give the stronger factorization

```text
K_U = (P-R_U) Q_U (P-R_U).
```

Because `Q_U` is positive, the factorization proves

```text
K_U >= 0.
```

Thus `K_U` is self-adjoint and positive by construction.  Compactness and the
CC20 rapid singular-value bound are not consequences of this abstract unitary
geometry and remain source obligations.

## 4. Same-object three-branch response

The definition gives the exact identity

```text
R_U = P Q_U P - K_U.
```

Proof 314 feeds this identity into Proof 313 and obtains, for every bounded
detector `W`,

```text
[R_U,W]
  = P Q_U [P,W]
    + P [Q_U,W] P
    + [P,W] Q_U P
    - [K_U,W].
```

The residue-augmented root pairing is instantiated at the same time:

```text
inner(eta,[R_U,W]xi) - 2 inner(eta,xi)
  = complete three-branch pairing - 2 inner(eta,xi).
```

No branchwise absolute value is used.

## 5. Rejected false specialization

An intermediate draft specialized `U` to Mathlib's ordinary additive
`Lp.fourierTransformLi`.  That specialization was removed before delivery.

CCM24's semilocal Sonin comparison uses a Hardy--Titchmarsh/scattering
transport.  The repository has no theorem identifying it with the ordinary
Fourier transform on the current logarithmic carrier.  Keeping `U` explicit
prevents a false same-object claim.

Primary source:

```text
Connes--Consani--Moscovici,
Zeta zeros and prolate wave operators: Semilocal adelic operators, v2
https://arxiv.org/abs/2310.18423v2
```

The projection/prolate source formula is summarized with source locations in
`docs/proofs/257_two_boundary_q_preserving_flow.md`.

## 6. Lean declarations

The main declarations in `GlobalLogSoninProjection.lean` are

```text
cc20PositiveHalfLineProjection_isSelfAdjoint
cc20PositiveHalfLineProjection_isStarProjection
cc20TransportedHalfLineProjection
cc20TransportedHalfLineProjection_isStarProjection
cc20TransportedSoninClosedSubspace
cc20TransportedSoninProjection
cc20TransportedSoninProjection_isStarProjection
cc20TransportedSoninProjection_apply_mem_both
cc20TransportedProlateRemainder
cc20TransportedProlateRemainder_isSelfAdjoint
cc20TransportedProlateRemainder_eq_complement_conjugation
cc20TransportedProlateRemainder_isPositive
cc20TransportedSonin_eq_supports_sub_prolate
cc20TransportedSonin_commutator_eq_threeBranch
cc20TransportedSonin_residueResponse_eq_threeBranch
```

## 7. Verification

Focused WSL2 ext4 build:

```text
lake build ConnesWeilRH.Source.CC20Concrete.GlobalLogSoninProjection \
           ConnesWeilRH.Dev.GlobalLogSoninProjectionAudit

Build completed successfully (3125 jobs).
```

Aggregate build:

```text
lake build ConnesWeilRH.Source.CC20Concrete

Build completed successfully (3606 jobs).
```

The audited declarations depend only on

```text
[propext, Classical.choice, Quot.sound]
```

and introduce no `sorryAx` or project axiom.

## 8. Route boundary

```text
+--------------------------------------------------------------+
| CLOSED                                                       |
|  concrete indicator half-line orthogonal projection P       |
|  Q_U = U^dagger P U for any supplied unitary U              |
|  genuine closed-intersection orthogonal projection R_U       |
|  positive K_U = P Q_U P - R_U                               |
|  instantiated three-branch and -2 residue ledger             |
+--------------------------------------------------------------+
| OPEN                                                         |
|  actual CCM24 finite-S scattering unitary U_S                |
|  identification of Q_(U_S) with the source second support    |
|  compactness and rapid singular values of K_(U_S)            |
|  trace-class legality and moving divided-difference match    |
|  Gate 3U, finite-S sign, Burnol identity, and RH             |
+--------------------------------------------------------------+
```

Proof 314 reduces the source-geometry construction from three missing
operators `Q/R/K_prol` to one missing source transport `U_S` plus its compact
spectral theorem.  It does not supply that transport or prove RH.

Final route status:

```text
RH=UNPROVED
```
