# Proof 621: antiresonant adjacent boundary bracket comparison

## Result

The result is good as an exact divide-and-conquer normal form.  It does not
supply either missing uniform estimate.

Define the complete source-side suffix response

```text
B_S
  = -Endpoint_S^dagger * ThreeBranch * sourceInclusion
    + sourceInclusion^dagger * ThreeBranch * Forward_S.
```

The existing raw-response readback proves that `B_S` is exactly the actual
coframe boundary moment.  Taking the adjoint of the genuine scalar inverse

```text
Reverse_(p,S) * Transition_(p,S) = rho_p * I
```

gives the orientation required by the interior owner:

```text
Transition_(p,S)^dagger * Reverse_(p,S)^dagger = rho_p * I.
```

Combining this with Proof 619 yields

```text
Interior_(p,S)
  = rho_p * B_S
    - Transition_(p,S)^dagger
        * B_(p::S)
        * Reverse_(p,S)^dagger.
```

This is the genuine actual-owner theorem.  All endpoint, forward, transition,
and reverse-transition dressing remains visible.

## Corrected bracket comparison

Proof 620's corrected quotient bracket acts on the global carrier.  Proof 621
first applies the canonical source compression

```text
Q_p^src = sourceInclusion^dagger * Q_p * sourceInclusion.
```

Its physical ledger is inherited exactly from Proof 620.  For each suffix,
define the dressing residual

```text
Delta_(p,S) = B_S - Q_p^src.
```

Lean then proves the exact two-channel split

```text
Interior_(p,S)
  = CovarianceDefect_(p,S) + DressingDefect_(p,S),

CovarianceDefect_(p,S)
  = rho_p * Q_p^src
    - Transition_(p,S)^dagger
        * Q_p^src
        * Reverse_(p,S)^dagger,

DressingDefect_(p,S)
  = rho_p * Delta_(p,S)
    - Transition_(p,S)^dagger
        * Delta_(p,p::S)
        * Reverse_(p,S)^dagger.
```

## What this changes

```text
+--------------------------------------+-----------------------------------+
| previous question                    | exact replacement                 |
+--------------------------------------+-----------------------------------+
| Is the radial bracket the Interior?  | No: carrier and S dressing differ |
| What is the true Interior?           | One adjacent complete response    |
| What does Q_p leave unresolved?      | covariance + dressing defects     |
| Can either defect be set to zero?    | no source theorem exists          |
| Can either be bounded uniformly?     | not yet                           |
+--------------------------------------+-----------------------------------+
```

The next source work has two precise options:

1. Prove a common family-uniform readout for the signed sum of the two
   defects.
2. Prove compatible uniform readouts for both defects through the same old-
   carrier analysis and add them only afterward.

A standalone operator-norm bound for either channel is not the required
Douglas factorization.

## Lean build boundary

Substituting the expanded three-branch response before pointwise operator
algebra triggered deterministic `isDefEq` timeouts.  The successful proof
keeps the raw boundary moments opaque, proves the adjacent identity first,
and substitutes the physical response using `congrArg₂`.  The generic
two-channel algebra is likewise proved on five opaque endomorphisms before
the CCM24 owners are instantiated.

## Files

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse.lean
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRadialBracketComparison.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponseAudit.lean
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRadialBracketComparisonAudit.lean
```

## Boundary

Proof 621 proves no uniform norm estimate and constructs no instance of
`SuffixRawOldCarrierCoframeUniformJointGapReadoutData`.  Bone 1, Gate 3U, the
finite-S sign, Burnol's identity, and RH remain open.

## Verification

The Ubuntu-24.04 WSL2 ext4 acceptance batch passes:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| six focused source/audit targets     |  3391 | PASS   |
| CCM25Concrete aggregate              |  3891 | PASS   |
| full repository                      |  3972 | PASS   |
+--------------------------------------+-------+--------+
```

Every audited concrete theorem uses exactly
`[propext, Classical.choice, Quot.sound]`.
