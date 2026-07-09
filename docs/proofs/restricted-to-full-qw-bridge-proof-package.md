# Restricted To Full QW Bridge Proof Package

Status: route-evidence proof package for the fixed-test bridge from
`QW_lambda(g,g)` to `QW(g,g)`.

This package proves the project-level target stated in:

```text
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
```

It is not a CCM25 source import. It is not a Lean theorem. It does not prove
finite-operator spectral convergence, determinant convergence, or RH.

## Result

Good result:

```text
RestrictedToFullQWBridgeContract is closed at route-evidence level.
```

Boundary:

```text
Accepted source-import status remains open.
Lean proof status remains open.
Final CC20 sign exit remains separate.
The RH proof is not complete.
```

## Target

For a fixed source test:

```text
g,
F_g = g^* * g,
```

prove that there is a fixed-test threshold `lambda0(g,F_g)` such that:

```text
forall lambda >= lambda0,
  QW_lambda(g,g) = QW(g,g).
```

The proof must not use:

```text
finite-operator spectral convergence,
determinant convergence,
or convergence of spectra to zeta zeros.
```

## Evidence Boundary

| claim | evidence |
|---|---|
| CCM25 source path is restriction-definition, not spectral convergence | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` |
| theorem target and rejected imports | `docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md` |
| bridge decomposition | `docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md` |
| common source test and square | `docs/proofs/source-common-test-tuple-theorem-contract.md`; `docs/proofs/source-test-convolution-compatibility.md` |
| source objects and windows | `docs/proofs/source-object-definition-theorem-contract.md`; `docs/proofs/ccm24-support-window-transport-discharge.md` |
| finite-prime normalization | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md`; `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` |

## Proof Skeleton

```text
fix g and F_g
        |
        v
choose lambda0 covering supp(g) and visible supp(F_g)
        |
        v
g lies in L2([lambda^-1,lambda],d^*u)
        |
        v
restricted finite-prime atoms equal global visible atoms
        |
        v
QW_lambda is QW restricted to the same vector
        |
        v
QW_lambda(g,g) = QW(g,g)
```

## Lemma 1. Fixed-Test Support Threshold

Statement:

```text
RestrictedToFullQWLambdaThreshold(S,I,g,F_g):
  exists lambda0,
    forall lambda >= lambda0,
      supp(g) subset [lambda^-1,lambda]
      and supp(F_g) subset [lambda^-2,lambda^2].
```

Proof.

The route fixes `g` before taking the `lambda` limit. The common-test contract
identifies:

```text
F_g = g^* * g.
```

Evidence:

```text
docs/proofs/source-common-test-tuple-theorem-contract.md
docs/proofs/source-test-convolution-compatibility.md
```

The source-object contract fixes the route tuple and support window before the
limit:

```text
(S,I,lambda,g,F_g).
```

Evidence:

```text
docs/proofs/source-object-definition-theorem-contract.md
```

Since `g` is fixed and compactly supported in the multiplicative coordinate,
choose `lambda0` large enough that:

```text
supp(g) subset [lambda0^-1, lambda0].
```

Then for every `lambda >= lambda0`:

```text
supp(g) subset [lambda^-1, lambda].
```

The convolution square has support in the product support:

```text
supp(F_g) subset [lambda^-2, lambda^2].
```

Output:

```text
fixed_test_threshold
same_g_before_limit
same_F_g_before_limit
support_containment_for_restricted_space
```

## Lemma 2. Visible Prime-Power Support Stabilizes

Statement:

```text
RestrictedFinitePrimeSupportStabilizes(g,F_g):
  exists lambda0,
    forall lambda >= lambda0,
      restrictedPrimeIndexSet(lambda,F_g)
        =
      globalPrimeIndexSet(F_g)
```

for the source prime-power atoms visible to `F_g`.

Proof.

The finite-prime normalization contract requires pointwise source atoms:

```text
source prime-power atom
visible in F_g
restricted lambda cut
Lambda(n)
<g|T(n)g>
```

Evidence:

```text
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md
```

For fixed compactly supported `F_g`, only finitely many source prime-power
atoms are visible. Choose `lambda0` so that every visible atom satisfies the
restricted CCM25 cut:

```text
1 < n <= lambda^2.
```

Then the restricted index set contains exactly the global visible atoms for
this fixed test. No spectral information enters this choice.

Output:

```text
finite_prime_threshold
global_visible_atoms_equal_restricted_atoms
pointwise_term_equality_before_summing
no_lambda_dependent_place_set
```

## Lemma 3. Restricted Form Is The Full Form On The Same Vector

Statement:

```text
RestrictedToFullQWScalarRestrictionEquality(S,I,lambda,g,F_g):
  lambda >= lambda0
  ->
  QW_lambda(g,g) = QW(g,g).
```

Proof.

The source-readiness audit records the CCM25 source path:

```text
QW_lambda is the restriction of QW to
L2([lambda^-1,lambda],d^*u).
```

Evidence:

```text
docs/audits/restricted-to-full-qw-source-readiness-audit.md
```

By Lemma 1, the fixed source test `g` lies in the restricted Hilbert interval
for every `lambda >= lambda0`.

By Lemma 2, the finite-prime atoms in the restricted formula are the same
visible atoms as in the full formula for this fixed `F_g`, with the same
pointwise term:

```text
Lambda(n)<g|T(n)g>.
```

The archimedean and pole terms use the same source convention because the
bridge consumes the same common source test and the CCM25 restricted read-off
contract.

Therefore the restricted scalar form and the full scalar form evaluate the
same source quadratic expression:

```text
QW_lambda(g,g) = QW(g,g).
```

This is an eventual identity for the fixed test, not a spectral limit.

## Lemma 4. Lower Bound Transfers To Full QW

Statement:

```text
RestrictedToFullQWLowerBoundTransfer(S,I,lambda,g,F_g,J):
  QW_lambda(g,g) >= -C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g)
  ->
  Cdef_(S,I,lambda,J)(g) -> 0
  ->
  QW_lambda(g,g) = QW(g,g)
  ->
  QW(g,g) >= 0.
```

Proof.

For every `lambda >= lambda0`, Lemma 3 gives:

```text
QW(g,g) = QW_lambda(g,g).
```

Row 7 gives the finite-lambda lower bound after ledger killing:

```text
QW_lambda(g,g) >= -C Cdef(lambda,g).
```

Row 6 supplies fixed-test `Cdef` exhaustion:

```text
Cdef(lambda,g) -> 0.
```

Taking `lambda -> infinity` along values larger than `lambda0` gives:

```text
QW(g,g) >= 0.
```

No finite-operator spectral convergence appears in the argument.

## Theorem. Restricted To Full QW Bridge

Statement:

```text
RestrictedToFullQWBridgeContract(S,I,lambda,g,F_g,J):
  exists lambda0,
    forall lambda >= lambda0,
      QW_lambda(g,g) = QW(g,g),
```

and the Row 7 lower bound transfers to:

```text
QW(g,g) >= 0.
```

Proof.

Combine Lemmas 1 through 4.

The proof uses:

```text
common source test,
fixed support threshold,
finite-prime pointwise support equality,
CCM25 restriction definition,
Row 7 lower bound,
Row 6 fixed-test Cdef exhaustion.
```

It does not use:

```text
spectral convergence,
determinant convergence,
zero convergence,
or RH.
```

## Output To The Route

This package supplies, at route-evidence level:

```text
RestrictedToFullQWBridgeContract
RestrictedToFullQWEventualIdentity
RestrictedToFullQWLowerBoundTransfer
FullQWNonnegativity_route_evidence
```

It does not supply:

```text
accepted_source_import_discharge
Lean_theorem
CC20FiniteVanishingExit
RiemannHypothesis
```

## Current Status

```text
Same source test:                       route-evidence available
Fixed-test lambda threshold:            proved at route-evidence level
Finite-prime support stabilization:     proved at route-evidence level
Scalar restriction equality:            proved at route-evidence level
Lower-bound transfer to full QW:         proved at route-evidence level

Accepted source-import status:          open
Lean proof status:                      open
CC20 final sign/RH exit:                open
RH proof:                               not complete
```
