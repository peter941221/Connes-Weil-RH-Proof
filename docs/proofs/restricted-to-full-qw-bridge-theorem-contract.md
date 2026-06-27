# Restricted To Full QW Bridge Theorem Contract

Status: theorem contract for the bridge from CCM25's restriction definition to
the route's fixed-test eventual identity.

This file is narrower than:

```text
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
```

That contract states the target. This bridge contract states the exact
composition needed to reach the target from existing source-object contracts.
It does not prove CCM25 spectral convergence, determinant convergence, or any
finite-operator zero convergence.

## Boundary

The route needs this implication:

```text
CCM25 restriction definition
  + common source test
  + one fixed route tuple and window
  + finite-prime support equality
        |
        v
exists lambda0,
  forall lambda >= lambda0,
    QW_lambda(g,g) = QW(g,g).
```

The bridge is not allowed to use:

```text
spectra of finite operators converge to zeta zeros
determinants converge to Xi
RH-equivalent convergence statements
```

Those are strategy or numerical-convergence claims in CCM25, not importable
theorems for this fixed-test scalar passage.

## Evidence Lock

| item | evidence |
|---|---|
| restricted-to-full source-readiness audit | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` |
| scalar target contract | `docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md` |
| common-test and fixed-tuple contract | `docs/proofs/source-common-test-tuple-theorem-contract.md` |
| source-object definition contract | `docs/proofs/source-object-definition-theorem-contract.md` |
| finite-prime normalization contract | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` |
| source import legitimacy audit | `docs/audits/source-import-legitimacy-audit.md` |
| formal-gate spine audit | `docs/audits/formal-gate-spine-consistency-audit.md` |

## Inputs

The bridge consumes these theorem targets.

### Input 1. Same Test And Square

```text
SourceCommonTestTupleContract(S,I,lambda,g,F_g)
```

Required projections:

```text
SourceCommonTestObject(g,F_g)
SourceConvolutionSquareOwned(g,F_g)
SourceRouteTupleFixed(S,I,lambda,g)
SourceTupleCarriesWindowAndSquare(S,I,lambda,g,F_g)
```

Purpose:

```text
QW_lambda(g,g) and QW(g,g) must be evaluated on the same source object
F_g = g^* * g.
```

### Input 2. Source Window Controls The Restricted Route

```text
SourceWindowControlsRestrictedRoute(S,I,lambda,g)
```

Required projections:

```text
supp(g) subset I
Fourier support of g lies in I
convolution support of F_g is transported through I
I subset [lambda^(-1), lambda]
ccm24Window_controls_qwLambda
ccm24Window_controls_finitePrimeVisibility
```

Purpose:

```text
The same fixed source window that makes the positive trace admissible also
places g inside the CCM25 restricted Hilbert interval.
```

### Input 3. CCM25 Restricted Form Is A Restriction

Target:

```text
SourceQWLambdaIsRestrictionOfQW(lambda,g):
  if g lies in L^2([lambda^(-1),lambda],d^*u),
  then the scalar restricted form is the full form restricted to that vector.
```

Scalar conclusion:

```text
QW_lambda(g,g) = QW(g,g)
```

after the support containment hypotheses from Input 2.

Purpose:

This is the source-definition leg. It is different from spectral convergence.
It says that the restricted form is the restriction of the same full form on a
vector already in the restricted space.

### Input 4. Finite-Prime Supports Match The Same Source Cut

```text
CCM25FinitePrimeNormalizationContract(lambda,g)
```

Required projections:

```text
SourceGlobalPrimePowerSupport(g)
SourceRestrictedPrimePowerSupport(lambda,g)
SourceVisiblePrimePowerBeforeLambdaCut(lambda,g)
FixedSVisiblePrimeSetBeforeLimit(lambda,g)
SourceFinitePrimeTermPointwiseNormalization(lambda,g)
SourceFinitePrimeFormulaOwnsSign(lambda,g)
```

Purpose:

The finite-prime comparison must be pointwise before summing:

```text
source prime-power atom
  -> visible in F_g
  -> in global support
  -> in restricted lambda cut once lambda is large enough
  -> same Lambda(n)<g|T(n)g> term
```

The bridge cannot use a sum-level equality that hides wrong atoms, weights,
pairings, or signs.

## Bridge Theorem 1. Fixed-Test Lambda Threshold

Target:

```text
RestrictedToFullQWLambdaThreshold(S,I,g,F_g):
  SourceCommonTestTupleContract(S,I,lambda,g,F_g)
  -> SourceWindowControlsRestrictedRoute(S,I,lambda,g)
  -> CCM25FinitePrimeNormalizationContract(lambda,g)
  -> exists lambda0,
       forall lambda >= lambda0,
         g lies in L^2([lambda^(-1),lambda],d^*u)
         and every source prime-power atom visible to F_g
             lies in restrictedPrimeIndexSet(lambda,F_g).
```

Meaning:

The threshold is a fixed-test threshold. It may depend on `g`, `F_g`, and the
fixed support data. It may not depend on a moving finite-operator spectrum or a
moving zero approximation.

## Bridge Theorem 2. Scalar Restriction Equality

Target:

```text
RestrictedToFullQWScalarRestrictionEquality(S,I,lambda,g,F_g):
  SourceQWLambdaIsRestrictionOfQW(lambda,g)
  -> SourceCommonTestTupleContract(S,I,lambda,g,F_g)
  -> SourceWindowControlsRestrictedRoute(S,I,lambda,g)
  -> CCM25FinitePrimeNormalizationContract(lambda,g)
  -> lambda >= lambda0
  -> QW_lambda(g,g) = QW(g,g).
```

Meaning:

The proof must be scalar and termwise:

```text
archimedean term: same source convention
pole term: same source convention
finite-prime term: same visible prime-power atoms and same pointwise terms
```

If any term changes convention between the restricted and full forms, the
bridge fails.

## Bridge Theorem 3. Lower Bound Transfer

Target:

```text
RestrictedToFullQWLowerBoundTransfer(S,I,lambda,g,F_g,J):
  (forall lambda >= lambda0,
     QW_lambda(g,g) >= -C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g))
  -> FixedTestCdefExhaustion(S,I,g,J)
  -> RestrictedToFullQWScalarRestrictionEquality(S,I,lambda,g,F_g)
  -> QW(g,g) >= 0.
```

Meaning:

Once eventual equality is proved, the route can transfer the fixed-test lower
bound to the full form without appealing to spectral convergence.

The exact order is:

```text
positive trace read-off
  -> QW_lambda(g,g) >= -Cdef(lambda,g)
  -> Cdef(lambda,g) -> 0
  -> eventual equality QW_lambda(g,g)=QW(g,g)
  -> QW(g,g) >= 0.
```

## Combined Bridge Contract

The formal/import target is:

```text
RestrictedToFullQWBridgeContract(S,I,lambda,g,F_g,J):
  RestrictedToFullQWLambdaThreshold(S,I,g,F_g)
  SourceQWLambdaIsRestrictionOfQW(lambda,g)
  RestrictedToFullQWScalarRestrictionEquality(S,I,lambda,g,F_g)
  RestrictedToFullQWLowerBoundTransfer(S,I,lambda,g,F_g,J)
```

Projection target:

```text
RestrictedToFullQWBridgeContract(S,I,lambda,g,F_g,J)
  ->
RestrictedToFullQWExhaustionContract(g).
```

## Import Acceptance Checklist

| requirement | required evidence |
|---|---|
| same source test | `QW_lambda`, `QW`, finite-prime support, and trace read-off use the same `g` and `F_g=g^* * g` |
| same tuple and window | `(S,I,lambda,g)` comes from one source package, and `I` is the window used by restricted `QW_lambda` |
| restriction definition | a source theorem or formal bridge states `QW_lambda` is the scalar restriction of `QW` on the restricted Hilbert interval |
| finite-prime termwise equality | global and restricted prime-power supports are two-sided source supports and pointwise terms match before summing |
| lambda threshold | `lambda0` comes from fixed support of `g` and `F_g`, not from spectral convergence |
| lower-bound transfer | uses eventual scalar equality and `Cdef` exhaustion only |
| rejected imports | no finite spectral convergence, determinant convergence, or zero convergence theorem is used |

## Current Judgment

| question | answer |
|---|---|
| Does this bridge prove `QW_lambda(g,g)=QW(g,g)`? | at route-evidence level via `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` |
| Does it state the missing composition between existing contracts? | yes |
| Does it keep CCM25 spectral convergence out of the proof? | yes |
| Does it reduce the source-import blocker? | yes, by isolating the exact bridge still needed |
| Can the route treat the bridge as accepted-source or Lean discharged now? | no |

The restricted-to-full gate is now split into:

```text
source-definition path found
  +
bridge contract stated
  +
route-evidence proof package written
  +
formal/import discharge still open.
```
