# Restricted-To-Full Accepted-Source Packet

Date: 2026-06-28

Status:

```text
restricted-to-full accepted-source packet started
accepted-source certification: open
Lean status: not touched
```

## Purpose

This packet targets the theorem candidate:

```text
RestrictedToFullQWAcceptedTheorem(g,F_g):
  exists lambda0,
  forall lambda >= lambda0,
    QW_lambda(g,g) = QW(g,g).
```

The theorem must use the CCM25 restriction definition and fixed-test support.
It must not use finite-operator spectral convergence, determinant convergence,
or eigenvalue convergence to zeta zeros.

## Source Anchors

| source | lines | role |
|---|---:|---|
| `mc2arXiv.tex` | `400-428` | Weil class and explicit formula for compact convolution tests |
| `mc2arXiv.tex` | `464-470` | `QW(f,g)=Psi(f^**g)` and `Psi` |
| `mc2arXiv.tex` | `496-529` | source convolution expression for `QW(kappa(f),kappa(g))` |
| `mc2arXiv.tex` | `530-535` | `QW_lambda` as the restriction of `QW` to `L^2([lambda^-1,lambda],d^*u)` |
| `mc2arXiv.tex` | `535-540` | restricted formula, finite sum `1<n<=lambda^2`, and `T(n)` pairing |
| `mc2arXiv.tex` | `266-272,302-303` | spectral convergence and determinant convergence appear as strategy or numerical program material, not as imported theorem input |

Primary source page:

```text
https://arxiv.org/abs/2511.22755
```

## Theorem Shape

For a fixed source test:

```text
g
F_g = g^* * g
```

the accepted-source theorem must prove:

```text
RestrictedToFullQWAcceptedTheorem(g,F_g):
  compact_support(g)
  same_source_square(F_g,g)
  finite_prime_support_stabilizes(F_g)
  ->
  exists lambda0,
  forall lambda >= lambda0,
    QW_lambda(g,g) = QW(g,g).
```

This is an eventual identity for one fixed test. It is not a spectral limit.

## Certification Chain

| row | theorem candidate | current evidence | accepted-source check |
|---|---|---|---|
| common test | `SourceCommonTestObject(g,F_g)` | `docs/proofs/source-test-convolution-compatibility.md`; `docs/proofs/source-common-test-tuple-theorem-contract.md` | confirm the `g` entering CCM25 `QW`, CCM25 `QW_lambda`, and CC20 trace read-off is one source object |
| support containment | `FixedTestSupportContained(g,lambda0)` | `docs/proofs/source-object-definition-theorem-contract.md`; `docs/proofs/ccm24-support-window-transport-discharge.md` | confirm `supp(g) subset [lambda^-1,lambda]` for every `lambda >= lambda0` |
| convolution-square support | `FixedSquareSupportContained(F_g,lambda0)` | `docs/proofs/source-test-convolution-compatibility.md` | confirm `F_g` has support compatible with the restricted finite-prime cutoff for large `lambda` |
| CCM25 restriction definition | `CCM25QWLambdaRestrictionDefinition(lambda,g)` | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` | confirm source `QW_lambda` is the restriction of `QW`, not a finite-dimensional approximation |
| finite-prime stabilization | `FixedTestFinitePrimeSupportStabilization(lambda,g,F_g)` | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md`; `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` | confirm restricted finite-prime atoms equal the global visible atoms for the fixed test once `lambda` is large |
| pole and archimedean convention | `SamePoleArchimedeanConvention(lambda,g)` | `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md`; `docs/proofs/final-sign-bridge-proof-package.md` | confirm the restricted and full forms use the same source pole and archimedean sign convention |
| no spectral input | `NoSpectralConvergenceImported` | `docs/audits/source-import-legitimacy-audit.md`; `docs/audits/second-external-opinion-audit.md` | confirm the proof never uses finite matrices, determinant convergence, eigenvalue convergence, or even-sector assumptions |

## Rejection Conditions

A reviewer should reject this row if any one of these conditions occurs:

```text
1. QW_lambda is treated as a spectral approximation rather than a restriction;
2. the fixed test used in QW_lambda differs from the test used in QW;
3. support containment holds only after varying the test;
4. the finite-prime restricted sum omits or duplicates a visible atom of F_g;
5. the pole or archimedean sign convention changes between restricted and full forms;
6. the proof imports finite-operator spectral convergence, determinant convergence,
   numerical eigenvalue convergence, or an even-sector minimum-eigenvector claim.
```

Any rejection here stops the route before the final sign bridge, because the
finite-lambda lower bound would not transfer to the global scalar `QW(g,g)`.

## Accepted-Source Questions

| question | required answer for acceptance |
|---|---|
| Does CCM25 define `QW_lambda` as a restriction of `QW` on the interval? | yes |
| Does the fixed route test lie in that interval for all large `lambda`? | yes |
| Does `F_g` determine the same visible finite-prime atoms in restricted and full formulas? | yes |
| Do pole and archimedean terms keep the same source convention? | yes |
| Does the proof avoid finite-dimensional spectral convergence? | yes |
| Does the theorem return equality of global scalar values for the same `g`? | yes |

## Current Judgment

| question | answer |
|---|---|
| Does this packet make `QW_lambda=QW` accepted-source? | no |
| Does it give an exact accepted-source review packet? | yes |
| What remains? | external acceptance of the common-test, support, finite-prime, and restriction-definition bridges |
| Did this pass touch Lean? | no |

The restricted-to-full gate now has a source-review packet that separates the
fixed-test scalar identity from the CCM25 spectral program.
