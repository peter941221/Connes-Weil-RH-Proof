# CCM25 Source-Interface Accepted-Source Packet

Date: 2026-06-28

Status:

```text
CCM25 accepted-source packet started
accepted-source certification: open
Lean status: not touched
```

## Purpose

This packet targets the CCM25 source-interface theorem candidates for:

```text
QW
Psi
QW_lambda
finite-prime atoms
pole normalization
sign ownership
```

It separates formula definitions from the CCM25 spectral program. Numerical
eigenvalue convergence, determinant convergence, and even-sector assumptions
are not inputs to this packet.

## Source Anchors

| source | anchors | role |
|---|---|---|
| Weil class and compact convolution tests | `mc2arXiv.tex:400-428` | source test class and explicit formula context |
| global `QW` and `Psi` | `mc2arXiv.tex:445-470` | `QW`, `Psi`, local signs, pole, and finite-prime pieces |
| source convolution expression | `mc2arXiv.tex:496-529` | `QW(kappa(f),kappa(g))` expression |
| restricted `QW_lambda` | `mc2arXiv.tex:530-540` | restriction to `L^2([lambda^-1,lambda],d^*u)`, pole term, finite sum, and `T(n)` pairing |
| spectral program boundary | `mc2arXiv.tex:266-272,302-303` | numerical/spectral strategy material, not importable theorem input |

## Certification Chain

| row | theorem candidate | current evidence | accepted-source check |
|---|---|---|---|
| global definition | `CCM25QWDefinitionTheorem(g,F_g)` | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` | confirm `QW(g,g)=Psi(F_g)` with the route convolution square |
| `Psi` sign expansion | `CCM25PsiSignExpansionTheorem(F_g)` | `docs/proofs/final-sign-bridge-spine-discharge.md` | confirm finite-prime, archimedean, and pole signs are source-owned |
| restricted form | `CCM25QWLambdaFormulaTheorem(lambda,g,F_g)` | `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md`; `docs/audits/restricted-to-full-qw-source-readiness-audit.md` | confirm `QW_lambda` is the source restriction of `QW` and has the displayed finite-prime and pole terms |
| finite-prime atom | `CCM25FinitePrimeTermTheorem(lambda,g,n)` | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md`; `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` | confirm each atom is indexed once with source `Lambda(n)<g|T(n)g>` |
| finite-prime support | `CCM25VisiblePrimeSupportTheorem(lambda,F_g)` | `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` | confirm restricted and global prime-power supports use the same visible source atoms for fixed `F_g` |
| pole normalization | `CCM25PoleNormalizationTheorem(lambda,g)` | `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` | confirm source pole term sits inside `QW_lambda` and is separated from route `PoleJetExtra` |
| no spectral import | `CCM25NoSpectralInputForScalarRoute` | `docs/audits/source-import-legitimacy-audit.md`; `docs/audits/second-external-opinion-audit.md` | confirm scalar `QW_lambda -> QW` uses restriction-definition, not spectral convergence |

## Rejection Conditions

A reviewer should reject this packet if one of these conditions occurs:

```text
1. route `QW` or `Psi` uses a different test than source `F_g`;
2. `QW_lambda` is treated as a spectral approximation instead of a restriction;
3. finite-prime atoms are omitted, duplicated, or assigned the wrong weight;
4. pole terms are counted twice or assigned the wrong sign;
5. finite-operator spectral convergence, determinant convergence, or
   even-sector assumptions enter a scalar theorem.
```

## Current Judgment

| question | answer |
|---|---|
| Does this packet make CCM25 accepted-source? | no |
| Does it give an exact accepted-source review packet? | yes |
| What remains? | external acceptance of the definitions, finite-prime normalization, pole normalization, and no-spectral boundary |
| Did this pass touch Lean? | no |

The CCM25 packet now gives reviewers a single place to certify the Weil-form
objects before checking trace-scale, restricted-to-full, and final sign packets.
