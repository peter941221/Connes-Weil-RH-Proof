# Trace Scale Compatibility Discharge Attempt

Date: 2026-06-28

Status:

```text
B1 discharge: closed at project proof-package level
theorem contract: written
proof package: written
Lean status: not started
```

## Question

This audit tests whether existing proof packages already discharge:

```text
docs/proofs/trace-scale-compatibility-theorem-contract.md
```

The first pass answer was no. Existing documents covered trace legality, the
restricted `QW_lambda` read-off, and the Rows 3-7 no-hidden-defect chain, but
they did not yet isolate the ordinary-to-source convention conversion ledger or
the no-missing-bulk statement required by B1.

The focused proof package is now:

```text
docs/proofs/trace-scale-compatibility-proof-package.md
```

## Evidence Checked

| evidence file | useful for B1 | limit |
|---|---|---|
| `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md` | gives operator identity, Hilbert-Schmidt gate, trace-class square, cyclic ledger, support-square trace, and no-defect source trace order | it does not prove lambda-scale compatibility or finite-part ownership |
| `docs/proofs/cc20-trace-object-normalization-discharge.md` | names positive trace, support-square trace, no-defect trace, Mellin convention, and sign normalization source objects | it still treats ordinary-to-source conversion as a source-object normalization target, not as a same-scale theorem |
| `docs/proofs/fixed-s-no-defect-compact-form-read-off.md` | identifies the no-defect compact-form read-off with `QW_lambda(g,g)` at route-evidence level | it starts after Battle 2 has already rewritten the positive support-square trace and separated ledgers |
| `docs/proofs/sonin-prolate-defect-referee-discharge.md` | proves the Rows 3-7 no-hidden-defect chain at project proof-package level | it assumes source positive-trace read-off ownership before it classifies the transported source remainder |
| `docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md` | states the no-fourth-defect equality after the source remainder is owned | it does not cover a finite-part or divergent bulk introduced while moving from ordinary trace to source convention |
| `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` | gives eventual fixed-test scalar equality `QW_lambda(g,g)=QW(g,g)` at route-evidence level | it assumes the finite-lambda scalar entering the bridge is already the correct read-off scalar |

## Subtarget Verdicts

| TraceScaleCompatibility subtarget | current evidence | verdict |
|---|---|---|
| OrdinaryPositiveTraceScaleOwner | `README.md:237-251`; manuscript `648-659`; trace-legality contract | partially covered for definition and trace-class existence |
| SupportSquareSameScalar | manuscript `675-677`; trace-legality contract | partially covered, pending accepted source or formal theorem |
| SourceConventionConversionLedger | `docs/proofs/trace-scale-compatibility-proof-package.md` Lemma 3 | closed at project proof-package level |
| NoDefectTraceEqualsRestrictedCCMScalar | manuscript `988-1002`, `1027-1033`; `fixed-s-no-defect-compact-form-read-off.md` | route-evidence covered after the source trace object is accepted |
| NoMissingTraceScaleBulk | `docs/proofs/trace-scale-compatibility-proof-package.md` Lemma 5 | closed at project proof-package level |
| TraceScaleLimitCompatibility | `restricted-to-full-qw-bridge-proof-package.md`; `battle-3-cdef-exhaustion-proof-package.md`; `docs/proofs/trace-scale-compatibility-proof-package.md` Lemma 6 | closed at project proof-package level |

## Failure Mechanism Still Open

The remaining risk has this shape:

```text
ordinary positive trace
        |
        v
support-square trace
        |
        v
source no-defect convention
        |
        +-- named rank/pole ledgers
        |
        +-- named Cdef remainder
        |
        +-- possible finite-part or divergent bulk term
```

Rows 3-7 block a fourth defect after the source remainder has been owned. They
do not by themselves block a bulk term introduced earlier by changing from the
ordinary trace scalar to the source no-defect convention.

That distinction matters because the final limit uses:

```text
Rank = 0,
PoleJetExtra = 0,
Cdef(lambda,g) -> 0,
QW_lambda(g,g) = QW(g,g) for lambda large.
```

If an untracked bulk term remains outside those classes, the lower bound for
`QW_lambda(g,g)` does not survive the `lambda -> infinity` step.

## Required Next Proof Package

The next proof package should target only two missing claims:

```text
SourceConventionConversionLedger
NoMissingTraceScaleBulk
```

It should not re-prove trace legality, Rows 3-7, or restricted-to-full
`QW_lambda=QW`. Those packages already exist. The missing proof must say where
each ordinary-to-source convention term goes.

Acceptance criteria:

| criterion | required result |
|---|---|
| ordinary-to-source equality | a scalar equality, not a prose convention match |
| finite-part ownership | every finite-part subtraction appears in no-defect source trace, rank, pole, or `Cdef` |
| bulk accounting | no lambda-growing term remains outside the named classes |
| downstream compatibility | after ledger killing, only `Cdef` remains on the right side of the lower bound |

## Current Decision

The B1 blocker is closed at project proof-package level.

Accepted-source certification, external referee certification, and Lean theorem
status remain open. The route should now move to B2, then B3 and B4.
