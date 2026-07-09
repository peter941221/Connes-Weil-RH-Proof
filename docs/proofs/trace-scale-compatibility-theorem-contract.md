# Trace Scale Compatibility Theorem Contract

Status: theorem contract for the B1 trace-scale compatibility blocker.

This contract strengthens:

```text
docs/audits/trace-scale-compatibility-audit.md
```

from an open audit into precise theorem targets. It does not prove the targets.
It states what a proof, accepted source import, or future Lean theorem must
show before the route can use positive trace to obtain a lower bound for
`QW_lambda(g,g)`.

## Evidence Lock

| item | evidence |
|---|---|
| public positive trace definition | `README.md:237-251` |
| public read-off equality | `README.md:282-297` |
| public fixed-test limit | `README.md:369-382` |
| Hilbert-Schmidt and trace-class gate | `docs/manuscripts/connes-weil-rh-proof-draft.md:648-659` |
| positive trace to support-square trace | `docs/manuscripts/connes-weil-rh-proof-draft.md:675-677` |
| support-square split | `docs/manuscripts/connes-weil-rh-proof-draft.md:680-710` |
| ordinary versus source regularized trace ledger | `docs/manuscripts/connes-weil-rh-proof-draft.md:720-724` |
| CCM25 restricted `QW_lambda` display | `docs/manuscripts/connes-weil-rh-proof-draft.md:988-1002` |
| no-defect trace equals `QW_lambda` assertion | `docs/manuscripts/connes-weil-rh-proof-draft.md:1027-1033` |
| trace legality theorem contract | `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md:351-372` |
| Row 7 no-hidden-defect contract | `docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md` |

The line references show the route already names the required objects. The
missing part is a theorem tying their finite-lambda scalar normalizations and
lambda-scale behavior together.

## Boundary

This contract sits between two existing gates:

```text
CC20 trace legality
        |
        v
TraceScaleCompatibility
        |
        v
NoHiddenPositiveDefectOutsideCdef
```

Trace legality proves that the ordinary trace and cyclic moves make sense.
Trace-scale compatibility must prove that the ordinary trace and the source
read-off have the same scalar normalization and the same lambda-scale.

Row 7 proves that no extra defect survives after the source remainder has been
identified. Row 7 cannot absorb a divergent bulk term unless that term appears
as one of its named inputs.

## Objects Fixed Before The Contract

For fixed route data:

```text
S       finite source place set
I       source support window
lambda  restricted CCM25 parameter
g       common source test
F_g     source convolution square g^* * g
J       endpoint-strip graph order
```

the contract uses these scalars:

```text
OrdinaryPositiveTrace(S,I,lambda,g)

SupportSquareTrace(S,I,lambda,g)

NoDefectSourceTrace(S,I,lambda,g)

RestrictedCCMScalar(S,I,lambda,g) = QW_lambda(g,g)

Rank_(S,I)(g)

PoleJetExtra_(S,I)(g)

CdefRemainder_(S,I,lambda,J)(g)
```

The theorem must use one route tuple. It cannot let the ordinary trace use one
cutoff, the source trace use another cutoff, and the CCM25 restricted form use
a third cutoff.

## Contract Theorem 1. Ordinary Trace Scale Ownership

Target:

```text
OrdinaryPositiveTraceScaleOwner(S,I,lambda,g):
  OrdinaryPositiveTrace(S,I,lambda,g)
    =
  Tr(A_(S,I,lambda,g)^* A_(S,I,lambda,g))

and the same lambda controls every projection in A_(S,I,lambda,g).
```

Required input:

```text
CC20AnalyticTraceLegalityContract(S,I,lambda,g)
```

Meaning:

The positive trace must remain an ordinary trace scalar after the cyclic
rewrite. If later steps use a finite-part or regularized scalar, the theorem
must name the conversion.

Reject:

```text
PositiveTrace(S,I,lambda,g)
```

as an abstract scalar with no trace identity and no cutoff ownership.

## Contract Theorem 2. Support-Square Same-Scalar Equality

Target:

```text
SupportSquareSameScalar(S,I,lambda,g):
  OrdinaryPositiveTrace(S,I,lambda,g)
    =
  SupportSquareTrace(S,I,lambda,g).
```

Required evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:675-677
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md:351-372
```

Meaning:

The support-square trace must be the same scalar as the ordinary positive
trace. A proof must not replace equality of scalars by a formal similarity of
operator expressions.

## Contract Theorem 3. Source Convention Conversion Ledger

Target:

```text
SourceConventionConversionLedger(S,I,lambda,g):
  SupportSquareTrace(S,I,lambda,g)
    =
  NoDefectSourceTrace(S,I,lambda,g)
    +
  SourceConventionLedger_(S,I,lambda,g).
```

The ledger must split as:

```text
SourceConventionLedger_(S,I,lambda,g)
  =
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
ProjectionDefectRemainder_(S,I,lambda,g).
```

Meaning:

The Connes--Consani regularized source convention can enter only through the
named no-defect source trace or through named ledgers. If the source convention
subtracts a divergent ordinary-trace bulk, that subtraction must appear in this
ledger before the route sends `lambda` to infinity.

Reject:

```text
same source convention
```

as a prose justification with no scalar equality.

## Contract Theorem 4. No-Defect To Restricted CCM Scalar

Target:

```text
NoDefectTraceEqualsRestrictedCCMScalar(S,I,lambda,g):
  NoDefectSourceTrace(S,I,lambda,g)
    =
  QW_lambda(g,g).
```

Required evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:988-1002
docs/manuscripts/connes-weil-rh-proof-draft.md:1027-1033
```

Meaning:

The CCM25 restricted scalar must use the same test `g`, square `F_g`, interval
`[lambda^(-1),lambda]`, pole convention, and finite-prime cutoff as the
no-defect source trace.

Reject:

```text
QW_lambda is the right Weil form.
```

without the equality above.

## Contract Theorem 5. No Missing Bulk Term

Target:

```text
NoMissingTraceScaleBulk(S,I,lambda,g,J):
  ProjectionDefectRemainder_(S,I,lambda,g)
    =
  CdefRemainder_(S,I,lambda,J)(g)

and no scalar term

  BulkScaleTerm_(S,I,lambda,g)

appears outside:

  Rank_(S,I)(g),
  PoleJetExtra_(S,I)(g),
  CdefRemainder_(S,I,lambda,J)(g).
```

Meaning:

The theorem must rule out the external-review failure mode:

```text
OrdinaryPositiveTrace
  =
QW_lambda + killed ledgers + small Cdef + divergent bulk.
```

It may rule this out in one of three ways:

| route | required proof |
|---|---|
| bounded ordinary trace | prove `OrdinaryPositiveTrace` has the same fixed-test scale as `QW_lambda + ledgers + Cdef` |
| exact named cancellation | identify the large term and prove it cancels inside the named ledgers or no-defect source convention |
| accepted source finite-part identity | import a source theorem that states the ordinary positive trace read-off equals the displayed CCM scalar plus exactly the named ledgers and `Cdef` |

## Contract Theorem 6. Lambda-Limit Compatibility

Target:

```text
TraceScaleLimitCompatibility(S,I,g,J):
  for lambda large enough,
    QW_lambda(g,g) = QW(g,g),

  and

    CdefRemainder_(S,I,lambda,J)(g) -> 0,

  while every term outside QW_lambda is either killed by triple vanishing or
  included in CdefRemainder_(S,I,lambda,J)(g).
```

Meaning:

The limit step can use:

```text
QW_lambda(g,g)
  >=
- C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g)
```

only after the read-off equality has no untracked lambda-growth term.

## Combined Contract

Target:

```text
TraceScaleCompatibilityContract(S,I,lambda,g,F_g,J):
  OrdinaryPositiveTraceScaleOwner
  + SupportSquareSameScalar
  + SourceConventionConversionLedger
  + NoDefectTraceEqualsRestrictedCCMScalar
  + NoMissingTraceScaleBulk
  + TraceScaleLimitCompatibility.
```

Projection target:

```text
TraceScaleCompatibilityContract(S,I,lambda,g,F_g,J)
  ->
PositiveTrace^G_(S,lambda)(g)
    =
QW_lambda(g,g)
  + Rank_(S,I)(g)
  + PoleJetExtra_(S,I)(g)
  + R_(S,I,lambda,J)(g)
```

with:

```text
R_(S,I,lambda,J)(g)
  =
CdefRemainder_(S,I,lambda,J)(g),

|R_(S,I,lambda,J)(g)|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

## Relation To Existing Contracts

| existing contract | contribution | remaining B1 work |
|---|---|---|
| `CC20AnalyticTraceLegalityContract` | gives operator identity, trace-class square, cyclic ledger, support-square order | does not prove lambda-scale compatibility or finite-part ownership |
| `NoHiddenPositiveDefectOutsideCdefContract` | states no fourth defect after the source remainder is owned | needs B1 to prove the source remainder has not hidden a bulk scale term before Row 7 |
| `RestrictedToFullQWBridgeContract` | gives eventual fixed-test equality `QW_lambda=QW` | assumes the restricted scalar entering the limit is already the correct read-off scalar |

## Import Acceptance Checklist

| item | required evidence |
|---|---|
| same scalar | ordinary positive trace equals support-square trace as a scalar |
| same cutoff | all trace and CCM objects use the same `lambda` window |
| source convention ledger | every ordinary-to-regularized conversion has a named scalar ledger |
| restricted CCM equality | no-defect source trace equals `QW_lambda(g,g)` with the same test and cutoff |
| no bulk leakage | no divergent or finite-part bulk remains outside rank, pole, or `Cdef` |
| limit compatibility | ledger killing plus `Cdef -> 0` gives the displayed lower bound for the same scalar that becomes `QW(g,g)` |

## Current Judgment

| question | answer |
|---|---|
| Does this contract prove trace-scale compatibility? | no |
| Does it state the theorem shape needed to attack B1? | yes |
| Does it close the external divergence objection? | no |
| What would it close if proved? | B1 trace-scale compatibility |

The next step is to attempt a proof package for this contract. If that proof
cannot name the ordinary-to-source convention conversion and the no-missing-bulk
theorem, the route should keep B1 open.
