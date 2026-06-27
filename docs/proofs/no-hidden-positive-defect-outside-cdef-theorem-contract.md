# No Hidden Positive Defect Outside Cdef Theorem Contract

Status: project-proof theorem contract for Row 7 of the sign/defect discharge
ledger.

This contract sits after:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
```

It states the last equality needed to answer the hostile sign/defect
objection:

```text
Tr(A^* A) >= 0
  does not imply
QW_lambda(g,g) >= 0
```

unless the positive trace is first read as the restricted Weil form plus only
the killed ledgers and a `Cdef`-controlled remainder.

## Boundary

This contract proves only the Row 7 project theorem target:

```text
NoHiddenPositiveDefectOutsideCdef(S,I,lambda,g,F_g,J).
```

It does not prove:

```text
accepted source-import legitimacy,
Lean formalization,
restricted-to-full QW exhaustion,
full Weil positivity,
or RH.
```

## Required Inputs

| input | current evidence |
|---|---|
| source positive-trace orientation | `docs/proofs/cc20-source-remainder-orientation-theorem-contract.md` |
| source post-`Q` term map | `docs/audits/cc20-post-q-remainder-term-map.md` |
| transported source remainder | `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md` |
| no-strip / endpoint-strip split | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md` |
| no-strip rank/pole identification | `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` |
| endpoint-strip `Cdef` domination | `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` |

The first two rows are source-orientation inputs. They are not accepted source
imports in this repository. Row 7 must keep that boundary visible.

## Contract Theorem 1. Source Read-Off Remainder Ownership

Target:

```text
SourcePositiveTraceRemainderOwnership(S,I,lambda,g,F_g):
  PositiveTrace^G_(S,lambda)(g)
    =
  QW_lambda(g,g)
    +
  TransportedCC20PostQRemainder(S,I,lambda,g,F_g).
```

Meaning:

The source read-off remainder must be the same object that Row 3 transported.
A proof cannot replace it by a route-local placeholder.

Reject:

```text
the source remainder is harmless.
```

The statement must be an equality with the same test, same support window, and
same fixed-S coordinate.

## Contract Theorem 2. Exhaustive Remainder Partition

Target:

```text
TransportedSourceRemainderPartition(S,I,lambda,g,F_g,J):
  TransportedCC20PostQRemainder(S,I,lambda,g,F_g)
    =
  Rank_(S,I)(g)
    +
  PoleJetExtra_(S,I)(g)
    +
  EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J).
```

Required projections:

```text
Row4_no_strip_endpoint_strip_split
Row4_no_fourth_class
Row5_no_strip_equals_rank_plus_pole
Row5_no_extra_no_strip_channel
Row6_endpoint_strip_object_unchanged_before_bounding
```

## Contract Theorem 3. Endpoint-Strip Remainder Bound

Target:

```text
EndpointStripRemainderBoundForRow7(S,I,lambda,g,F_g,J):
  |EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J)|
    <=
  C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

This theorem uses Row 6. It must not introduce a second defect norm.

## Contract Theorem 4. No Hidden Positive Defect Equality

Target:

```text
NoHiddenPositiveDefectOutsideCdef(S,I,lambda,g,F_g,J):
  exists R_(S,I,lambda,J)(g) such that

    PositiveTrace^G_(S,lambda)(g)
      =
    QW_lambda(g,g)
      +
    Rank_(S,I)(g)
      +
    PoleJetExtra_(S,I)(g)
      +
    R_(S,I,lambda,J)(g),

    R_(S,I,lambda,J)(g)
      =
    EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J),

    |R_(S,I,lambda,J)(g)|
      <=
    C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Meaning:

There is no additional term:

```text
HiddenDefect_(S,I,lambda,g)
```

with a separate sign or a separate limit. If such a term appears in the source
read-off, this contract fails.

## Contract Theorem 5. Sign Consequence After Ledger Killing

Target:

```text
PositiveTraceToRestrictedLowerBound(S,I,lambda,g,F_g,J):
  if
    hat g(0) = 0,
    hat g(+i/2) = 0,
    hat g(-i/2) = 0,
  then

    QW_lambda(g,g)
      >=
    - C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

This is the only sign conclusion Row 7 allows before the `lambda -> infinity`
step.

## Combined Contract

Target:

```text
NoHiddenPositiveDefectOutsideCdefContract(S,I,lambda,g,F_g,J):
  SourcePositiveTraceRemainderOwnership
  + TransportedSourceRemainderPartition
  + EndpointStripRemainderBoundForRow7
  + NoHiddenPositiveDefectOutsideCdef
  + PositiveTraceToRestrictedLowerBound.
```

Projection target:

```text
NoHiddenPositiveDefectOutsideCdefContract
  ->
SoninProlateDefectEqualsEndpointStripCdef
```

at route-evidence level only.

## Proof Acceptance Checklist

| requirement | required evidence |
|---|---|
| source remainder ownership | source read-off remainder equals Row 3 transported object |
| exact equality | positive trace is expressed by equality, not inequality |
| exhaustive split | Row 4 supplies no fourth class |
| no-strip closure | Row 5 supplies only rank and pole no-strip ledgers |
| endpoint-strip closure | Row 6 supplies the exact `Cdef`-bounded endpoint-strip remainder |
| sign discipline | positive trace gives `QW_lambda >= -Cdef`, not direct positivity |
| no overclaim | source-import, Lean, restricted-to-full, and RH remain separate |

## Current Judgment

| question | answer |
|---|---|
| Does this contract state the hostile-objection closure point? | yes |
| Does it make the source read-off equality visible? | yes |
| Does it discharge accepted-source or Lean proof status by itself? | no |
| What would it close if proved? | Row 7 at route-evidence level |
