# No Hidden Positive Defect Outside Cdef Proof Package

Status: route-evidence proof package for Row 7 of the sign/defect discharge
ledger.

This package proves the project-level target stated in:

```text
docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md
```

It is not a CC20, CCM24, or CCM25 source import. It is not a Lean theorem. It
does not prove restricted-to-full `QW_lambda -> QW`, full Weil positivity, or
RH.

## Result

Good result:

```text
NoHiddenPositiveDefectOutsideCdef is closed at route-evidence level.
```

Boundary:

```text
The sign/defect bridge now has a route-evidence closure.
Accepted source-import status remains open.
Lean proof status remains open.
The RH proof is not complete.
```

## Target

For an admissible source-backed tuple:

```text
(S,I,lambda,g,F_g,J),
```

prove:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
R_(S,I,lambda,J)(g),

|R_(S,I,lambda,J)(g)|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The proof must also show that no extra positive defect remains outside this
remainder.

## Evidence Boundary

| claim | evidence |
|---|---|
| source positive-trace obstruction is `D circ Q` / `E circ Q` | `docs/proofs/cc20-source-remainder-orientation-theorem-contract.md`; `docs/audits/cc20-post-q-remainder-term-map.md` |
| the source post-`Q` remainder is transported into one fixed-S object | `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md` |
| transported remainder has no-strip and endpoint-strip classes only | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md` |
| no-strip classes are rank or pole only | `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` |
| endpoint-strip class is bounded by route `Cdef` | `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` |

## Proof Skeleton

```text
source positive-trace read-off
        |
        v
QW_lambda + source post-Q remainder
        |
        v
QW_lambda + TransportedCC20PostQRemainder
        |
        v
QW_lambda + no-strip + endpoint-strip
        |
        v
QW_lambda + Rank + PoleJetExtra + R
        |
        v
|R| <= C Cdef
```

The proof is an equality proof followed by one norm bound. It does not infer
direct positivity for `QW_lambda`.

## Lemma 1. Source Read-Off Remainder Is The Row 3 Object

Statement:

```text
SourcePositiveTraceRemainderOwnership(S,I,lambda,g,F_g):
  PositiveTrace^G_(S,lambda)(g)
    =
  QW_lambda(g,g)
    +
  TransportedCC20PostQRemainder(S,I,lambda,g,F_g).
```

Proof.

The CC20 orientation contract fixes the source obstruction:

```text
W_infty = L - D,
W_infty = S - E,
```

and identifies the post-`Q` obstruction as `D circ Q` / `E circ Q`, not as a
free project-local error.

Evidence:

```text
docs/proofs/cc20-source-remainder-orientation-theorem-contract.md
docs/audits/cc20-post-q-remainder-term-map.md
```

Row 3 transports exactly that source post-`Q` remainder into the fixed-S
coordinate:

```text
TransportedCC20PostQRemainder(S,I,lambda,g,F_g).
```

Evidence:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md
```

Therefore the positive-trace read-off remainder is not a new object. It is the
Row 3 transported source remainder.

Output:

```text
source_remainder_same_as_Row3_object
same_test_g
same_square_F_g
same_tuple_S_I_lambda
same_fixedS_coordinate
```

## Lemma 2. Transported Remainder Has Only No-Strip And Endpoint-Strip Parts

Statement:

```text
TransportedRemainderTwoClassSplit(S,I,lambda,g,F_g,J):
  TransportedCC20PostQRemainder
    =
  NoStripSourceRemainder_(S,I,g)
    +
  EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J),
```

with no fourth Row 4 class.

Proof.

Row 4 proves that the transported source remainder splits into no-strip
channels and endpoint-strip projection-defect normal forms:

```text
FixedSProjectionDefectNormalFormForSourceRemainder.
```

The Row 4 output also records:

```text
no_fourth_Row4_class.
```

Evidence:

```text
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
```

This removes the first possible hiding place for a positive defect. A term that
is neither no-strip nor endpoint-strip would contradict the Row 4 exhaustive
split.

## Lemma 3. No-Strip Part Is Exactly Rank Plus Pole

Statement:

```text
NoStripRemainderRankPoleEquality(S,I,g):
  NoStripSourceRemainder_(S,I,g)
    =
  Rank_(S,I)(g)
    +
  PoleJetExtra_(S,I)(g).
```

Proof.

Row 5 identifies every no-strip channel as either the rank ledger or the
extra pole ledger:

```text
SourceRankPoleLedgerIdentification.
```

It also records that no extra no-strip channel remains after this
identification.

Evidence:

```text
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
```

This removes the second hiding place for a positive defect. A no-strip term
outside `Rank` and `PoleJetExtra` would contradict Row 5.

## Lemma 4. Endpoint-Strip Part Is The Cdef-Bounded Remainder

Statement:

```text
EndpointStripRemainderIsCdefBounded(S,I,lambda,g,F_g,J):
  let R_(S,I,lambda,J)(g)
    =
  EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J);

  |R_(S,I,lambda,J)(g)|
    <=
  C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Proof.

Row 6 matches each endpoint-strip source-remainder term to the exact finite
endpoint-strip index set used in route `Cdef`:

```text
R_(S,I,lambda,J)
Q R_(S,I,lambda,J).
```

It proves the trace-norm and boundary-strip domination and then sums over the
fixed index family.

Evidence:

```text
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
```

This removes the third hiding place for a positive defect. An endpoint-strip
term not bounded by `Cdef` would contradict Row 6.

## Theorem. No Hidden Positive Defect Outside Cdef

Statement:

```text
NoHiddenPositiveDefectOutsideCdef(S,I,lambda,g,F_g,J):
  PositiveTrace^G_(S,lambda)(g)
    =
  QW_lambda(g,g)
    +
  Rank_(S,I)(g)
    +
  PoleJetExtra_(S,I)(g)
    +
  R_(S,I,lambda,J)(g),

  |R_(S,I,lambda,J)(g)|
    <=
  C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g),
```

with no additional term outside `R`.

Proof.

Start from Lemma 1:

```text
PositiveTrace
  =
QW_lambda
  +
TransportedCC20PostQRemainder.
```

Use Lemma 2:

```text
TransportedCC20PostQRemainder
  =
NoStripSourceRemainder
  +
EndpointStripSourceRemainder.
```

Use Lemma 3:

```text
NoStripSourceRemainder
  =
Rank
  +
PoleJetExtra.
```

Define:

```text
R_(S,I,lambda,J)(g)
  :=
EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J).
```

Then:

```text
PositiveTrace
  =
QW_lambda
  +
Rank
  +
PoleJetExtra
  +
R.
```

Use Lemma 4 to get:

```text
|R|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

No hidden positive defect can remain, because Lemma 1 owns the whole source
remainder, Lemma 2 exhausts that remainder into two classes, Lemma 3 exhausts
the no-strip class, and Lemma 4 defines the endpoint-strip class as `R`.

## Corollary. Restricted Lower Bound After Ledger Killing

Statement:

```text
PositiveTraceToRestrictedLowerBound(S,I,lambda,g,F_g,J):
  if
    Rank_(S,I)(g) = 0
    and
    PoleJetExtra_(S,I)(g) = 0,
  then

    QW_lambda(g,g)
      >=
    - C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Proof.

From the theorem:

```text
PositiveTrace
  =
QW_lambda
  +
R
```

after the ledgers vanish. Since:

```text
PositiveTrace >= 0
```

we get:

```text
QW_lambda >= -R.
```

Using:

```text
|R| <= C Cdef
```

gives:

```text
QW_lambda >= -C Cdef.
```

This is the strongest sign statement available at finite `lambda`. Direct
finite-`lambda` positivity of `QW_lambda` is not claimed.

## Output To The Discharge Ledger

This package supplies, at route-evidence level:

```text
NoHiddenPositiveDefectOutsideCdef
PositiveTraceToRestrictedLowerBound
SoninProlateDefectEqualsEndpointStripCdef_route_evidence
```

It does not supply:

```text
accepted_source_import_discharge
Lean_theorem
RestrictedToFullQWExhaustion
FullWeilPositivity
RiemannHypothesis
```

## Current Status

```text
Source remainder ownership:             route-evidence composition
Exhaustive remainder partition:         proved at route-evidence level
Rank/pole no-strip closure:             proved at route-evidence level
Endpoint-strip Cdef bound:              proved at route-evidence level
No hidden positive defect equality:      proved at route-evidence level
Restricted finite-lambda lower bound:    proved at route-evidence level

Accepted source-import status:          open
Lean proof status:                      open
Restricted-to-full QW bridge:           open
Full RH proof:                          not complete
```
