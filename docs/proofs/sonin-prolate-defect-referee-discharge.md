# Sonin Prolate Defect Referee Discharge

Status: mathematics-only referee discharge package for the sign/defect bridge.

This file upgrades the Row 3 through Row 7 route-evidence packages into one
referee-facing proof package. It does not claim Lean verification, accepted
source import status, journal acceptance, Clay acceptance, or an unconditional
public proof of RH.

The target is narrower:

```text
for one fixed source-backed tuple (S,I,lambda,g,F_g,J),
the positive-trace defect equals killed rank/pole ledgers plus an
endpoint-strip Cdef remainder.
```

The package treats the CC20 and CCM24 source formulas as cited inputs and
checks the project proof layer that connects them to the route objects.

## Verdict

Good result:

```text
Rows 3 through 7 now form a single referee-readable sign/defect proof chain.
```

Remaining boundary:

```text
Rows 1 and 2 now have a project proof package in
docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md.
Row 3 still depends on project proof of fixed-S transport, not on a direct
source import.
External certification remains open.
```

So the mathematical status is:

```text
sign/defect bridge: closed as a project proof package;
accepted-source certification: not yet closed.
```

## Fixed Objects

Fix one admissible tuple:

```text
S                 finite place set
I                 fixed CCM24 support window
lambda            restricted-window parameter, 1 < lambda
g                 common source test
F_g = g^* * g     common convolution square
J                 fixed graph/order budget for endpoint-strip Cdef
```

Every theorem below uses these objects. The proof rejects any step that changes
the test, window, fixed-S coordinate, or source square.

The proof uses this common coordinate:

```text
V_S = M_S U_S.
```

That coordinate is the only place where projection commutators, endpoint-strip
normal forms, and transported CC20 post-Q remainders may meet.

## Theorem

For the fixed tuple above:

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

After the rank and pole ledgers vanish:

```text
QW_lambda(g,g)
  >=
- C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The theorem does not assert finite-lambda positivity of `QW_lambda(g,g)`.

## Dependency Chain

```text
CC20 source post-Q remainder
        |
        v
Row 3: fixed-S transport into V_S
        |
        v
Row 4: no-strip / endpoint-strip split
        |
        +-----------------------------+
        |                             |
        v                             v
Row 5: rank + pole no-strip      Row 6: endpoint-strip Cdef
        |                             |
        +-------------+---------------+
                      |
                      v
Row 7: no hidden positive defect
                      |
                      v
QW_lambda(g,g) >= - C Cdef
```

The proof has one job: show that this graph has no branch where a positive
defect can hide.

## Lemma 1. Row 3 Owns The Whole Source Post-Q Remainder

Statement:

```text
CC20PostQRemainderFixedSSoninTransport(S,I,lambda,g,F_g):
  the CC20 post-Q source remainder is transported into
  TransportedCC20PostQRemainder(S,I,lambda,g,F_g)
  in the common fixed-S coordinate V_S.
```

Proof.

The CC20 term map splits the post-Q source remainder into four visible
classes:

```text
bulk integral term,
moving lower-boundary term,
fixed upper-boundary term,
series tail.
```

The Row 3 package assigns a separate bridge to these classes:

| source class | bridge |
|---|---|
| bulk integral term | `FixedSPostQBulkGraphTransfer` |
| lower and upper boundary terms | `FixedSPostQBoundaryFunctionalTransfer` |
| infinite series tail | `FixedSPostQSeriesTailBoundedComparison` |

The bulk bridge proves source-to-log graph translation, fixed finite-S Euler
graph boundedness, a common `V_S` representative, and source-bulk equality.

The boundary bridge keeps the endpoint functionals source-owned and transports
them through the same finite-S trace coordinate before Row 5 or Row 6 classifies
them.

The tail bridge uses a fixed-S tail graph norm and the CC20 summable majorants
to pass from transported finite partial sums to the full transported source
remainder.

The combined object is:

```text
TransportedCC20PostQRemainder(S,I,lambda,g,F_g).
```

This object contains all post-Q source classes listed above. The proof does
not use triple vanishing, rank/pole identification, endpoint-strip Cdef
domination, CCM25 spectral convergence, determinant convergence, or a
lambda-limit.

Evidence:

```text
docs/audits/cc20-post-q-remainder-term-map.md
docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md
docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md
docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md
docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md
docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md
```

## Lemma 2. Row 4 Gives An Exhaustive Two-Class Split

Statement:

```text
TransportedCC20PostQRemainder(S,I,lambda,g,F_g)
  =
NoStripSourceRemainder_(S,I,g)
  +
EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J).
```

No third source-remainder class appears after Row 4.

Proof.

Row 4 applies the fixed-S projection calculus only after Row 3 has moved the
source remainder into `V_S`. It then expands projection-order defects through
the listed commutators:

```text
[P,M_S], [P_hat,M_S], [P,M_S^*], [P_hat,M_S^*].
```

Each non-no-strip commutator contributes an endpoint-strip shifted-kernel
normal form. The remaining terms have no endpoint-strip factor and form the
no-strip source remainder.

The split is exhaustive because Row 4 classifies each transported source
summand by whether it contains one of the listed projection commutators. A term
outside both classes would be a transported source summand with neither
no-strip status nor a projection commutator, contradicting the Row 4 expansion.

Evidence:

```text
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
```

## Lemma 3. Row 5 Identifies Every No-Strip Channel

Statement:

```text
NoStripSourceRemainder_(S,I,g)
  =
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g).
```

Proof.

Row 5 starts from the no-strip class produced by Row 4. It proves that the
class has only two source channels:

```text
rank channel,
pole-jet channel.
```

The rank channel is the zero-mode ledger killed by the route rank condition.

The pole-jet channel is the extra pole ledger outside the CCM25 pole term
already present inside `QW_lambda`. The proof keeps these two pole roles
separate, so the route cannot erase a CCM25 pole contribution by calling it a
ledger defect.

Triple vanishing enters only after Row 5 identifies these channels. The proof
does not use triple vanishing to classify an unidentified remainder.

Evidence:

```text
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
docs/proofs/final-sign-bridge-proof-package.md
```

## Lemma 4. Row 6 Turns The Endpoint-Strip Class Into Cdef

Statement:

```text
R_(S,I,lambda,J)(g)
  :=
EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J)
```

and:

```text
|R_(S,I,lambda,J)(g)|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Proof.

Row 6 matches each endpoint-strip normal-form term from Row 4 to a summand in
the route `Cdef` family. The matching preserves source ownership: the endpoint
terms still come from `TransportedCC20PostQRemainder`, not from a route-local
placeholder.

For boundary evaluations, Row 6 uses the Row 4 strip factor before applying the
evaluation functional. For post-Q terms, it uses the Row 3 source ownership so
that the `Q` image does not create an untracked bulk term.

The proof sums the fixed finite endpoint-strip family and obtains the displayed
trace-norm domination. The fixed-test exhaustion belongs to the later
lambda-limit step. The present lemma only supplies the finite-lambda bound.

Evidence:

```text
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
docs/proofs/battle-3-cdef-exhaustion-proof-package.md
docs/proofs/fixed-test-graph-cdef-exhaustion.md
```

## Lemma 5. Row 7 Removes The Fourth-Defect Escape

Statement:

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
```

with the Row 6 bound on `R`.

Proof.

Start with the source positive-trace read-off:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
TransportedCC20PostQRemainder(S,I,lambda,g,F_g).
```

Lemma 1 identifies the remainder as the full transported CC20 post-Q source
object. Lemma 2 splits that object into no-strip and endpoint-strip classes.
Lemma 3 identifies the no-strip class as `Rank + PoleJetExtra`. Lemma 4 defines
the endpoint-strip class as `R` and bounds it by `C Cdef`.

A fourth positive defect would have to enter in one of four places:

| possible hiding place | blocked by |
|---|---|
| outside the transported source remainder | Lemma 1 owns the full CC20 post-Q remainder |
| inside the Row 4 split | Lemma 2 exhausts no-strip and endpoint-strip classes |
| inside the no-strip class | Lemma 3 identifies rank and pole only |
| inside the endpoint-strip class | Lemma 4 defines it as the Cdef-bounded `R` |

Therefore no additional term remains outside:

```text
Rank_(S,I)(g), PoleJetExtra_(S,I)(g), R_(S,I,lambda,J)(g).
```

Evidence:

```text
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md
```

## Corollary. Finite-Lambda Lower Bound

Assume:

```text
Rank_(S,I)(g) = 0,
PoleJetExtra_(S,I)(g) = 0,
PositiveTrace^G_(S,lambda)(g) >= 0.
```

Then:

```text
QW_lambda(g,g)
  >=
- C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Proof.

Under the ledger vanishings, Lemma 5 gives:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
R_(S,I,lambda,J)(g).
```

Since the positive trace is nonnegative:

```text
QW_lambda(g,g) >= -R_(S,I,lambda,J)(g).
```

The Row 6 bound gives:

```text
-R_(S,I,lambda,J)(g)
  >=
-|R_(S,I,lambda,J)(g)|
  >=
-C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Combining these inequalities proves the claim.

## Referee Acceptance Tests

This package should satisfy the following tests before anyone treats the
sign/defect bridge as a mathematical proof package rather than a route note.

| test | required answer |
|---|---|
| Does one tuple `(S,I,lambda,g,F_g,J)` govern all rows? | yes |
| Does Row 3 consume the CC20 post-Q source remainder before Row 4 classifies it? | yes |
| Does Row 3 split derivative/domain, boundary evaluation, and series tail? | yes |
| Does Row 4 classify only the Row 3 transported source object? | yes |
| Does Row 5 identify no-strip terms before triple vanishing kills them? | yes |
| Does Row 6 match endpoint-strip terms to displayed `Cdef` summands? | yes |
| Does Row 7 prove equality before taking a sign consequence? | yes |
| Does the finite-lambda conclusion avoid claiming `QW_lambda(g,g) >= 0`? | yes |
| Does the argument avoid spectral or determinant convergence? | yes |

## Remaining Certification Work

This package reduces the sign/defect objection to two source-facing tasks:

```text
1. Source-orientation discharge:
   CC20 must supply the exact prolate/Sonin remainder object and post-Q image
   with the sign convention used here.

2. Source/import acceptance:
   a referee, external theorem, or later formal proof must accept the fixed-S
   transport and endpoint-strip Cdef classification as mathematics, not only
   as project route evidence.
```

After those tasks, the next mathematical gates are:

```text
restricted-to-full QW_lambda(g,g) = QW(g,g),
final sign bridge QW(g,g) = -sum_v W_v(F_g),
CC20 Proposition C.1 finite-vanishing exit,
source RH to standard RH definition.
```

## Current Status

```text
Rows 3-7 proof chain:                   referee-readable package written
No-hidden-defect equality:              closed at project proof-package level
Finite-lambda lower bound:              closed at project proof-package level
Rows 1-2 source orientation:            project proof package written
Accepted-source certification:          open
Lean proof status:                      not part of this pass
RH proof status:                        source-conditional
```
