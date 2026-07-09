# Semilocal Fourth-Defect Ledger

Date: 2026-06-28

Status:

```text
B3 semilocal fourth-defect risk: closed at project proof-package level
accepted-source certification: open
Lean status: not started
```

## Question

The first external opinion raised this B3 risk:

```text
semilocal place coupling may create cross-terms outside
rank, pole, and endpoint-strip Cdef.
```

This ledger asks whether the current route has a place where such a fourth
positive defect can survive.

## Verdict

At project proof-package level, the answer is no.

The route has an explicit Rows 1-7 chain:

```text
Rows 1-2: CC20 source obstruction and post-Q image
Row 3:   fixed-S transport of the source post-Q object
Row 4:   no-strip / endpoint-strip projection split
Row 5:   no-strip rank and pole identification
Row 6:   endpoint-strip Cdef domination
Row 7:   no hidden positive defect equality
```

The chain still needs accepted-source or Lean certification. A source referee
can reject any row. But inside the current route evidence, a semilocal
cross-term has no unclassified slot left.

## Cross-Term Entry Map

| possible hiding place | if a semilocal cross-term appears here | route evidence | verdict |
|---|---|---|---|
| CC20 source formula before `Q` | it must be part of `D=L-W_infty` or `E=S-W_infty` | `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md` | source-owned, not hidden |
| CC20 post-`Q` source image | it must be bulk, moving boundary, fixed boundary, or series tail | `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md` | itemized before fixed-S transport |
| fixed-S transport | it must pass through bulk graph transfer, boundary functional transfer, or series-tail bounded comparison | `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md` | transported as Row 3 source object |
| projection/model mismatch | it must contain one of `[P,M_S]`, `[P_hat,M_S]`, `[P,M_S^*]`, `[P_hat,M_S^*]` or be no-strip | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md` | split by Row 4 |
| no-strip class | it must be rank or pole | `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` | killed by triple vanishing after identification |
| endpoint-strip class | it must be indexed by route `Cdef` and satisfy the trace-norm bound | `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | bounded and exhausted |
| after Row 7 equality | it would be an extra term outside `R` | `docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md` | excluded at route-evidence level |

## Entry 1. Source Formula Ownership

Rows 1-2 prevent the route from inventing or dropping source terms. They fix:

```text
W_infty = L - D,
W_infty = S - E.
```

They also fix the post-`Q` obstruction as:

```text
bulk integral term,
moving lower-boundary term,
fixed upper-boundary term,
series tail.
```

Evidence:

```text
docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md
docs/audits/cc20-post-q-remainder-term-map.md
```

If a semilocal coupling term is already present in the source formula, it must
appear in one of these source-owned classes before the route applies fixed-S
transport.

## Entry 2. Fixed-S Transport

Row 3 transports the CC20 post-`Q` source object. It does not classify it.

The transported object is:

```text
TransportedCC20PostQRemainder(S,I,lambda,g,F_g).
```

Evidence:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md
```

The proof splits the source object into:

```text
bulk derivative/domain transport,
boundary endpoint-functional transport,
series-tail bounded comparison.
```

A semilocal cross-term created during fixed-S transport must enter one of
those three Row 3 subcontracts. If it does not, Row 3 fails and the route must
name a new defect class. The current Row 3 package states that no such class
appears at route-evidence level.

## Entry 3. Projection Defect Normal Form

Row 4 works only after Row 3 has produced the transported source object.

It splits every transported term into:

```text
no-strip channel
endpoint-strip projection-defect channel
```

with no fourth Row 4 class.

Evidence:

```text
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
```

The semilocal mechanism is explicit: model-change terms must contain one of:

```text
[P,M_S],
[P_hat,M_S],
[P,M_S^*],
[P_hat,M_S^*].
```

For fixed finite `S`, each commutator expands into endpoint-strip shifted-kernel
normal form. A cross-term without such a commutator is no-strip and goes to
Row 5.

## Entry 4. No-Strip Closure

Row 5 proves that no-strip channels are only:

```text
Rank_(S,I)(g),
PoleJetExtra_(S,I)(g).
```

Evidence:

```text
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
```

This row also separates the route `PoleJetExtra` ledger from the CCM25 pole
term already inside `QW_lambda`. Triple vanishing kills rank and pole only
after this identification.

Any semilocal no-strip cross-term outside these ledgers would contradict Row 5
and reopen B3.

## Entry 5. Endpoint-Strip Closure

Row 6 matches every endpoint-strip source-remainder term to the route `Cdef`
family:

```text
R_(S,I,lambda,J),
Q R_(S,I,lambda,J).
```

Evidence:

```text
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
docs/proofs/battle-3-cdef-exhaustion-proof-package.md
```

The bound is:

```text
|EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J)|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Thus an endpoint-strip semilocal cross-term is not hidden. It is part of
`Cdef`.

## Entry 6. Row 7 Equality

Row 7 composes Rows 3-6 into the read-off equality:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
R_(S,I,lambda,J)(g).
```

with:

```text
R_(S,I,lambda,J)(g)
  =
EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J).
```

Evidence:

```text
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md
docs/proofs/sonin-prolate-defect-referee-discharge.md
```

A fourth positive defect after Row 7 would have to be a fifth summand in this
equality. Row 7 excludes that at project proof-package level.

## What Would Reopen B3

B3 reopens if a reviewer supplies a source term that satisfies all three
conditions:

```text
1. it is produced by the CC20/CCM24 fixed-S route object;
2. it is not part of the Rows 1-2 source post-Q itemization;
3. it is not no-strip rank/pole and not endpoint-strip Cdef.
```

Such a term would become:

```text
SemilocalFourthDefect_(S,I,lambda,g).
```

The current route has no theorem for that object. The proof would stop at the
positive-trace read-off.

## Current Judgment

| question | answer |
|---|---|
| Does the route have a semilocal fourth-defect ledger? | yes |
| Does the ledger close B3 at project proof-package level? | yes |
| Does it close B3 at accepted-source or Lean level? | no |
| What evidence would refute it? | a source-owned cross-term outside Rows 1-7 classes |

B3 is closed at project proof-package level. The next external-opinion target
is B4: whether dynamic `S(g)` breaks the global `forall g` target.
