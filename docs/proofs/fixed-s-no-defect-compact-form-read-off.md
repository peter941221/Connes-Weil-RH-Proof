# Fixed-S No-Defect Compact-Form Read-Off

Status: proof package for the source-normalized no-defect read-off left by
the rank-repair package.

This file proves:

```text
FixedSNoDefectCompactFormReadOff(S,I)
```

at source-interface level. It does not prove the support-square transport
again, and it does not prove endpoint-strip exhaustion. Those are handled in:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md
docs/proofs/battle-3-cdef-exhaustion-proof-package.md
```

## Target

After Battle 2 has rewritten the positive support-square trace as:

```text
Tr(theta_S(g)^*
   [-P_(S,G)(1/2)u_S^(-1)d^-u_S P_(S,G)]
   theta_S(g))

+ Rank_(S,I)(g)
+ PoleJetExtra_(S,I)(g)
+ CdefRemainder_(S,I,lambda)(g),
```

the no-defect read-off must identify the main trace with:

```text
QW_lambda(g,g).
```

Equivalently:

```text
FixedSNoDefectCompactFormReadOff(S,I):
  the no-defect fixed-S quantized differential trace has only the source
  channels already present in CCM25:

    W_(0,2),
    W_infty,
    -sum_p W_p,
    restricted QW_lambda,

  and creates no extra no-strip rank or pole channel.
```

## Evidence Boundary

| claim | evidence |
|---|---|
| CCM25 signs for `W_p`, `W_R=-W_infty`, `QW`, `Psi`, and `W_(0,2)` | `docs/audits/source-reread-v0.2.md:47`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:991-1033`, `1338-1361` |
| CCM25 restricted `QW_lambda` and prime-power pairing | `docs/audits/source-reread-v0.2.md:48`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:991-1001`, `1129-1130` |
| CC20 support-square template and trace-class convention | `docs/audits/source-reread-v0.2.md:49-54`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:1330-1345` |
| Battle 2 supplies the support-square to quantized differential transport | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md` |
| Battle 1 supplies the external rank/pole ledger | `docs/proofs/battle-1-test-quotient-proof-package.md` and `docs/proofs/rank-repair-finite-normal-form.md` |

## Lemma 1. Source Test Identification

Statement:

```text
SourceTestIdentification(lambda):
  the CCM25 restricted form is applied to the support-square test

    F_g = g^* * g,

  with the same half-density convention used in the positive fixed-S trace.
```

Proof.

The support-square trace contains `theta_S(g)^*` and `theta_S(g)`. The source
trace attached to that square is the convolution test:

```text
F_g=g^* * g.
```

CCM25 defines:

```text
QW(f,g)=Psi(f^* * g).
```

Therefore the source test read by `Psi` is exactly `F_g`. This prevents the
main term from using a shifted or unsquared test.

## Lemma 2. CCM25 Sign And Pole Normalization

Statement:

```text
CCM25NoDefectSignReadOff:
  the no-defect source main term has sign pattern

    W_(0,2) + W_infty - sum_p W_p.
```

Proof.

CCM25 gives:

```text
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F),
```

and:

```text
W_R=-W_infty.
```

Substitute the second equation into the first:

```text
Psi(F)
  =
W_(0,2)(F)+W_infty(F)-sum_p W_p(F).
```

The finite-prime term has the negative sign in `Psi`. The proof does not
derive finite-prime coefficients from a scalar even-trace shortcut; it reads
them from CCM25.

The CCM pole functional:

```text
W_(0,2)(F)
```

belongs inside `QW_lambda`. The route's `PoleJetExtra_(S,I)(g)` remains outside
`QW_lambda`; it records quotient directions introduced by the fixed-S
positive-trace matching. The triple vanishing kills both, but the proof must
not count them as the same term.

## Lemma 3. Restricted QW Lambda Read-Off

Statement:

```text
RestrictedQWLambdaReadOff(lambda,g):
  on the interval [lambda^(-1),lambda], CCM25 reads the no-defect source trace
  as QW_lambda(g,g).
```

Proof.

CCM25 gives the restricted form:

```text
QW_lambda(g,g)
  =
int_R |hat g(t)|^2 (2 partial_t theta(t))/(2 pi) dt
  +
2 Re(hat g(i/2) overline{hat g(-i/2)})
  -
sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>,
```

with:

```text
<g|T(n)g>
  =
n^(-1/2)((g^* * g)(n)+(g^* * g)(n^(-1))).
```

This formula is the restricted form of:

```text
W_(0,2) + W_infty - sum_p W_p
```

for the support-square test `F_g=g^* * g`.

Thus the no-defect quantized differential trace is not evaluated by a new
finite-prime computation. It is read through CCM25:

```text
Trace_source,no-defect(R_lambda U(F_g))
  =
QW_lambda(g,g).
```

## Lemma 4. No Extra No-Strip Channel

Statement:

```text
NoExtraNoStripChannel(S,I):
  after Battle 2 separates projection-order defects and after Battle 1 records
  the route rank/pole ledgers, the no-defect CCM25 read-off has no additional
  no-strip rank, pole, or derivative-jet channel.
```

Proof.

Battle 2 removes every projection-order mismatch from the main term and
charges it to endpoint-strip `Cdef`.

Battle 1 records the finite-dimensional channels outside `QW_lambda`:

```text
hat g(0),
hat g(+i/2),
hat g(-i/2).
```

Inside the source main term, CCM25 already accounts for:

```text
W_(0,2),
W_infty,
-sum_p W_p.
```

No derivative jet appears in the restricted CCM25 formula cited above. Hence
no additional no-strip channel remains after ledger collection.

## The Read-Off Theorem

Combine Lemmas 1 through 4.

The no-defect fixed-S quantized differential trace is first identified with
the source no-defect cutoff trace for:

```text
F_g=g^* * g.
```

CCM25 reads that source trace as:

```text
QW_lambda(g,g).
```

All terms outside this source main term have already been separated as:

```text
Rank_(S,I)(g),
PoleJetExtra_(S,I)(g),
CdefRemainder_(S,I,lambda)(g).
```

Therefore:

```text
FixedSNoDefectCompactFormReadOff(S,I)
```

holds at source-interface level.

## Consequence For Battle 1

The rank-repair package had reduced Battle 1 to:

```text
FixedSNoDefectCompactFormReadOff(S,I).
```

This file discharges that input, subject to the cited CCM25 and CC20 source
interfaces and to the Battle 2 transport package.

The Battle 1 remaining rank-repair statement becomes:

```text
RankRepairFiniteNormalForm(S,I)
```

at route-evidence level, with its endpoint-strip terms charged to Battle 3
`Cdef`.

## Current Status

```text
Source test identification:       proved from support-square test convention
CCM25 sign/pole normalization:    proved from source-interface formulas
Restricted QW_lambda read-off:    proved from source-interface formulas
No extra no-strip channel:        proved after Battles 1 and 2 ledger split
FixedSNoDefectCompactFormReadOff: source-conditional, route-evidence closed
Battle 1 rank repair:             closed at route-evidence level, Cdef-conditional
```
