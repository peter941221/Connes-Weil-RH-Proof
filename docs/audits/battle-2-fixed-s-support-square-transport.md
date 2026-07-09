# Battle 2 Fixed-S Support-Square Transport

Status: proof audit for the fixed-S transport package behind Theorem 1.

This file does not certify Battle 2. It separates the trace-level theorem from
the route-note phrase:

```text
same quantized-calculus expansion.
```

That phrase cannot carry the proof. The fixed-S route must show, term by term,
that the positive support-square trace transports to the fixed-S quantized
differential trace modulo only rank, pole, and endpoint-strip `Cdef` terms.

## Result

Battle 2 now has a route-evidence proof package. It expands the fixed-S
support-square transport term by term and no longer relies on the phrase
`same quantized-calculus expansion`.

The imported exploration note gives the target at
`docs/ConnesWeilPositivity.md:147084-147115` and later marks it
`closed at route-paper level` at `docs/ConnesWeilPositivity.md:147258-147263`.
The route should not rely on that label. The proof package
`docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md`
replaces the label with a decomposed proof of:

```text
FixedSQuantizedSupportSquareTransport(S,I,lambda).
```

The theorem is the bridge:

```text
positive fixed-S support square
        |
        v
fixed-S quantized differential main term
        |
        +-- rank ledger
        +-- pole ledger
        +-- endpoint-strip Cdef remainder
```

Only after this bridge can the manuscript read the no-defect main term through
the CCM25 restricted Weil form.

## Target Statement

In the canonical fixed-S model:

```text
V_S = M_S U_S,
```

prove:

```text
Tr(theta_S(g)^*
   P_(S,G) P_hat_(S,G) P_(S,G)
   theta_S(g))

=

Tr(theta_S(g)^*
   [-P_(S,G)(1/2)u_S^(-1)d^-u_S P_(S,G)]
   theta_S(g))

+ Rank_(S,I)(g)
+ PoleJetExtra_(S,I)(g)
+ CdefRemainder_(S,I,lambda)(g),
```

with:

```text
|CdefRemainder_(S,I,lambda)(g)|
  <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The manuscript states this shape in
`docs/manuscripts/connes-weil-rh-proof-draft.md:733-760`.

## Required Proof Chain

Battle 2 must prove this chain:

```text
source support projection P_R(lambda)
      |
      v
fixed-S support projection P_S(lambda)
      |
      v
canonical support projection P_(S,G)(lambda)

source Fourier support projection P_hat_R(lambda)
      |
      v
fixed-S Fourier projection P_hat_S(lambda)
      |
      v
canonical Fourier projection P_hat_(S,G)(lambda)

P_(S,G) P_hat_(S,G) P_(S,G)
      |
      v
-P_(S,G)(1/2)u_S^(-1)d^-u_S P_(S,G)
      |
      +-- no-strip rank and pole terms
      +-- projection-order defects
                |
                v
          endpoint-strip Cdef
```

Each arrow needs a named theorem or source formula.

## Evidence Map

| subclaim | current evidence | audit status |
|---|---|---|
| support projections transport from the source model | `docs/ConnesWeilPositivity.md:143728-143750`, `147119-147129`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:762-771` | strong route lemma candidate |
| Fourier projections transport with the same comparison map | `docs/ConnesWeilPositivity.md:143752-143762`, `147119-147129`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:762-771` | strong route lemma candidate |
| canonical phase pullback gives `P_hat_(S,G)=u_S^(-1) I P_(S,G) I u_S` modulo projection-order defects | `docs/ConnesWeilPositivity.md:143764-143778`, `147131-147140`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:773-780` | needs exact operator-domain statement |
| CC20 gives the no-defect archimedean support-square template | `docs/ConnesWeilPositivity.md:147155-147159`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:782-786`, `1338-1341` | source-interface obligation |
| fixed-S transport replaces `u_infty` by `u_S` | `docs/ConnesWeilPositivity.md:147146-147170`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:788-792` | weakest algebraic step |
| no-strip boundary terms become rank and pole ledgers | `docs/ConnesWeilPositivity.md:147173-147176`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:832-840`, `864-878` | depends on Battle 1 |
| projection-order defects contain an `M_S` or `M_S^*` commutator and enter `Cdef` | `docs/ConnesWeilPositivity.md:147178-147182`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:1092-1094`, `1338-1342` | depends on Battle 3 |
| theta smoothing makes the trace operations legal | `docs/ConnesWeilPositivity.md:147184-147187`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:1059-1074`, `1096-1112`, `1330-1345` | trace-class proof obligation |

## Subclaim 1. Projection Transport

Required theorem:

```text
FixedSProjectionTransport(S,lambda):
  P_S(lambda)=S(P_R(lambda))
  and
  P_hat_S(lambda)=S(P_hat_R(lambda)).
```

After the canonical map `V_S=M_S U_S`, the theorem must identify these
projections with the operators under the positive trace:

```text
P_(S,G)(lambda),
P_hat_(S,G)(lambda).
```

This subclaim blocks a common error: treating the fixed-S support cutoff as a
new projection with the same notation. It must be the transported source
projection.

## Subclaim 2. Phase Pullback In One Coordinate

Required theorem:

```text
FixedSPhasePullback(S,lambda):
  in the common scattering coordinate,
  P_hat_(S,G)=u_S^(-1) I P_(S,G) I u_S
  modulo listed projection-order defects.
```

The commutators:

```text
[P,M_S],
[P_hat,M_S],
[P,M_S^*],
[P_hat,M_S^*]
```

must live in one Hilbert-space coordinate. If the proof forms a commutator
between operators in different Hilbert spaces, the argument fails.

## Subclaim 3. No-Defect CC20 Template

Required theorem:

```text
FixedSNoDefectSupportSquareTemplate(S,I,lambda):
  the no-defect part of the fixed-S support-square trace is the CC20
  support-square template with u_infty replaced by u_S.
```

Source template:

```text
P P_hat P = -P(1/2)u_infty^(-1)d^-u_infty P.
```

The fixed-S proof must show why the same commutator calculation applies after
transport through `V_S=M_S U_S`. The sentence:

```text
same quantized-calculus expansion
```

is only a claim until the proof expands all terms generated by `M_S` and
`M_S^*`.

## Subclaim 4. Defect Classification And Trace Legality

Required theorem:

```text
FixedSDefectClassification(S,I,lambda,J):
  every leftover fixed-S model-change term is one of:
    rank ledger,
    pole ledger,
    endpoint-strip Cdef remainder.
```

Trace-class gate:

```text
P_hat_(S,G) P_(S,G) theta_S(g) in S_2.
```

After this gate, the positive trace is an ordinary trace of `A^*A`. Endpoint
strip terms must be trace-class before cyclicity is used. No projection defect
may be read through CCM25 as part of `QW_lambda`.

## Rejection Tests

Battle 2 fails if any of these occur:

| rejection test | why it kills the route |
|---|---|
| the proof uses `same quantized-calculus expansion` without term expansion | the fixed-S transport is assumed, not proved |
| `P_(S,G)` or `P_hat_(S,G)` is not shown to be the transported source projection | the source trace and route trace may be different operators |
| commutators with `M_S` are formed before moving to one coordinate | the algebra is undefined |
| a projection-order defect contributes to the no-defect CCM25 read-off | `QW_lambda` gets an extra term |
| trace cyclicity is used before Hilbert-Schmidt or trace-class membership | positivity and read-off become formal manipulations |
| the rank/pole terms are used before Battle 1 identifies their support | Theorem 2 may kill the wrong ledgers |
| the `Cdef` bound is used before Battle 3 defines the trace-norm quantity | the error term is only named, not controlled |

## Lean Follow-Up

The Lean route should not accept Battle 2 as a bare proof field. The target
shape should expose at least these fields:

```text
projectionTransport
phasePullback
noDefectSupportSquareTemplate
defectClassification
traceLegality
```

Only their combination should construct:

```text
FixedSQuantizedSupportSquareTransport(S,I,lambda).
```

## Acceptance Gate

Battle 2 passes only after the manuscript or proof package contains
theorem-level proofs for:

```text
FixedSProjectionTransport(S,lambda)
FixedSPhasePullback(S,lambda)
FixedSNoDefectSupportSquareTemplate(S,I,lambda)
FixedSDefectClassification(S,I,lambda,J)
TraceClassCyclicSupportSquareIdentity(S,I,lambda)
```

and combines them into:

```text
FixedSQuantizedSupportSquareTransport(S,I,lambda).
```

The current status is:

```text
Battle 2 proof package written,
closed at route-evidence level, source-conditional.
```
