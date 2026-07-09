# CCM24 Support-Window Transport Discharge

Status: proof package for the CCM24 source-interface transport layer.

This package attacks four CCM24 source-interface contracts:

```text
ccm24CanonicalSemilocalModel
ccm24SupportTransport
ccm24BoundedComparison
ccm24SoninComparison
```

The target is not the full semilocal theory. The target is narrower: the route
must use one source-backed fixed-`S` test and one source-backed support window
through every later read-off.

## Evidence Boundary

Official source package:

```text
https://arxiv.org/e-print/2310.18423
```

The relevant source file is `mainc2m24fine.tex`.

| claim | evidence |
|---|---|
| semilocal canonical model and introductory `V_S=M_S U_S` statement | `mainc2m24fine.tex:237-253` |
| support and Fourier-support transport through `eta_S` | `mainc2m24fine.tex:761-771` |
| canonical cyclic pair, `V_S=M_S U_S`, and Fourier grading as `s -> -s` | `mainc2m24fine.tex:786-804` |
| bounded comparison map with bounded inverse | `mainc2m24fine.tex:806-823` |
| dual/Sonin transport through `theta_S` | `mainc2m24fine.tex:983-1003` |
| Sonin-space comparison and fixed-window isomorphism | `mainc2m24fine.tex:1050-1060` |
| route admissible-window target | `docs/proofs/ccm25-restricted-read-off-discharge.md:77-119` |
| fixed-test exhaustion order | `docs/proofs/fixed-test-graph-cdef-exhaustion.md:1-45` |

## Target Statement

The CCM24 discharge target is:

```text
CCM24SupportWindowTransportDischarge(S,I,lambda,g):
  the fixed-S test used in the positive trace, the CCM25 restricted read-off,
  and the fixed-test exhaustion all come from the same CCM24 source window.
```

The route must pass this chain:

```text
source test g and source window
      |
      v
eta_S support and Fourier support transport
      |
      v
canonical fixed-S coordinate V_S=M_S U_S
      |
      v
bounded comparison with bounded inverse
      |
      v
theta_S / Sonin fixed-window comparison
      |
      v
same lambda window used by QW_lambda and Cdef exhaustion
```

## Lemma 1. Canonical Fixed-S Model

Statement:

```text
CCM24CanonicalFixedSModel(S):
  the route's fixed-S Hilbert model is the CCM24 canonical model under
  V_S=M_S U_S, and its Fourier grading is reflection s -> -s.
```

Proof.

CCM24 introduces:

```text
U_S = F_mu o w_S
M_S(f)(s) = product_v L_v(1/2-is)^(-1) f(s)
V_S = M_S o U_S
```

Evidence:

```text
mainc2m24fine.tex:237-253
mainc2m24fine.tex:786-804
```

The same source lines state that `V_S` gives the canonical form of the cyclic
pair and sends the Fourier grading to the symmetry:

```text
s -> -s.
```

Therefore the route may form commutators and support-square identities only
after moving all operators into this one canonical coordinate. This is the
coordinate rule used by the Battle 2 proof package:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:93-142
```

Output:

```text
ccm24CanonicalSemilocalModel
```

as the canonical model object used by the route.

## Lemma 2. Eta Support And Fourier-Support Transport

Statement:

```text
CCM24EtaSupportTransport(S,lambda,g):
  support and Fourier-support containment for the source test transport through
  eta_S to the same fixed-S window.
```

Proof.

CCM24 states that for `lambda > 0`:

```text
eta_S(P_lambda) subset P_lambda^S
```

and that Fourier transform commutes with `eta_S`:

```text
Fourier_S o eta_S = eta_S o Fourier_R.
```

It then gives the Fourier-support containment:

```text
eta_S(hat P_lambda) subset hat P_lambda^S.
```

Evidence:

```text
mainc2m24fine.tex:761-771
```

Thus the route cannot choose separate support and Fourier windows after the
test enters the fixed-`S` model. Both windows are transported from the same
source cutoff.

Output:

```text
source support in CCM24 window
Fourier support in the same CCM24 window
```

for the route's `WindowSupportContainment`.

## Lemma 3. Bounded Comparison Preserves The Analytic Class

Statement:

```text
CCM24BoundedComparisonPreservation(S):
  the comparison from the source Hilbert model to the fixed-S canonical model
  has bounded inverse, so transported bounded and trace-ideal statements do not
  change their analytic class.
```

Proof.

CCM24 gives a bounded comparison map with bounded inverse and a commutative
diagram between the source and fixed-`S` Hilbert models:

```text
mainc2m24fine.tex:806-823
```

The source proof identifies the reason: the finite Euler-factor product is
bounded with bounded inverse for fixed finite `S`.

Consequences for the route:

```text
bounded operators remain bounded;
Hilbert-Schmidt estimates survive bounded left and right comparison;
trace-class products survive bounded left and right comparison;
fixed-window graph seminorms remain comparable.
```

This lemma does not create a trace-class theorem by itself. It preserves the
class after CC20 trace legality or Battle 3 endpoint-strip estimates provide
the trace-ideal input.

Output:

```text
ccm24BoundedComparison
```

as the comparison gate used before trace and norm estimates move between
source and fixed-`S` coordinates.

## Lemma 4. Theta And Sonin Fixed-Window Compatibility

Statement:

```text
CCM24ThetaSoninWindowCompatibility(S,lambda,g):
  theta_S transports the fixed source test into the same Sonin window used by
  the fixed-test exhaustion.
```

Proof.

CCM24 states that Fourier transform commutes with `theta_S`:

```text
Fourier_S o theta_S = theta_S o Fourier_R.
```

It also gives the comparison diagram involving `theta_S`, `upsilon_infty`,
`upsilon_S`, and the comparison map:

```text
mainc2m24fine.tex:983-1003
```

The Sonin-space comparison states that `upsilon_S` is an isomorphism from the
semilocal Sonin space to the fixed Hilbertian model for a fixed `lambda`:

```text
mainc2m24fine.tex:1050-1060
```

Thus the fixed-test exhaustion package may fix:

```text
g, I, S_A, graph order
```

before sending:

```text
lambda -> infinity.
```

The comparison does not allow the proof to grow `S` with `lambda` or to swap in
a new cutoff after the CCM25 restricted read-off.

Output:

```text
ccm24SoninComparison
```

for the fixed-window exhaustion leg.

## Lemma 5. One Window For QW_lambda And Cdef

Statement:

```text
CCM24OneWindowInvariant(S,I,lambda,g):
  the restricted CCM25 form QW_lambda and the endpoint-strip Cdef exhaustion
  use the same source-backed window.
```

Proof.

The CCM25 restricted read-off package requires:

```text
1 < lambda
source support in the CCM24 window
Fourier support in the same window
window contained in [lambda^(-1),lambda]
```

Evidence:

```text
docs/proofs/ccm25-restricted-read-off-discharge.md:77-119
```

The fixed-test Cdef package requires the test data to be fixed before the
lambda limit:

```text
docs/proofs/fixed-test-graph-cdef-exhaustion.md:1-45
```

Lemmas 2 through 4 provide the CCM24 source-backed window and comparison maps.
Therefore the same window controls:

```text
QW_lambda support
finite-prime visibility before lambda exhaustion
Cdef endpoint strips
fixed-test Sonin exhaustion
```

This blocks the main fixed-`S` drift failure:

```text
the trace uses one cutoff,
the restricted Weil form uses another,
and Cdef exhaustion sends a third cutoff to infinity.
```

Output:

```text
WindowLambdaCompatibility
```

as a source-backed condition, not a route-local parameter choice.

## Integrated Discharge Result

Combine Lemmas 1 through 5:

```text
CCM24SupportWindowTransportDischarge(S,I,lambda,g).
```

The proof-package-level result is:

```text
the route's fixed-S positive trace,
the CCM25 restricted read-off,
and the fixed-test Cdef exhaustion
all use one CCM24 source-backed support window.
```

Dependency graph:

```text
canonical model V_S=M_S U_S
        |
        v
eta_S support/Fourier transport
        |
        v
bounded comparison with bounded inverse
        |
        v
theta_S and Sonin fixed-window comparison
        |
        v
WindowLambdaCompatibility for QW_lambda and Cdef exhaustion
```

## Remaining Boundary

This package closes the CCM24 support-window transport layer at
source-interface proof-package level. It leaves these stronger evidence tasks:

| task | reason |
|---|---|
| formalize or import the CCM24 Hilbert-model theorems | this package cites the source statements and does not rebuild the semilocal analysis |
| replace symbolic window predicates with concrete support sets | Lean still represents support/window obligations abstractly |
| prove trace-ideal preservation through comparison maps formally | this package records the bounded-comparison mechanism, while the formal trace-ideal bridge remains future Lean work |

The route remains source-conditional until these CCM24 contracts are discharged
by formal proofs, accepted imports, or a referee-checked source bridge.
