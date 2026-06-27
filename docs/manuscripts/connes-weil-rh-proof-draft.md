# Connes-Weil RH Proof Draft

Status: v0.1 referee-readable source-conditional manuscript.

This file gives a referee-readable v0.1 version of the Connes-Weil route-paper
proof. It puts the proof in theorem order, records the source-line audit needed
to check the imported results, and separates source theorems from project
lemmas. It does not claim Clay-level certification, journal acceptance, or Lean
formalization. It records a source-conditional manuscript whose cited source
theorems, if accepted as stated, imply RH by the route theorem below.

Source ledger:

| claim | local evidence |
|---|---|
| Final route-paper chain | `ConnesWeilPositivity.md:146963-146982` |
| Semilocal support reflection | `ConnesWeilPositivity.md:135197-135206`, `135480-135532` |
| Projection closure and two-projection intertwining | `ConnesWeilPositivity.md:135208-135342` |
| Phase pullback identity | `ConnesWeilPositivity.md:135346-135406`, `135733-135798` |
| Endpoint-strip theorem statement and proof | `ConnesWeilPositivity.md:146192-146320` |
| Theta-smoothed trace-class and cyclic trace legality | `ConnesWeilPositivity.md:143859-144140` |
| Source trace operator equality audit | `ConnesWeilPositivity.md:143025-143153`, `143540-143724`, `143780-143857` |
| Final definitions block | `ConnesWeilPositivity.md:146688-146746` |
| Cdef norm formula | `ConnesWeilPositivity.md:146790-146853` |
| Fixed-S support-square transport | `ConnesWeilPositivity.md:147084-147196` |
| Hostile audit verdict | `ConnesWeilPositivity.md:147198-147264` |
| Current project memory verdict | `MEMORY.md:22073-22095` |

Stable citation targets for a public draft:

| source claim | stable citation target |
|---|---|
| CCM canonical fixed-S model `V_S=M_S U_S` | CCM 2310.18423, Proposition 4.2 |
| Bounded comparison map `S` | CCM 2310.18423, Proposition 4.3 |
| Fourier compatibility `F_S S = S F_R` | CCM 2310.18423, Proposition 4.1(iii) and Proposition 4.7(i) |
| Finite-prime Weil term | CCM 2511.22755, equation `bombieriexplicit1bis` |
| Weil form `QW(f,g)=Psi(f^* * g)` | CCM 2511.22755, equation `bombtest` |
| Pole functional `W_(0,2)` | CCM 2511.22755, equation `bombtest-0` |
| Restricted quadratic form `QW_lambda` | CCM 2511.22755, equation `quadratsemi` |
| Prime-power operator pairing | CCM 2511.22755, equation `quadratsemi1` |
| Archimedean trace-class theorem | Connes--Consani 2006.13771, Proposition 1.5 |
| Support-square to quantized differential identity | Connes--Consani 2006.13771, Section 3 calculation following Proposition 1.5 |
| Mellin/half-density convention | Connes--Consani 2006.13771, equation (145) |
| Finite-vanishing Weil positivity criterion | Connes--Consani 2006.13771, Proposition C.1 |

Source reread certificate:

| source claim | reread result |
|---|---|
| CCM canonical semilocal model | CCM24 Proposition 4.2 states `V_S=M_S U_S` and identifies the canonical cyclic pair; it also states that the Fourier transform becomes reflection `s -> -s` |
| CCM bounded comparison | CCM24 Proposition 4.3 states that the comparison map `S` is bounded with bounded inverse |
| CCM Fourier compatibility | CCM24 Proposition 4.1(iii) and Proposition 4.7(i) state `F_S S = S F_R` |
| Finite-prime Weil term | CCM25 equation `bombieriexplicit1bis` gives `W_p(F)=(log p) sum p^(-m/2)(F(p^m)+F(p^(-m)))` |
| Weil form and pole functional | CCM25 equations `bombtest` and `bombtest-0` give `QW(f,g)=Psi(f^* * g)` and `W_(0,2)(F)=hat F(i/2)+hat F(-i/2)` |
| Restricted quadratic form | CCM25 equations `quadratsemi` and `quadratsemi1` give `QW_lambda` and the prime-power operator pairing |
| Archimedean trace-class and support-square template | CC20 Proposition 1.5 and the following Section 3 calculation give trace-class legality and `P P_hat P=-P(1/2)u_infty^(-1)d^-u_infty P` |
| Mellin convention and final RH exit | CC20 equation (145) gives the half-density convention, and Proposition C.1 gives the finite-vanishing Weil positivity criterion |

Formula dependency map:

| formula in this draft | source target | manuscript use | sign/normalization check |
|---|---|---|---|
| `V_S=M_S U_S` | CCM24 Proposition 4.2 | defines the canonical fixed-S model | model transport happens before any trace read-off |
| `F_S S = S F_R` | CCM24 Proposition 4.1(iii), Proposition 4.7(i) | transports Fourier-support projections | used only as a range/projection intertwining statement |
| `P P_hat P=-P(1/2)u_infty^(-1)d^-u_infty P` | CC20 Section 3 after Proposition 1.5 | supplies the no-defect support-square template | fixed-S changes are charged to rank, pole, or `Cdef` ledgers |
| `QW(f,g)=Psi(f^* * g)` | CCM25 equation `bombtest` | converts the no-defect quantized trace into the Weil form | test conversion is always `F_g=g^* * g` |
| `W_(0,2)(F)=hat F(i/2)+hat F(-i/2)` | CCM25 equation `bombtest-0` | identifies the CCM pole functional | not identified with the extra `PoleJetExtra` ledger |
| `Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F)` | CCM25 equation `bombtest` | fixes the global Weil-form sign pattern | with `W_R=-W_infty`, the archimedean term is `+W_infty` |
| `W_p(F)=(log p) sum p^(-m/2)(F(p^m)+F(p^(-m)))` | CCM25 equation `bombieriexplicit1bis` | fixes the finite-prime coefficient | finite primes enter as `-sum_p W_p`, not by a local even-trace shortcut |
| `QW_lambda(g,g)` formula on `[lambda^(-1),lambda]` | CCM25 equation `quadratsemi` | gives the restricted quadratic form used in Theorem 1 | pole term is the displayed `2 Re(hat g(i/2) overline{hat g(-i/2)})` |
| `<g|T(n)g>=n^(-1/2)((g^* * g)(n)+(g^* * g)(n^(-1)))` | CCM25 equation `quadratsemi1` | gives the prime-power operator pairing | finite-prime sign is inherited from the `-sum` in `QW_lambda` |

Source-line audit for v0.1:

| imported item | arXiv source file and lines | use in this manuscript |
|---|---|---|
| CCM24 canonical semilocal transform and introduction theorem | `mainc2m24fine.tex:237-253` | defines `U_S`, `M_S`, `V_S=M_S U_S`, and the Fourier grading becoming reflection |
| CCM24 support transport for `eta_S` | `mainc2m24fine.tex:761-771` | supports Lemma A and the support/Fourier-support transport in Lemma B |
| CCM24 canonical fixed-S cyclic pair | `mainc2m24fine.tex:786-804` | supports the fixed-S canonical Hilbert model and the `s -> -s` grading |
| CCM24 bounded comparison map | `mainc2m24fine.tex:806-823` | supplies boundedness and bounded inverse for the comparison map used in Lemma B |
| CCM24 dual Fourier compatibility | `mainc2m24fine.tex:983-1003` | supports the Fourier-side intertwining used in Lemma B |
| CCM24 Sonin-space comparison diagram | `mainc2m24fine.tex:1050-1060` | supports the fixed support-window comparison used in Theorem 3 |
| CCM25 finite-prime and archimedean terms | `mc2arXiv.tex:445-470` | supplies `W_p`, `W_R=-W_infty`, `QW`, `Psi`, and `W_(0,2)` |
| CCM25 restricted Weil quadratic form | `mc2arXiv.tex:530-540` | supplies `QW_lambda` and `<g|T(n)g>` in Theorem 1 |
| CC20 archimedean support-square trace formula | `weil-compo.tex:378-387` | supplies the source trace formula and `traceequa` |
| CC20 trace-class verification for the archimedean summand | `weil-compo.tex:448-464` | supplies the trace-class argument imported in Lemma 2 |
| CC20 Fourier/Mellin convention | `weil-compo.tex:2014-2030` | fixes the half-density and Mellin convention used in Theorem 4 |
| CC20 quantized calculus trace-class lemma | `weil-compo.tex:2106-2121` | supplies the trace ideal template used in Lemma 2 |
| CC20 signs and normalizations appendix | `weil-compo.tex:2131-2165` | fixes `u_infty`, `qd u`, and the sign of the archimedean trace |
| CC20 finite-vanishing positivity criterion | `weil-compo.tex:2072-2085` | supplies Proposition C.1, the final RH exit |

References used in this draft:

| key | reference | public source | role in this draft |
|---|---|---|---|
| CCM24 | Alain Connes, Caterina Consani, Henri Moscovici, "Zeta Zeros and Prolate Wave Operators: Semilocal Adelic Operators", arXiv:2310.18423v2 | https://arxiv.org/abs/2310.18423 | canonical fixed-S Hilbert model, support/Fourier transport, bounded comparison |
| CCM25 | Alain Connes, Caterina Consani, Henri Moscovici, "Zeta Spectral Triples", arXiv:2511.22755 | https://arxiv.org/abs/2511.22755 | `QW`, `QW_lambda`, finite-prime Weil terms, half-density normalization |
| CC20 | Alain Connes, Caterina Consani, "Weil positivity and Trace formula: the archimedean place", arXiv:2006.13771v1 | https://arxiv.org/abs/2006.13771 | support-square trace template, archimedean trace-class proof, Mellin convention, Proposition C.1 |

## Dependency And Non-Circularity Audit

The route theorem uses three different kinds of inputs. Keeping them separate
prevents the proof from smuggling the desired Weil positivity into an earlier
lemma.

| class | inputs | use |
|---|---|---|
| Source theorem | CCM24 fixed-S model, support/Fourier transport, bounded comparison | identifies the Hilbert model and transported projections |
| Source theorem | CC20 trace-class support-square calculation and Proposition C.1 | supplies the archimedean trace template and the RH exit criterion |
| Source theorem | CCM25 `QW`, `QW_lambda`, finite-prime and pole normalization | reads the no-defect quantized trace as the Weil quadratic form |
| Project lemma | endpoint-strip `Cdef` trace ideal and fixed-S support-square transport | proves that model-change errors do not enter the main Weil term |
| Project lemma | fixed-test exhaustion | removes `Cdef` after the support set and finite `S_A` are fixed |
| Elementary lemma | eta-function side condition at `1/2` | verifies that `F={0,1/2,1}` is allowed in Proposition C.1 |

None of the project lemmas assumes Weil positivity. The only positivity input
before Proposition C.1 is the Hilbert-space square

```text
(P_hat P theta_S(g))^* (P_hat P theta_S(g)).
```

The CCM `QW_lambda` formula is used only after the support-square trace has
been transported, trace-class membership has been checked, and rank, pole, and
`Cdef` ledgers have been separated.

## Proof Spine

```text
Definitions
  |
  v
Projection transport lemmas
  |
  v
EndpointStripCdefTraceIdealTheorem
  |
  v
FixedSQuantizedSupportSquareTransport
  |
  v
Source trace read-off and operator equality audit
  |
  v
Fixed-S Source-Normalized Positive Trace
  |
  v
Triple-killed corrected trace inequality
  |
  v
Fixed-test exhaustion
  |
  v
Finite-set side-condition check
  |
  v
Connes--Consani Proposition C.1 with F={0,1/2,1}
  |
  v
Riemann Hypothesis
```

## Definitions

Fix a finite set `S` of places containing the archimedean place. Let

```text
V_S = M_S U_S
```

be the CCM canonical semilocal transform. Write `H_S` for the resulting
canonical Hilbert space.

For `lambda > 1`, let `P_S(lambda)` denote the semilocal multiplicative support
projection in the source model. Define the canonical support projection by

```text
P_(S,G)(lambda) = V_S P_S(lambda) V_S^(-1).
```

Let `F_S` denote the grading/Fourier symmetry of the semilocal cyclic pair.
Define

```text
P_hat_(S,G)(lambda) = F_S^(-1) P_(S,G)(lambda) F_S.
```

The CCM canonical Hilbert model makes `F_S` unitary. In the involutive
normalization used below, range notation such as `F_S Ran(P)` and projection
notation such as `F_S^(-1) P F_S` describe the same transported closed
subspace. This convention is used only for support and Fourier-support
projections; all trace identities below keep the conjugating operators visible.

For a compactly supported half-density test `g`, let `theta_S(g)` denote the
bounded test operator obtained from the semilocal representation after
transport by `V_S`. In the scattering coordinate it acts as multiplicative
convolution by `g`; in the canonical coordinate it has the form

```text
theta_S(g)_can = M_S theta_S(g)_sc M_S^(-1).
```

Let

```text
u_S = M_S^(-1) I M_S I
```

be the phase multiplier. In spectral coordinates,

```text
u_S(s) = prod_(v in S) L_v(1/2-is) / L_v(1/2+is).
```

Let `Q` denote the Connes--Consani trace-remainder operator from the angle
operator calculus. In the local coordinate used for the trace-remainder
calculation, `Q` acts through the finite graph differential

```text
D = D_u^2 + D_u
```

plus the boundary terms described in Connes--Consani Lemmas 5.1 and 5.2.

All commutators with `M_S` below are written in one common scattering
coordinate. That is, the proof first transports operators to the same
`L^2(R,ds)` model through `U_S` and the fixed Radon-Nikodym identification
given by `M_S`. In this common model, `M_S` and `M_S^*` act as multiplication
operators with bounded inverse on the fixed finite-S graph domain, while
`P` and `P_hat` are the transported support and Fourier-support projections.
Thus symbols such as

```text
[P,M_S], [P_hat,M_S], [P,M_S^*], [P_hat,M_S^*]
```

mean commutators in this common model, not maps between different Hilbert
spaces.

For fixed graph order `J`, define `Cdef_(S,I,lambda,J)(g)` as the trace-norm
sum of endpoint-strip normal-form terms created when the proof transports
support and Fourier-support projections through `M_S` and `M_S^*`.

Let `R_(S,I,lambda,J)` be the finite index set of terms

```text
alpha = (r,s,a,X_0,X_1,b,T_a)
```

with

```text
r+s <= J,
supp(b) subset E_(lambda,a),
X_0 and X_1 fixed graph-bounded factors,
T_a a bounded shift/dilation factor.
```

Define

```text
Cdef_(S,I,lambda,J)(g)
  :=
sum_(alpha in R_(S,I,lambda,J))
  || theta(D^r g) X_0 M_b T_a X_1 theta(D^s g)^* ||_1

  +

sum_(beta in Q R_(S,I,lambda,J))
  |BoundaryStripTrace_beta(g)|.
```

Here `Q R_(S,I,lambda,J)` denotes the finite family obtained by applying the
Connes--Consani `Q` trace-remainder formula to the same endpoint-strip
normal-form terms. Each `BoundaryStripTrace_beta(g)` contains at least one
endpoint-strip factor before the boundary evaluation.

The route uses the comparison

```text
Cdef_(S,I,lambda,J)(g)
  <=
C'_(S,I,J)(g) Cdef_graph_(S,I,lambda,J')(g),
```

and the graph/prolate exhaustion statement

```text
Cdef_graph_(S_A,I,lambda,J')(g) -> 0
```

with `g` and `S_A` fixed.

### Admissible Windows For Theorem 1

Theorem 1 is used only for admissible tuples `(S,I,lambda,g)`.

An admissible tuple satisfies:

```text
S is finite and contains the archimedean place,
lambda > 1,
I subset [lambda^(-1),lambda],
supp(g) subset I.
```

Let

```text
F_g = g^* * g.
```

The finite-prime visibility condition is:

```text
if F_g(p^m) or F_g(p^(-m)) can be nonzero for some m >= 1,
then p is in S.
```

Equivalently, if `supp(F_g) subset exp([-A,A])`, it is enough to take

```text
S_A={infinity} union {p : log p <= A}.
```

This condition prevents a fixed-S trace from being read as the full restricted
Weil form while omitting prime-power atoms visible to `F_g`. In the final
exhaustion step, `g` is fixed first, then `S_A` is fixed from this support
condition, and only then does `lambda` tend to infinity.

## Projection Transport Lemmas

These lemmas expand the "projection transport" line in the proof spine. Their
job is to exclude an extra semilocal support component and to identify the
Euler phase as a consequence of the canonical CCM model, rather than as an
inserted multiplier.

### Lemma A. Semilocal Support Reflection

For fixed finite `S`, the semilocal periodization map reflects the module
support window:

```text
E_S f supported in (0,lambda]
  <=>
f supported in (0,lambda].
```

Proof. In the `K_S`-invariant module coordinate, the semilocal
periodization has the one-sided finite-prime form

```text
E_S f(u)=sum_(a in A_S) c_a f(au).
```

The inverse is a finite bounded difference operator

```text
E_S^(-1)=prod_(p in S_fin)(1-T_p).
```

If `E_S f` vanishes almost everywhere on `(lambda,infty)`, then every shifted
argument appearing in the finite product also lies above `lambda`. Applying
`E_S^(-1)` gives `f(u)=0` for almost every `u>lambda`. CCM Proposition 4.1
gives the reverse inclusion.

This proves the support-reflection step used below.

### Lemma B. Projection Closure And Two-Projection Intertwining

In the fixed finite-S semilocal Hilbert model,

```text
Ran(P_S(lambda))     = S Ran(P_R(lambda)),
Ran(P_hat_S(lambda)) = S Ran(P_hat_R(lambda)).
```

After pulling back through the fixed-S metric `G_S=M_S^*M_S`, the canonical
operators `P_(S,G)` and `P_hat_(S,G)` are the `G_S`-orthogonal projections onto
these transported ranges.

Proof. CCM Proposition 4.3 gives a bounded comparison map `S` with
bounded inverse between the archimedean and semilocal Hilbert models. Thus
each `K_S`-invariant semilocal vector has the form `h=S(f)` for a unique
archimedean vector `f`.

If `h` lies in the semilocal support subspace `P_S(lambda)`, then
`w_S(h)=E_S f` is supported in `(0,lambda]`. Lemma A implies that `f` is
supported in `(0,lambda]`. Hence

```text
h in P_S(lambda)
  =>
h = S(f) with f in P_R(lambda).
```

CCM Proposition 4.1 gives the reverse inclusion

```text
S(P_R(lambda)) subset P_S(lambda).
```

Therefore

```text
P_S(lambda)=S(P_R(lambda))
```

at the level of closed Hilbert subspaces.

The Fourier-side equality follows from CCM Fourier compatibility:

```text
F_S S = S F_R.
```

Consequently

```text
Ran(P_hat_S(lambda))
  =
F_S Ran(P_S(lambda))
  =
F_S S Ran(P_R(lambda))
  =
S F_R Ran(P_R(lambda))
  =
S Ran(P_hat_R(lambda)).
```

Since the Fourier symmetries are unitary involutions in the canonical
normalization, this range equality is equivalent to the conjugated-projection
identity used in the definition of `P_hat`.

This proves the projection closure and two-projection intertwining used below.

### Lemma C. Phase Pullback Identity

In the route convention,

```text
P_hat_S = u_S^(-1) I P I u_S,
```

where

```text
u_S(s)=prod_(v in S) L_v(1/2-is)/L_v(1/2+is).
```

Proof. CCM writes the canonical semilocal model as

```text
V_S=M_S U_S,

M_S(s)=prod_(v in S) L_v(1/2-is)^(-1).
```

Under `V_S`, the semilocal Fourier transform becomes the reflection

```text
I:s -> -s.
```

Pulling the Fourier-side support projection through `M_S` produces the scalar

```text
M_S^(-1) I M_S I
  =
prod_(v in S) L_v(1/2-is)/L_v(1/2+is)
  =
u_S(s).
```

The archimedean Connes--Consani convention fixes the direction of conjugation:

```text
P_hat = u_infty^(-1) I P I u_infty.
```

The fixed-S identity follows with `u_infty` replaced by `u_S`.

This proves the phase pullback identity used in the support-square calculation.

## Lemma 1. Endpoint-Strip Trace Ideal

Fix finite `S`, compact support interval `I`, and graph order `J`. Let `Delta`
be any projection-order defect generated in the fixed-S canonical transport by
one of

```text
[P,M_S], [P_hat,M_S], [P,M_S^*], [P_hat,M_S^*],
```

with bounded fixed-S graph factors and Euler multipliers inserted on either
side. Then, for every compactly supported test `h` in the fixed graph class,

```text
theta(h) Delta theta(h)^*
```

belongs to the trace ideal used in the Connes--Consani support-square trace,
and

```text
||theta(h) Delta theta(h)^*||_1
  <= C_(S,I,J)(h) Cdef_(S,I,lambda,J)(h).
```

Moreover, applying the Connes--Consani `Q` trace-remainder extraction to this
operator produces only bulk endpoint-strip trace-class terms and boundary
endpoint-strip rank terms. These terms satisfy the same `Cdef` bound.

Proof. Each projection-order defect contains a commutator with `M_S` or
`M_S^*`. The fixed-S commutator calculus writes every such defect as a finite
sum of endpoint-strip shifted kernels

```text
theta(D^r h) X_0 M_b T_a X_1 theta(D^s h)^*,
```

where `r+s <= J'`, the multiplier `b` has support inside a finite endpoint
strip `E_(lambda,a)`, and `X_0,X_1` are fixed graph-bounded factors.

Factor the operator through the strip:

```text
L2(R) --B_s--> L2(E_(lambda,a)) --A_r--> L2(R).
```

The Hilbert-Schmidt estimates give

```text
||A_r B_s||_1
  <= ||A_r||_2 ||B_s||_2
  <= C_(S,I,J)(h) Cdef_(S,I,lambda,J)(h).
```

After summing the finite-S Euler coefficient budget, the product belongs to the
trace ideal and obeys the displayed trace-norm estimate.

The operator `Q` differentiates only a bounded number of times, so it raises
the graph order by a fixed amount. Bulk terms keep the endpoint-strip factor.
Boundary evaluations also retain a strip factor before the evaluation
functional. A pure no-strip boundary jet would require a path from `theta(h)`
to the boundary evaluation with no commutator-generated strip factor, which
cannot occur for `Delta`.

## Lemma 2. Theta-Smoothed Trace-Class And Cyclic Trace Legality

For fixed finite `S`, compact support interval `I`, and compactly supported
half-density test `g`, the theta-smoothed fixed-S support-square calculation
uses one trace ideal. In particular:

```text
P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g) is Hilbert-Schmidt,

theta_S(g)^*
  P_(S,G)(lambda) P_hat_(S,G)(lambda) P_(S,G)(lambda)
  theta_S(g)
  in L^1,

theta_S(g)_can (1/2)u_S^(-1)d^-u_S theta_S(g)_can^*
  in L^1,
```

all endpoint-strip projection defects belong to the same trace ideal with
`Cdef` bounds, and the cyclic trace moves that replace the support square by
the quantized differential are legal term by term.

Proof. The route uses the following five-piece certification:

```text
ThetaSmoothingSchwartzKernel(S,I)
FixedSEulerPhaseTraceClass(S,I)
WeightedProjectionDefectTraceClass(S,I)
CyclicMoveWithSupportProjection(S,I)
TraceClassCyclicSupportSquareIdentity(S,I,lambda)
```

For theta smoothing, earlier route sections identify

```text
theta_S(g)_can = M_S theta_S(g)_sc M_S^(-1),
```

and show that `theta_S(g)_can` has a Schwartz smoothing kernel in the canonical
coordinate, with only fixed-S Euler multiplier loss.

For fixed finite `S`,

```text
u_S^(-1)d^-u_S
  =
u_infty^(-1)d^-u_infty
  +
sum_(p in S_fin) u_p^(-1)d^-u_p.
```

Connes--Consani Proposition 1.5 supplies trace-class membership for the
archimedean summand after localization. Each finite-prime summand is a fixed
smooth phase multiplier or finite logarithmic derivative multiplier on the
fixed graph domain. After left and right theta smoothing, it factors as

```text
theta_S(g)_can M_p theta_S(g)_can^*
  =
(theta_S(g)_can (1+B^2)^(-N))
*
((1+B^2)^N M_p (1+B^2)^N)
*
((1+B^2)^(-N) theta_S(g)_can^*)
```

for fixed large `N`. The outside factors are Hilbert-Schmidt by the Schwartz
kernel estimates, while the middle factor is bounded on the fixed graph
domain. Hence the product is trace-class. Since `S_fin` is finite, the whole
theta-smoothed phase derivative belongs to `L^1`.

Weighted projection defects contain commutators with `M_S` or `M_S^*`. Lemma 1
puts those defects into endpoint-strip trace ideals and gives the `Cdef`
trace-norm bound.

The cyclic move now uses ordinary trace cyclicity on trace-class summands, plus
the same regularized trace convention as Connes--Consani for the source
archimedean summand. Thus

```text
Trace(theta_S(g)^* P_(S,G) P_hat_(S,G) P_(S,G) theta_S(g))

=

Trace(theta_S(g)^*
      [-P(1/2)u_S^(-1)d^-u_S P]
      theta_S(g))

  +
rank/pole/Cdef terms.
```

This proves trace-class and cyclic trace legality for the support-square
calculation below.

The first two trace-class assertions follow from the same smoothing estimate:
`theta_S(g)_can` has a Schwartz kernel after the fixed-S canonical transport,
and left multiplication by the bounded projections `P_(S,G)` and
`P_hat_(S,G)` preserves Hilbert-Schmidt membership. Hence

```text
A_(S,lambda,g)=P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g)
```

is Hilbert-Schmidt, and

```text
A_(S,lambda,g)^* A_(S,lambda,g)
```

is trace-class. This gives an ordinary positive trace before any regularized
source trace is invoked.

Cyclic trace certification used below:

| move | trace-class input | source of legality |
|---|---|---|
| Insert theta smoothing around the phase derivative | `theta_S(g)_can (1/2)u_S^(-1)d^-u_S theta_S(g)_can^* in L^1` | fixed-S phase trace-class factorization in Lemma 2 |
| Move support projections across the theta-smoothed trace | commutators `[P,theta_S(g)]` and `[P_hat,theta_S(g)]` are theta-smoothed trace-class terms | Connes--Consani Proposition 1.5 template plus theta smoothing |
| Replace weighted projection errors by remainders | every `M_S` or `M_S^*` mismatch contains an endpoint-strip factor | Lemma 1 endpoint-strip trace ideal |
| Apply the `Q` trace-remainder extraction | `Q` raises graph order by a fixed amount and preserves endpoint-strip factors | Lemma 1 `Q` stability statement |
| Read the main trace through CCM | the remaining no-defect term is the fixed-S `u_S` quantized differential | source trace read-off audit below |

Numbered cyclic trace chain:

```text
(C1)
PositiveTrace^G_(S,lambda)(g)
  =
Tr(theta_S(g)^* P_(S,G) P_hat_(S,G) P_(S,G) theta_S(g)).

(C2)
P_(S,G) P_hat_(S,G) P_(S,G)
  =
-P_(S,G)(1/2)u_S^(-1)d^-u_S P_(S,G)
  +
NoStripBoundaryTerms
  +
ProjectionOrderDefects.

(C3)
Tr(theta_S(g)^*
   [-P_(S,G)(1/2)u_S^(-1)d^-u_S P_(S,G)]
   theta_S(g))
```

is legal because the theta-smoothed phase derivative is trace-class.

```text
(C4)
Tr(theta_S(g)^* ProjectionOrderDefects theta_S(g))
  =
CdefRemainder_(S,I,lambda)(g)
```

with the `Cdef` bound from Lemma 1.

```text
(C5)
NoStripBoundaryTerms
  =
Rank_(S,I)(g) + PoleJetExtra_(S,I)(g).
```

Equations `(C1)`--`(C5)` are the only cyclic trace moves used in Theorem 1.
All non-trace-class formal terms have been routed into rank, pole, or `Cdef`
ledgers before the CCM read-off.

Trace-cyclicity domain ledger:

| term class | trace convention | reason |
|---|---|---|
| theta-smoothed fixed-S phase derivative | ordinary trace on `L^1` | Lemma 2 factors it into two Hilbert-Schmidt outside terms and one bounded graph-domain middle term |
| endpoint-strip projection defects | ordinary trace on `L^1` | Lemma 1 factors each defect through a finite endpoint strip |
| `Q` applied to endpoint-strip defects | ordinary trace plus finite-rank boundary evaluations | the strip factor remains before every boundary evaluation |
| archimedean no-defect source summand | Connes--Consani regularized trace convention | CC20 Proposition 1.5 supplies the source trace-class calculation and the support-square identity |
| no-strip boundary jets | no cyclic permutation after extraction | these terms are recorded as rank and pole ledgers before CCM read-off |

Thus the proof never uses regularized cyclicity on an unclassified fixed-S
defect. It either proves ordinary trace-class membership first, or it leaves
the term in the source Connes--Consani convention and records the resulting
rank or pole functional.

## Lemma 3. Fixed-S Quantized Support-Square Transport

In the canonical fixed-S model `V_S=M_S U_S`, the theta-smoothed support-square
trace satisfies

```text
Tr(theta_S(g)^*
   P_(S,G) P_hat_(S,G) P_(S,G)
   theta_S(g))

=

Tr(theta_S(g)^*
   [-P_(S,G)(1/2)u_S^(-1)d^-u_S P_(S,G)]
   theta_S(g))

  +
  Rank_(S,I)(g)
  +
  PoleJetExtra_(S,I)(g)
  +
  CdefRemainder_(S,I,lambda)(g),
```

with

```text
|CdefRemainder_(S,I,lambda)(g)|
  <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Proof. The semilocal support reflection lemma and the two-projection
intertwining theorem give

```text
P_S(lambda) = S(P_R(lambda)),
P_hat_S(lambda) = S(P_hat_R(lambda)).
```

After applying `V_S=M_S U_S`, these projections become `P_(S,G)` and
`P_hat_(S,G)`.

The phase pullback identity gives

```text
P_hat_(S,G) = u_S^(-1) I P_(S,G) I u_S
```

up to projection-order defects generated by moving `M_S` and `M_S^*` through
the support and Fourier-support projections.

Connes--Consani prove the archimedean no-defect identity

```text
P P_hat P = -P(1/2)u_infty^(-1)d^-u_infty P.
```

The fixed-S transport applies the same commutator calculation with `u_S`. The
no-strip boundary terms become the rank repair and Tate quotient evaluations,
recorded as `Rank_(S,I)(g)` and `PoleJetExtra_(S,I)(g)`. Each projection-order
defect contains a commutator with `M_S` or `M_S^*`, so Lemma 1 charges it to
`CdefRemainder_(S,I,lambda)(g)`.

Lemma 2 supplies trace-class legality and cyclic trace certification for the
theta-smoothed fixed-S calculation.

## Source Trace Read-Off And Operator Equality Audit

The route must compare the theta-smoothed positive support-square trace with
the Connes/CCM source trace, not only with a formal phase derivative.

Connes' finite-S source operator has the trace-formula shape

```text
Trace(R_Lambda U(h))

with

R_Lambda=P_hat_Lambda P_Lambda.
```

The route operator has the support-square shape

```text
Trace(theta_S(g)^*
      P_(S,G) P_hat_(S,G) P_(S,G)
      theta_S(g)).
```

The bridge has three parts.

First, the test must be converted by the same half-density convention used in
CCM:

```text
F_g = g^* * g.
```

The source trace uses the group test associated with `F_g`, and CCM reads the
main term as `QW_lambda(g,g)`.

Second, the quotient/radical directions in the source trace must match the
route ledgers. The project ledger identifies the rank repair with the zero mode

```text
Rank_(S,I)(g)=C_(S,I)|hat g(0)|^2
```

up to `Cdef` terms, and identifies the two Tate directions with the
`hat g(+i/2)` and `hat g(-i/2)` pole evaluations.

Third, the route must replace the source cutoff trace by the positive
support-square trace only after projection-order defects and trace remainders
have been charged to

```text
rank + killed pole + endpoint-strip Cdef.
```

Lemmas A--C identify the transported support and Fourier-support ranges.
Lemma 1 controls projection-order and endpoint-strip defects. Lemma 2 supplies
trace-class and cyclic trace legality. Therefore the remaining source read-off
in Theorem 1 is the CCM normalization

```text
QW_lambda = W_(0,2) + W_infty - sum_p W_p,
```

with the rank, pole, and `Cdef` ledgers kept outside the main term.

This isolates the source read-off from the rank, pole, and `Cdef` ledgers used
in Theorem 1.

The quotient ledger has no hidden derivative jets. The route records the
no-strip finite-dimensional part as the following three evaluation channels:

```text
zero mode:          hat g(0),
positive Tate jet:  hat g(+i/2),
negative Tate jet:  hat g(-i/2).
```

Every other term produced by the source-to-fixed-S transport contains either a
projection-order commutator, hence belongs to the endpoint-strip `Cdef`
remainder, or remains inside the no-defect CCM trace already read as
`QW_lambda`. Thus `Rank_(S,I)(g)` is proportional to `|hat g(0)|^2`, and
`PoleJetExtra_(S,I)(g)` is supported only on the two Tate evaluations. This is
the exact statement used by Theorem 2.

Source read-off failure modes and current controls:

| failure mode | control in this draft |
|---|---|
| Wrong `h` versus `F_g=g^* * g` conversion | Source read-off keeps `F_g` explicit before invoking CCM `QW(f,g)=Psi(f^* * g)` |
| Source quotient differs from route rank/pole ledger | Rank and pole ledgers are kept outside the CCM main term until triple vanishing kills them |
| Unsymmetrized `R_Lambda U(h)` is replaced by a positive support square too early | Lemmas A--C and Lemma 3 perform the transport before Theorem 1 reads the main term |
| A projection defect contributes to the main Weil term | Lemma 1 charges projection-order defects to endpoint-strip `Cdef` |
| A cyclic move changes the regularized trace | Lemma 2 requires trace-class membership and the Connes--Consani regularized convention before cyclicity |
| Fixed `S` misses a visible prime-power atom | admissibility requires `S` to contain every finite prime visible to `F_g=g^* * g` |
| Positive trace is used before it is trace-class | Lemma 2 proves `P_hat P theta_S(g)` is Hilbert-Schmidt before Theorem 1 takes `Tr(A^*A)` |

## Theorem 1. Fixed-S Source-Normalized Positive Trace

Let `(S,I,lambda,g)` be an admissible tuple in the sense above. Thus

```text
I subset [lambda^(-1),lambda],
supp(g) subset I,
and S contains every finite prime visible to F_g=g^* * g.
```

Define

```text
PositiveTrace^G_(S,lambda)(g)
  =
Tr(theta_S(g)^*
   P_(S,G)(lambda) P_hat_(S,G)(lambda) P_(S,G)(lambda)
   theta_S(g)).
```

Then

```text
PositiveTrace^G_(S,lambda)(g) >= 0,
```

and

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
R_(S,I,lambda)(g),
```

with

```text
|R_(S,I,lambda)(g)|
  <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Proof. Lemma 2 gives

```text
A_(S,lambda,g)
  =
P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g)
  in S_2.
```

Here `S_2` denotes the Hilbert-Schmidt ideal. Therefore

```text
PositiveTrace^G_(S,lambda)(g)
  =
Tr(A_(S,lambda,g)^* A_(S,lambda,g))
```

is an ordinary trace-class positive trace. In the canonical Hilbert structure,
`P_hat_(S,G)(lambda)` is an orthogonal projection, so

```text
theta_S(g)^* P P_hat P theta_S(g)
  =
(P_hat P theta_S(g))^* (P_hat P theta_S(g)).
```

Lemma 3 rewrites the support-square trace as the quantized differential main
term plus rank, pole, and `Cdef` remainders.

CCM gives the source normalization

```text
W_p(F)=(log p) sum_(m>=1) p^(-m/2)(F(p^m)+F(p^(-m))),

QW(f,g)=Psi(f^* * g),

Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F),

W_(0,2)(F)=hat F(i/2)+hat F(-i/2),

W_R=-W_infty.
```

Thus

```text
Psi(F)=W_(0,2)(F)+W_infty(F)-sum_p W_p(F).
```

On `[lambda^(-1),lambda]`, CCM gives

```text
QW_lambda(g,g)
  =
int_R |hat g(t)|^2 (2 partial_t theta(t))/(2 pi) dt
  +
2 Re(hat g(i/2) overline{hat g(-i/2)})
  -
sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>,

<g|T(n)g>
  =
n^(-1/2)((g^* * g)(n)+(g^* * g)(n^(-1))).
```

The `QW_lambda` expression already contains the CCM pole functional through
the displayed `2 Re(hat g(i/2) overline{hat g(-i/2)})` term. The additional
`PoleJetExtra_(S,I)(g)` in Theorem 1 is not a second copy of `W_(0,2)`. It is
the finite-dimensional Tate quotient ledger produced while matching the
source cutoff trace to the fixed-S positive support-square trace. Its support
is the same two evaluations `hat g(+i/2)` and `hat g(-i/2)`, so Theorem 2's
triple vanishing kills both the CCM pole functional and this extra quotient
ledger.

Sign and normalization audit:

| item | source formula | sign used here | reason |
|---|---|---|---|
| archimedean term | `Psi=W_(0,2)-W_R-sum_p W_p` and `W_R=-W_infty` | `+W_infty` | subtracting `W_R` adds `W_infty` |
| finite-prime term | same `Psi` formula plus `W_p` from `bombieriexplicit1bis` | `-sum_p W_p` | CCM puts finite primes in the negative summand of `Psi` |
| restricted finite-prime operator | `quadratsemi` and `quadratsemi1` | `-sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>` | this is the restricted form of `-sum_p W_p` |
| CCM pole functional | `bombtest-0` and `quadratsemi` | inside `QW_lambda` | it appears as the displayed two-evaluation term |
| route quotient pole ledger | fixed-S source-to-positive-trace matching | outside `QW_lambda` | it records quotient directions before triple vanishing, not a second CCM pole term |

Reading the fixed-S quantized differential trace through this formula gives
the displayed identity by the following source-normalized equality chain:

```text
Tr(theta_S(g)^*
   [-P_(S,G)(1/2)u_S^(-1)d^-u_S P_(S,G)]
   theta_S(g))

= Trace_source,no-defect(R_lambda U(F_g))

= QW_lambda(g,g).
```

The first equality is Lemma 3 plus the trace-class/cyclicity ledger of Lemma 2:
the no-defect quantized differential trace is the source cutoff trace after
projection-order defects have been charged to `Cdef` and no-strip quotient
terms have been recorded outside the main term as `Rank` and `PoleJetExtra`.
The second equality is the CCM25 restricted-form read-off for the test
`F_g=g^* * g`.

The admissibility condition on `S` is used exactly here. Since `F_g` vanishes on
all prime powers outside the finite-prime visibility set, the finite-prime sum
read from the fixed-S source trace agrees with the displayed full
`QW_lambda(g,g)` sum on the interval `[lambda^(-1),lambda]`. Without this
condition, Theorem 1 would give only the finite-S restricted trace, not the full
restricted Weil form.

### Referee Expansion Of Theorem 1

The proof of Theorem 1 uses the following local checks.

**Step 0. Admissible window.**  The theorem is used only when
`I subset [lambda^(-1),lambda]`, `supp(g) subset I`, and `S` contains every
finite prime visible to `F_g=g^* * g`. This makes `QW_lambda(g,g)` defined on
the same support window and prevents missing prime-power terms.

**Step 1. Positive trace-class square.**  Lemma 2 proves

```text
P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g) in S_2.
```

Thus the positive trace is an ordinary trace of `A^*A`. In the canonical Hilbert
structure, `P_hat_(S,G)(lambda)` is an orthogonal projection. Therefore

```text
theta_S(g)^* P P_hat P theta_S(g)
  =
(P_hat P theta_S(g))^* (P_hat P theta_S(g)).
```

The trace of this positive trace-class operator is non-negative.

**Step 2. Support-square transport.**  Lemmas A--C identify the fixed-S support
and Fourier-support projections with the transported archimedean support
projections. Lemma 3 then gives

```text
support-square trace
  =
fixed-S quantized differential trace
  +
rank ledger
  +
Tate/pole ledger
  +
Cdef remainder.
```

All commutators with `M_S` and `M_S^*` are taken in the common scattering
coordinate fixed in the definitions. No Weil-form term is read off before this
transport step.

**Step 3. Trace legality.**  Lemma 2 and the trace-cyclicity domain ledger
classify each trace operation:

```text
ordinary L^1 trace:
  theta-smoothed phase derivative and endpoint-strip defects;

regularized source convention:
  archimedean no-defect summand from CC20;

no cyclic move after extraction:
  no-strip rank and pole jets.
```

This blocks the main cyclicity failure mode: a fixed-S defect cannot be moved
by regularized cyclicity unless it has first been put in the ordinary trace
ideal or recorded as a ledger term.

**Step 4. CCM read-off.**  The remaining no-defect quantized differential trace
is read through CCM25, not through a new finite-prime trace computation:

```text
QW(f,g)=Psi(f^* * g),
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F),
W_R=-W_infty.
```

Hence the no-defect main term has the sign pattern

```text
W_(0,2) + W_infty - sum_p W_p.
```

The restricted form is the displayed `QW_lambda` formula from
`mc2arXiv.tex:530-540`.

**Step 5. Ledger collection.**  The terms outside `QW_lambda` are exactly:

```text
Rank_(S,I)(g),
PoleJetExtra_(S,I)(g),
R_(S,I,lambda)(g).
```

The remainder satisfies the `Cdef` bound by Lemma 1. The rank and pole ledgers
are kept outside the CCM main term until Theorem 2 imposes the three vanishing
conditions. This avoids double-counting the CCM pole functional.

The quotient ledger has only the three evaluation channels

```text
hat g(0), hat g(+i/2), hat g(-i/2).
```

No derivative jet or extra finite-S residue is allowed in Theorem 2; any such
term would have to be added to the ledger and killed separately.

## Theorem 2. Triple-Killed Corrected Trace Inequality

For an admissible tuple `(S,I,lambda,g)`, assume

```text
hat g(0)=hat g(+i/2)=hat g(-i/2)=0.
```

Then

```text
QW_lambda(g,g)
  >=
-C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Proof. The rank term is proportional to `|hat g(0)|^2`. The pole ledger uses
only the evaluations at `+i/2` and `-i/2`. The three vanishing conditions kill
both ledgers. Theorem 1 and non-negativity of `PositiveTrace^G_(S,lambda)(g)`
give the inequality.

## Theorem 3. Fixed-Test Exhaustion

Fix a compactly supported test `g` satisfying the triple vanishing conditions.
Choose a compact interval `I` containing `supp(g)`, and choose `A` with

```text
supp(g^* * g) subset exp([-A,A]),
```

and set

```text
S_A={infinity} union {p : log p <= A}.
```

Then

```text
QW(g,g) >= 0.
```

Proof. If a prime-power atom `p^m` meets the support of `g^* * g`, then
`log(p^m)<=A`, hence `log p<=A` and `p in S_A`. Prime-power atoms with
`log(p^m)>A` do not meet the fixed support.

For every sufficiently large `lambda`, the tuple `(S_A,I,lambda,g)` is
admissible. Keep `g`, `I`, and `S_A` fixed and send `lambda -> infinity`. The
graph/prolate exhaustion gives

```text
Cdef_graph_(S_A,I,lambda,J')(g)->0.
```

The endpoint-strip comparison gives

```text
Cdef_(S_A,I,lambda,J)(g)->0.
```

Theorem 2 then yields `liminf_(lambda -> infinity) QW_lambda(g,g) >= 0`.
The restricted CCM form converges to the full Weil quadratic form on this
fixed test for three separate reasons:

```text
finite-prime part:  the support condition makes the prime-power sum stable
                    once lambda is larger than exp(A/2);

pole part:          the pole evaluations are independent of lambda;

archimedean part:   the restricted CCM cutoff exhausts the fixed
                    half-density test in the source Hilbert model.
```

Hence `QW_lambda(g,g) -> QW(g,g)` for this fixed `g`, and `QW(g,g) >= 0`.

## Lemma 4a. The Finite Set Is Disjoint From Zeta Zeros

The finite set

```text
F={0,1/2,1}
```

is disjoint from the non-trivial zero set used in Connes--Consani
Proposition C.1.

Proof. The points `0` and `1` are not non-trivial zeros by definition. For
`1/2`, use the Dirichlet eta relation

```text
eta(s) = (1 - 2^(1-s)) zeta(s).
```

For `0<s<1`, the alternating-series expression for `eta(s)` is positive. At
`s=1/2`, the scalar factor is

```text
1 - sqrt(2),
```

which is nonzero. Therefore

```text
zeta(1/2) = eta(1/2)/(1 - sqrt(2)) != 0.
```

This proves the finite-set side condition for Proposition C.1.

## Theorem 4. Triple-Killed Weil Positivity Implies RH

The finite vanishing set for the Connes--Consani convention is

```text
F={0,1/2,1}.
```

Triple-killed Weil positivity for this finite set implies the Riemann
Hypothesis.

Proof. Connes--Consani use the convention

```text
s = 1/2 - i t.
```

Therefore

```text
t=0     -> s=1/2,
t=+i/2  -> s=1,
t=-i/2  -> s=0.
```

Connes--Consani Proposition C.1 applies to every finite set `F` that contains
`{0,1}` and is disjoint from the non-trivial zero set, with the extra finite
vanishing conditions built into the criterion. The set `{0,1/2,1}` contains
`{0,1}`, and Lemma 4a proves that it is disjoint from the non-trivial zero set.
Proposition C.1 gives RH.

## Route Theorem

Assuming the cited source theorems in CCM24, CCM25, and CC20, the lemmas above
give the Riemann Hypothesis from the fixed-S Connes-Weil positive compression
package.

Proof. Lemma 1 supplies endpoint-strip trace ideal control. Lemma 2 supplies
trace-class and cyclic trace legality. Lemma 3 transports the Connes--Consani
support-square trace to the fixed-S canonical model, using Lemmas A--C to
identify the transported support ranges and the phase multiplier `u_S`.
Theorem 1 reads that positive trace as the CCM-normalized `QW_lambda` form plus
rank, pole, and `Cdef` terms. Theorem 2 kills the rank and pole ledgers under
the three finite vanishing conditions. Theorem 3 removes the `Cdef` term by
fixed-test exhaustion. Theorem 4 applies Connes--Consani Proposition C.1.

## Appendix A. Operator And Domain Conventions

The proof uses four Hilbert-space coordinates. The table records where each
object lives and which source fixes it.

| object | coordinate | source | manuscript use |
|---|---|---|---|
| `L^2(X_S)^(K_S)` | semilocal source space | CCM24 `mainc2m24fine.tex:237-253` | initial support projections |
| `L^2(R_+^*,d^*u)` | multiplicative group coordinate | CCM24 `mainc2m24fine.tex:237-253` | support-window comparison |
| `L^2(R,dm_S)` | canonical fixed-S spectral coordinate | CCM24 `mainc2m24fine.tex:786-804` | positivity and orthogonal projections |
| `L^2([lambda^(-1),lambda],d^*u)` | restricted CCM quadratic-form coordinate | CCM25 `mc2arXiv.tex:530-540` | `QW_lambda` read-off |

The manuscript never identifies these spaces by notation alone. It moves
between them only through `U_S`, `M_S`, `V_S=M_S U_S`, the bounded comparison
map, and the Fourier compatibility stated in Lemmas A--C.

The commutator notation in Lemma 1 uses the common scattering coordinate. After
transporting all terms to this coordinate, `M_S` is a multiplication operator
with bounded inverse on the fixed finite-S graph domain. The symbols
`[P,M_S]`, `[P_hat,M_S]`, `[P,M_S^*]`, and `[P_hat,M_S^*]` are therefore
ordinary commutators in one operator algebra.

## Appendix B. Trace-Class And Cyclicity Ledger

The dangerous trace step is the replacement of the positive support-square
trace by the fixed-S quantized differential trace. The proof uses this ledger.

| trace operation | basis | risk controlled |
|---|---|---|
| `P_hat P theta_S(g)` is Hilbert-Schmidt | Lemma 2; theta-smoothed Schwartz kernel plus bounded projections | defines `PositiveTrace` as `Tr(A^*A)` before positivity is used |
| theta-smoothed phase derivative is trace-class | Lemma 2; CC20 `weil-compo.tex:448-464` | avoids cyclicity before trace-class membership |
| endpoint-strip defects are trace-class | Lemma 1 finite-strip Hilbert-Schmidt factorization | prevents projection defects from entering the main Weil term |
| `Q` applied to strip defects remains controlled | Lemma 1 `Q` stability statement | prevents new no-strip boundary jets |
| archimedean no-defect summand uses source convention | CC20 `weil-compo.tex:378-387`, `448-464` | avoids inventing a new regularized trace |
| no-strip rank/pole jets are extracted, not cycled | Lemma 2 domain ledger | prevents regularized cyclicity on unclassified terms |

Thus every cyclic trace move used by Theorem 1 either takes place in the
ordinary trace ideal or remains inside the Connes--Consani source convention.

## Appendix C. Source Normalization And Sign Audit

Theorem 1 imports the finite-prime and archimedean signs from CCM25.

| term | source | sign in the manuscript |
|---|---|---|
| `W_R=-W_infty` | `mc2arXiv.tex:445-470` | converts `-W_R` into `+W_infty` |
| `Psi=W_(0,2)-W_R-sum_p W_p` | `mc2arXiv.tex:465-467` | fixes `W_(0,2)+W_infty-sum_p W_p` |
| `W_p` | `mc2arXiv.tex:445-447` | finite primes appear with the negative sign in `Psi` |
| `QW_lambda` | `mc2arXiv.tex:530-540` | restricted form contains `-sum Lambda(n)<g|T(n)g>` |
| CCM pole functional | `mc2arXiv.tex:469-470`, `530-540` | appears inside `QW_lambda` |
| route pole ledger | Lemma 3 and Theorem 1 | remains outside `QW_lambda` until Theorem 2 kills it |

The manuscript does not use the false shortcut

```text
Tr_even(u_p^(-1)d u_p)=2 Tr(u_p^(-1)d u_p).
```

Finite-prime coefficients enter only through the CCM Weil quadratic form.

The fixed finite set `S` is not arbitrary when Theorem 1 is read as the full
restricted form `QW_lambda`. The admissibility condition requires `S` to contain
every finite prime visible to `F_g=g^* * g`. If `supp(F_g) subset exp([-A,A])`,
the manuscript takes `S_A={infinity} union {p : log p <= A}` before the
`lambda -> infinity` step. This makes the finite-prime part of the fixed-S
source trace agree with the CCM restricted sum
`sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>` for the fixed test.

## Appendix D. Finite-Set Side Condition

Connes--Consani Proposition C.1 requires a finite set containing `{0,1}` and
disjoint from the non-trivial zero set. The manuscript uses

```text
F={0,1/2,1}.
```

The points `0` and `1` are excluded by the non-trivial-zero convention. Lemma
4a proves `zeta(1/2) != 0` through the Dirichlet eta relation. Therefore this
finite set satisfies the source criterion used in Theorem 4.

## Hostile Audit Ledger

| risk | current answer | evidence |
|---|---|---|
| Hidden fixed-S transport assumption | The draft states it as Lemma 3, supported by Lemmas A--C | `ConnesWeilPositivity.md:135197-135342`, `135733-135798`, `147084-147196` |
| Source-operator equality gap | The draft names the bridge and keeps rank, pole, and Cdef ledgers outside the CCM main term | `ConnesWeilPositivity.md:143025-143153`, `143540-143724`, `143780-143857` |
| False finite-prime even-trace shortcut | The proof reads finite primes through CCM `QW_lambda` | `ConnesWeilPositivity.md:146525-146561` |
| Growing `S` with `lambda` | The proof chooses `S_A` from fixed support before `lambda -> infinity` | `ConnesWeilPositivity.md:146608-146638` |
| Surviving rank or pole terms | Triple vanishing kills `hat g(0)` and `hat g(+-i/2)` ledgers | `ConnesWeilPositivity.md:146587-146600` |
| Cdef ambiguity | The draft separates trace-norm `Cdef`, graph/prolate `Cdef`, and comparison | `ConnesWeilPositivity.md:146790-146919` |
| Proposition C.1 convention mismatch | The draft records `s=1/2-it` and `F={0,1/2,1}` | `ConnesWeilPositivity.md:146630-146665` |
| Trace-class/cyclicity gap | The draft states it as Lemma 2 | `ConnesWeilPositivity.md:143859-144140` |
| Fourier-projection notation mismatch | The draft separates range transport from conjugated projection notation and uses unitarity of `F_S` | Lemma B and Definitions |
| `QW_lambda -> QW` exhaustion gap | The draft splits convergence into finite-prime stabilization, fixed pole evaluations, and source Hilbert cutoff exhaustion | Theorem 3 |
| Fixed `S` cannot see full finite-prime sum | Theorem 1 now uses admissible tuples; `S_A` is chosen from `supp(F_g)` before `lambda -> infinity` | Admissible Windows; Appendix C |
| Positive trace used before trace-class proof | Lemma 2 now states `P_hat P theta_S(g)` is Hilbert-Schmidt, so `PositiveTrace=Tr(A^*A)` is defined first | Lemma 2; Appendix B |
| Commutators between different Hilbert spaces | Definitions now put all `[P,M_S]` terms in one common scattering coordinate | Definitions; Appendix A |
| Rank/pole ledger hides derivative jets | Source read-off ledger lists exactly `hat g(0)`, `hat g(+i/2)`, and `hat g(-i/2)` as no-strip channels | Source Trace Read-Off; Theorem 1 expansion |

Current hostile-audit verdict:

```text
No named route-level mathematical gap remains in this draft after adding the
admissible-window, positive-trace-class, common-coordinate, and quotient-ledger
conditions to Theorem 1.

External checks required for public circulation are source-citation formatting,
independent rereading of displayed trace identities, and editorial conversion
from internal ledger style to journal style. Those are not new proof ingredients
visible from the route ledger.
```

## Completion Audit

This audit treats completion as a set of gates. A gate passes only when the
current draft contains the object and points to the evidence used by the proof.

| gate | evidence in draft | result |
|---|---|---|
| Manuscript has a declared status and boundary | status line; opening paragraph; final public-certification note | pass as internal manuscript draft, not Clay/journal/Lean certification |
| Public source targets are named | stable citation table; reference table with arXiv URLs | pass |
| Source formula dependencies are mapped | `Formula dependency map` | pass |
| Source-line audit is present | `Source-line audit for v0.1` | pass |
| Proof order is explicit | `Proof Spine` | pass |
| Definitions fix operators and ledgers | `Definitions` block | pass |
| Fixed-S support and Fourier transport are stated | Lemmas A, B, C | pass |
| Endpoint-strip defects are trace-ideal controlled | Lemma 1 | pass |
| Trace-class and cyclic trace legality is classified | Lemma 2 plus trace-cyclicity domain ledger | pass |
| PositiveTrace is defined before non-negativity is used | Lemma 2 Hilbert-Schmidt assertion plus Theorem 1 Step 1 | pass |
| Fixed-S support-square transport is stated | Lemma 3 | pass |
| Source trace read-off avoids premature replacement | `Source Trace Read-Off And Operator Equality Audit` | pass |
| Theorem 1 has admissible support and finite-prime conditions | `Admissible Windows For Theorem 1` | pass |
| Positive trace gives the restricted CCM form | Theorem 1 | pass |
| Theorem 1 can be checked stepwise | `Referee Expansion Of Theorem 1` | pass |
| Sign and normalization do not hide a finite-prime shortcut | Theorem 1 sign and normalization audit | pass |
| Fixed-S/full-QW prime visibility is controlled | Admissible window and Appendix C | pass |
| Rank and pole ledgers vanish under the chosen test class | Theorem 2 | pass |
| Restricted forms converge to the full Weil form for fixed tests | Theorem 3 | pass |
| Finite set for Proposition C.1 is admissible | Lemma 4a | pass |
| Connes--Consani RH exit is applied with the correct convention | Theorem 4 | pass |
| Route theorem closes the implication chain | Route Theorem | pass |
| Audit material is accessible to referees | Appendices A--D | pass |
| Known hostile risks are named and answered | Hostile Audit Ledger | pass |
| Text hygiene was checked | Final Verification Status plus external command checks recorded in memory | pass |

Current completion verdict:

```text
The draft is complete as a v0.1 referee-readable, source-conditional
manuscript.
No obvious route-level weak point remains visible in the current manuscript.
The result is not a public proof certificate: independent referee review,
source-line rereading, journal acceptance, Clay acceptance, and Lean
formalization remain outside this artifact.
```

## Final Verification Status

| gate | status | evidence |
|---|---|---|
| Body prose avoids local extraction paths | pass | no local extraction paths remain in the draft body |
| Stable source targets are listed | pass | `Stable citation targets for a public draft` table |
| Source reread results are recorded | pass | `Source reread certificate` table |
| Source-line audit is recorded | pass | `Source-line audit for v0.1` table |
| Cyclic trace moves are numbered | pass | `(C1)`--`(C5)` in Lemma 2 |
| Eta side condition is stated inside the proof | pass | Lemma 4a |
| Hostile audit found no named route-level mathematical gap | pass | Hostile Audit Ledger and verdict |
| Referee appendices are included | pass | Appendices A--D |
| Completion gates are audited | pass | Completion Audit |
| External public certification | not claimed | Clay-level, journal-level, and Lean-certified claims are outside this draft |

External public certification requires independent referee review, Lean
formalization, or journal/Clay acceptance. This draft does not assert any of
those statuses.

## Appendix E. Lean Formalization Status

The Lean formalization now has a segmented phase-1 target:

```text
ConnesWeilRH
```

The target separates source theorem interfaces from the route composition:

```text
ConnesWeilRH.Source.CCM24
ConnesWeilRH.Source.CCM25
ConnesWeilRH.Source.CC20
  |
  v
ConnesWeilRH.Route.*
  |
  v
Mathlib _root_.RiemannHypothesis
```

The current Lean route skeleton builds with:

```text
lake build ConnesWeilRH
```

The current axiom audit for
`ConnesWeilRH.Route.final_connes_weil_rh` records only Lean/Mathlib foundation
axioms:

```text
[propext, Classical.choice, Quot.sound]
```

The source-interface names and source-line obligations are recorded in:

```text
docs/audits/lean-source-interface-map.md
```

The CCM24 semilocal-model, support-transport, bounded-comparison, and
Sonin-comparison obligations now have symbolic Lean statements over
`ConnesWeilRH.SemilocalModelSymbols`. The CCM25 `QW`, `QW_lambda`,
finite-prime, and pole obligations now have symbolic Lean statements over
`ConnesWeilRH.WeilFormSymbols`. The CC20 archimedean trace, trace-class,
Mellin, and sign obligations now have symbolic statements over
`ConnesWeilRH.ArchimedeanTraceSymbols`. The CC20 finite-vanishing RH exit is
represented by `ConnesWeilRH.FiniteVanishingCriterionPackage`, and the final
route theorem uses `inputs.cc20.finiteVanishingRhExit.criterion` directly.

A scan of `ConnesWeilRH/Source` now finds no remaining `statement := True`
source obligations. This removes the buildable placeholder layer, but it does
not discharge the source-paper analysis.

The final route certificate now carries
`ConnesWeilRH.Route.SourceBackedFixedSTest`. The route theorem derives
`AdmissibleForTheorem1` through
`ConnesWeilRH.Route.admissible_for_theorem1_of_source_backed` instead of taking
bare route-local admissibility as a certificate field. This records the first
Lean bridge from the route-level fixed-`S` test back to the CCM24 semilocal
interface.

Finite-prime visibility now passes through the CCM25 finite-prime normalization
interface. `finite_prime_visibility_statement_of_source_backed` derives
`ConnesWeilRH.WeilFormSymbols.FinitePrimeVisibilityStatement` from
`inputs.ccm25.finitePrimeNormalization`, and
`finite_primes_visible_of_source_backed` uses the explicit bridge on
`SourceBackedFixedSTest` to obtain the route predicate
`test.finitePrimesVisible`.

Full Weil positivity now passes through
`ConnesWeilRH.Route.SourceBackedFullPositivity`. The bridge uses the CC20
trace-class template and archimedean trace-square statement, and it uses a
CCM25 Weil-form read-off bridge fed by `inputs.ccm25.qwDefinition`,
`inputs.ccm25.qwLambdaFormula`, and `inputs.ccm25.poleNormalization`. The final
route theorem obtains `FullWeilPositivity` through
`ConnesWeilRH.Route.full_weil_positivity_of_source_backed`.

The rank, pole, and Cdef ledgers now pass through
`ConnesWeilRH.Route.SourceBackedLedgers`. The route obtains `LedgersCleared`
through `ConnesWeilRH.Route.ledgers_cleared_of_source_backed` instead of taking
a direct final-certificate proof of cleared ledgers.

Triple vanishing now passes through
`ConnesWeilRH.TripleVanishingSymbols` over the finite type
`ConnesWeilRH.CriticalVanishingPoint`, whose constructors represent `0`,
`1/2`, and `1`. The route obtains `test.tripleVanishing` through
`ConnesWeilRH.Route.triple_vanishing_of_source_backed`.

The fixed-S trace read-off bridge is now split by
`ConnesWeilRH.Route.SourceTraceReadOffData` into trace legality, no-defect
source read-off, Weil-form identification, and positive-trace nonnegativity
stages. `ConnesWeilRH.Route.FixedSPositiveTraceReadOff` is no longer an alias
for the admissibility predicate. The source-backed positivity path supplies the
CC20 trace-square result and CCM25 Weil-form read-off result before constructing
that independent fixed-S positive trace package.

The Lean route now places the CC20 archimedean test object and its
Hilbert-Schmidt gate inside `SourceTraceReadOffData`. The Theorem 1 segment
derives trace-class/cyclicity legality and the trace-square read-off from the
CC20 interface before it builds the fixed-S positive trace package.

This is not yet a full Lean proof of RH. The formalization remains
source-conditional until the CCM24, CCM25, and CC20 interfaces are discharged by
formal proofs or replaced by accepted imported theorems.
