# Connes-Weil RH Proof

Version 0.2.0.

This repository records a source-conditional mathematical route from the
Connes--Consani--Moscovici and Connes--Consani source inputs to Mathlib's
canonical Riemann Hypothesis statement.

The theorem proved by the route has the following shape:

$$
\Bigl(
  H_{\mathrm{CCM24}},
  H_{\mathrm{CCM25}},
  H_{\mathrm{CC20}},
  H_{\mathrm{trace}},
  H_{\mathrm{defect}},
  H_{\mathrm{exhaust}},
  H_{\mathrm{sign}},
  H_{\mathrm{RH}}
\Bigr)
\Longrightarrow
\mathrm{RH}.
$$

The repository does not claim journal acceptance, Clay acceptance, independent
referee certification, or a no-argument Lean proof of RH. The Lean theorem in
the active route remains certificate-conditional:

```lean
structure RouteCertificate (inputs : RouteInputs) where
  sourceBackedTest : SourceBackedFixedSTest inputs
  ledgers : RouteLedgers
  bridge : RouteBridgeCertificate inputs sourceBackedTest ledgers

theorem final_connes_weil_rh
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    _root_.RiemannHypothesis := by
  ...
```

Local evidence:

| claim | evidence |
|---|---|
| Mathlib RH is the target, not a project-local replacement | `ConnesWeilRH/Basic.lean:14-23` |
| the route consumes a certificate | `ConnesWeilRH/Route/RouteTheorem.lean:24-28` |
| the conditional Lean theorem concludes Mathlib RH | `ConnesWeilRH/Route/RouteTheorem.lean:2599-2606` |
| the no-argument theorem is still development work | `ConnesWeilRH/Dev/UnconditionalSkeleton.lean` |

## Source References

| label | source | role |
|---|---|---|
| CCM24 | Alain Connes, Caterina Consani, Henri Moscovici, "Zeta Zeros and Prolate Wave Operators: Semilocal Adelic Operators", arXiv:2310.18423, https://arxiv.org/abs/2310.18423 | fixed-$S$ semilocal model, support transport, Fourier compatibility, bounded comparison, Sonin comparison |
| CCM25 | Alain Connes, Caterina Consani, Henri Moscovici, "Zeta Spectral Triples", arXiv:2511.22755, https://arxiv.org/abs/2511.22755 | $QW$, $QW_\lambda$, pole normalization, finite-prime normalization |
| CC20 | Alain Connes, Caterina Consani, "Weil positivity and Trace formula: the archimedean place", arXiv:2006.13771, https://arxiv.org/abs/2006.13771 | archimedean support-square trace, trace-class legality, Mellin convention, finite-vanishing RH criterion |

The source-line audit used by the manuscript records these checked source
locations:

| imported item | arXiv source file and lines | use |
|---|---|---|
| CCM24 canonical semilocal transform | `mainc2m24fine.tex:237-253` | defines $U_S$, $M_S$, $V_S=M_SU_S$, and the grading reflection |
| CCM24 support transport | `mainc2m24fine.tex:761-771` | transports support through the semilocal periodization map |
| CCM24 fixed-$S$ cyclic pair | `mainc2m24fine.tex:786-804` | supplies the canonical Hilbert model |
| CCM24 bounded comparison | `mainc2m24fine.tex:806-823` | supplies a bounded comparison map and bounded inverse |
| CCM24 Fourier compatibility | `mainc2m24fine.tex:983-1003` | transports the Fourier-side support projection |
| CCM24 Sonin comparison | `mainc2m24fine.tex:1050-1060` | supports the fixed-window exhaustion comparison |
| CCM25 finite-prime and pole terms | `mc2arXiv.tex:445-470` | fixes $W_p$, $W_{\mathbb R}$, $QW$, $\Psi$, and $W_{(0,2)}$ |
| CCM25 restricted quadratic form | `mc2arXiv.tex:530-540` | supplies $QW_\lambda$ and the prime-power pairing |
| CC20 support-square trace | `weil-compo.tex:378-387` | supplies the archimedean trace formula |
| CC20 trace-class verification | `weil-compo.tex:448-464` | supplies the trace-class argument |
| CC20 Mellin convention | `weil-compo.tex:2014-2030` | fixes the half-density convention |
| CC20 quantized trace ideal | `weil-compo.tex:2106-2121` | supplies the trace-ideal template |
| CC20 sign normalizations | `weil-compo.tex:2131-2165` | fixes $u_\infty$, $qdu$, and the archimedean sign |
| CC20 finite-vanishing criterion | `weil-compo.tex:2072-2085` | supplies the final RH exit |

Repository evidence for this table:

| file | content |
|---|---|
| `docs/manuscripts/connes-weil-rh-proof-draft.md` | route-paper proof draft, source-line audit, theorem order |
| `docs/audits/source-reread-v0.2.md` | source reread audit for Lean boundary declarations |
| `docs/audits/unconditional-rh-gap-ledger.md` | current gap ledger for the no-argument theorem |
| `docs/audits/accepted-source-certification-status-board.md` | accepted-source review state |

## The Conditional Theorem

Let $g$ be a compactly supported half-density test on $\mathbb R_+^\ast$ and
let

$$
F_g = g^\ast \ast g.
$$

Choose a finite set of places $S$ containing $\infty$. For a fixed support
bound $A$ with

$$
\operatorname{supp}(F_g)\subset \exp([-A,A]),
$$

the route takes

$$
S_A=\{\infty\}\cup\{p:\log p\le A\}.
$$

This choice prevents a fixed-$S$ trace from omitting a finite-prime atom that
can appear in $F_g$.

Let $\lambda>1$ and choose a support window

$$
I\subset [\lambda^{-1},\lambda],
\qquad
\operatorname{supp}(g)\subset I.
$$

Assume the source inputs and project lemmas listed below.

1. CCM24 supplies the canonical fixed-$S$ Hilbert model

$$
V_S=M_SU_S
$$

and the bounded comparison and Fourier-transport data needed to move support
and Fourier support through the same fixed-$S$ model.

2. CC20 supplies the archimedean support-square trace template, trace-class
legality, Mellin convention, and finite-vanishing criterion.

3. CCM25 supplies the global Weil form $QW$, the restricted form
$QW_\lambda$, the pole functional, and the finite-prime normalization.

4. The project defect lemmas split the fixed-$S$ trace read-off into a main
restricted Weil term, rank and pole ledgers, and an endpoint-strip defect.

5. The fixed-test exhaustion lemma sends the endpoint-strip defect to zero
after $g$, $S_A$, $I$, and the graph order are fixed.

6. The final sign bridge identifies the full Weil form with the CC20 Weil sum
with the correct sign.

Then the route proves Mathlib's statement:

$$
{}_{{\rm Mathlib}}\mathrm{RiemannHypothesis}.
$$

In Lean, this conclusion appears as

```lean
_root_.RiemannHypothesis
```

rather than a local synonym.

## Proof

### 1. Move every object into the fixed-$S$ canonical model

CCM24 gives a canonical semilocal transform

$$
V_S=M_SU_S.
$$

Write $H_S$ for the corresponding Hilbert space. Let $P_S(\lambda)$ be the
support projection in the source model and define the canonical support
projection

$$
P_{S,G}(\lambda)=V_SP_S(\lambda)V_S^{-1}.
$$

Let $F_S$ denote the fixed-$S$ Fourier symmetry. The Fourier-side support
projection is

$$
\widehat P_{S,G}(\lambda)
  =F_S^{-1}P_{S,G}(\lambda)F_S.
$$

The CCM24 comparison map identifies the semilocal support range with the
archimedean support range:

$$
\operatorname{Ran}P_S(\lambda)
  =
S\operatorname{Ran}P_{\mathbb R}(\lambda).
$$

The CCM24 Fourier compatibility gives

$$
F_SS=SF_{\mathbb R},
$$

and therefore

$$
\operatorname{Ran}\widehat P_S(\lambda)
  =
S\operatorname{Ran}\widehat P_{\mathbb R}(\lambda).
$$

This step fixes the object discipline. The same $g$, $F_g$, $S$, $I$, and
$\lambda$ pass through the trace read-off, ledger clearing, exhaustion,
restricted-to-full bridge, final sign bridge, and RH exit.

### 2. Form the positive trace before reading it as a Weil expression

Let $\theta_S(g)$ be the bounded test operator attached to $g$ in the fixed-$S$
model. Define

$$
A_{S,\lambda}(g)=\widehat P_{S,G}(\lambda)P_{S,G}(\lambda)\theta_S(g).
$$

The CC20 trace-class input and the project trace-class wrappers prove that
$A_{S,\lambda}(g)$ is Hilbert--Schmidt. Hence

$$
\operatorname{Pos}_{S,\lambda}(g)
  :=
\operatorname{Tr}\bigl(A_{S,\lambda}(g)^\ast A_{S,\lambda}(g)\bigr)
\ge 0.
$$

The proof uses positivity only after this trace is defined. That prevents the
route from using a formal nonnegative expression before the operator belongs
to the trace ideal.

### 3. Read the positive trace as a restricted Weil scalar plus ledgers

The source read-off has the form

$$
\operatorname{Pos}_{S,\lambda}(g)
  =
QW_\lambda(g,g)
  +
\operatorname{Rank}_{S,I}(g)
  +
\operatorname{PoleJetExtra}_{S,I}(g)
  +
R_{S,I,\lambda,J}(g).
$$

The terms have separate jobs.

| term | meaning |
|---|---|
| $QW_\lambda(g,g)$ | the CCM25 restricted Weil scalar for the same test $g$ |
| $\operatorname{Rank}_{S,I}(g)$ | the zero-mode ledger |
| $\operatorname{PoleJetExtra}_{S,I}(g)$ | the two pole-evaluation ledgers |
| $R_{S,I,\lambda,J}(g)$ | endpoint-strip and projection-defect remainder |

The CCM25 restricted scalar uses the same square

$$
F_g=g^\ast\ast g
$$

and the same prime-power pairing

$$
\langle g,T(n)g\rangle
  =
n^{-1/2}\bigl(F_g(n)+F_g(n^{-1})\bigr).
$$

The finite-prime sign comes from the CCM25 formula for $QW_\lambda$. The route
does not introduce a separate finite-prime sign convention.

### 4. Kill the rank and pole ledgers by triple vanishing

Restrict to tests satisfying

$$
\widehat g(0)=\widehat g(i/2)=\widehat g(-i/2)=0.
$$

The rank ledger is supported on $\widehat g(0)$, and the pole ledger is
supported on $\widehat g(i/2)$ and $\widehat g(-i/2)$. Thus

$$
\operatorname{Rank}_{S,I}(g)=0,
\qquad
\operatorname{PoleJetExtra}_{S,I}(g)=0.
$$

The read-off becomes

$$
\operatorname{Pos}_{S,\lambda}(g)
  =
QW_\lambda(g,g)
  +
R_{S,I,\lambda,J}(g).
$$

Since $\operatorname{Pos}_{S,\lambda}(g)\ge 0$,

$$
QW_\lambda(g,g)\ge -R_{S,I,\lambda,J}(g).
$$

### 5. Bound and remove the endpoint-strip defect

The defect package proves

$$
\left|R_{S,I,\lambda,J}(g)\right|
  \le
C_{S,I,J}(g)\,Cdef_{S,I,\lambda,J}(g).
$$

Here $Cdef$ is a trace-norm sum over endpoint-strip normal-form terms:

$$
Cdef_{S,I,\lambda,J}(g)
  =
\sum_{\alpha\in\mathcal R_{S,I,\lambda,J}}
\left\|
\theta(D^rg)X_0M_bT_aX_1\theta(D^sg)^\ast
\right\|_1
  +
\sum_{\beta\in Q\mathcal R_{S,I,\lambda,J}}
\left|\operatorname{BoundaryStripTrace}_\beta(g)\right|.
$$

Each summand contains an endpoint-strip factor. The fixed-test graph/prolate
exhaustion package gives

$$
Cdef_{S_A,I,\lambda,J}(g)\longrightarrow 0
\qquad (\lambda\to\infty)
$$

after $g$, $S_A$, $I$, and $J$ are fixed. Therefore

$$
\liminf_{\lambda\to\infty} QW_\lambda(g,g)\ge 0.
$$

### 6. Pass from the restricted Weil form to the full Weil form

The restricted-to-full bridge proves that, for this fixed test and the fixed
finite-prime visibility set $S_A$,

$$
QW_\lambda(g,g)\longrightarrow QW(g,g).
$$

Combining this with the previous inequality gives

$$
QW(g,g)\ge 0.
$$

The bridge is restricted to fixed-test support, prime-power atom stabilization,
finite-prime support equality, archimedean and pole stability, and the
endpoint-strip exhaustion package. It does not use finite-operator spectral
convergence, determinant convergence, numerical eigenvalue convergence, or an
even-sector minimum-eigenvector assumption.

### 7. Convert $QW$ positivity into the CC20 Weil inequality

The final sign bridge proves

$$
QW(g,g)
  =
-\sum_v W_v(F_g).
$$

Therefore

$$
QW(g,g)\ge 0
\quad\Longrightarrow\quad
\sum_v W_v(F_g)\le 0.
$$

This is the inequality direction used by the CC20 finite-vanishing criterion.
The sign bridge must use the same $F_g=g^\ast\ast g$ that entered the CCM25
read-off.

### 8. Apply the CC20 finite-vanishing criterion

CC20 applies the Weil inequality to tests whose Mellin transform vanishes on a
finite set containing $0$ and $1$ and disjoint from the non-trivial zero set.
The route uses

$$
F=\{0,1/2,1\}.
$$

The triple vanishing condition matches this set under the CC20 convention

$$
s=1/2-it.
$$

Thus

$$
t=0\mapsto s=1/2,\qquad
t=i/2\mapsto s=1,\qquad
t=-i/2\mapsto s=0.
$$

The side condition that $1/2$ is not a non-trivial zero is handled in the
manuscript through the eta-function argument recorded in the CC20 exit proof
package. The points $0$ and $1$ are excluded by the source non-trivial-zero
convention.

The CC20 criterion then yields the source RH statement. The RH-definition
bridge identifies the source zeta function, zero predicate, pole exclusions,
trivial-zero exclusions, and critical-line condition with Mathlib's
`_root_.RiemannHypothesis`.

Hence

$$
{}_{{\rm Mathlib}}\mathrm{RiemannHypothesis}.
$$

## Dependency Graph

```text
fixed test g
  |
  v
F_g = g^* * g
  |
  v
choose S_A, I, lambda with fixed-prime visibility
  |
  v
CCM24 fixed-S canonical model and support transport
  |
  v
positive trace Tr(A^* A) >= 0
  |
  v
trace read-off:
  Pos = QW_lambda + Rank + PoleJetExtra + R
  |
  v
triple vanishing kills Rank and PoleJetExtra
  |
  v
endpoint-strip bound and fixed-test exhaustion kill R
  |
  v
QW_lambda(g,g) -> QW(g,g)
  |
  v
QW(g,g) >= 0
  |
  v
QW(g,g) = - sum_v W_v(F_g)
  |
  v
sum_v W_v(F_g) <= 0
  |
  v
CC20 finite-vanishing criterion
  |
  v
Mathlib RiemannHypothesis
```

## Falsification Checks

A reviewer should reject the route if one of these checks fails.

| check | failure mode | first repository file to inspect |
|---|---|---|
| trace scale | the positive trace contains a $\lambda$-growing bulk term outside $QW_\lambda$, rank, pole, and $Cdef$ | `docs/proofs/trace-scale-compatibility-proof-package.md` |
| fixed-$S$ support transport | the fixed-$S$ projection transport creates a fourth no-strip defect | `docs/audits/semilocal-fourth-defect-ledger.md` |
| finite-prime visibility | $S_A$ omits a prime-power atom visible to $F_g$ | `docs/audits/s-local-global-quantifier-audit.md` |
| pole separation | the CCM25 pole term is double-counted with the route pole ledger | `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` |
| endpoint-strip exhaustion | $Cdef_{S_A,I,\lambda,J}(g)$ does not tend to zero for fixed $g$ | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md` |
| restricted-to-full bridge | $QW_\lambda\to QW$ imports a forbidden spectral or numerical convergence assumption | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` |
| final sign | $QW(g,g)$ has the wrong sign relative to $\sum_v W_v(F_g)$ | `docs/proofs/final-sign-bridge-proof-package.md` |
| RH definition | the source zero predicate does not match Mathlib's zeta-zero predicate | `docs/proofs/rh-definition-bridge-proof-package.md` |

## Lean Status

The active Lean root is

```text
ConnesWeilRH.lean
```

It imports the source and route modules. It does not import the development
file

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
```

The route theorem has this certified conditional shape:

$$
\mathrm{RouteCertificate}(\mathrm{inputs})
\Longrightarrow
{}_{{\rm Mathlib}}\mathrm{RiemannHypothesis}.
$$

The remaining formalization work is to replace source-facing certificate fields
and development skeleton assumptions by Lean proofs or accepted theorem imports
for the analytic rows.

Useful checks:

```text
lake build ConnesWeilRH
rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean" -g "!ConnesWeilRH/Dev/**"
#print axioms ConnesWeilRH.Route.final_connes_weil_rh
```

Current boundary:

| artifact | status |
|---|---|
| mathematical route manuscript | source-conditional, referee-readable |
| Lean route composition | certificate-conditional |
| accepted-source certification | open |
| no-argument Lean proof of RH | open |
| public unconditional RH proof | not claimed |

## Repository Layout

```text
ConnesWeilRH/
  Lean source and route scaffold.

docs/manuscripts/
  Referee-facing manuscript drafts.

docs/proofs/
  Project proof packages and theorem contracts.

docs/audits/
  Source rereads, gap ledgers, accepted-source packets, and falsification tests.

formalization/
  Lean readiness and interface planning notes.
```

## Version 0.2.0 Scope

Version 0.2.0 makes the GitHub README a mathematical proof page. It states the
conditional theorem, expands the proof chain in LaTeX, names the exact source
inputs, and keeps the open certification boundary visible.

The release does not change the proof status from conditional to
unconditional.
