# Connes-Weil RH Proof

Version 0.2.5-dev.

This repository records a source-conditional Connes-Weil route to Mathlib's
canonical Riemann Hypothesis statement.

The public status, as of 2026-07-13, is conditional:

```text
CCM24 source rows
+ CCM25 source rows
+ CC20 source rows
+ route trace / defect / exhaustion / sign bridges
--------------------------------------------------
Mathlib _root_.RiemannHypothesis
```

The repository does not claim journal acceptance, Clay acceptance, independent
referee certification, or an unconditional no-argument Lean proof of RH. The
conditional route still has this shape:

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

The latest Lean milestone is below the final RH-producing layer. The project
now has an axiom-clean operator bridge for the selected finite-prime crossing:

```text
compact A†B crossing traces
  -> global convolution crossing and its adjoint
  -> Euler-log weighted prime-power trace atoms
  -> finite-S operator sum on one global L2 space
  -> compact + self-adjoint + trace read-off
```

This is a genuine same-object finite-prime trace package. It is not yet a
positive semilocal owner and it does not prove the sign of the remaining
post-Q terms.

Local evidence:

| claim | evidence |
|---|---|
| Mathlib RH is the target, not a project-local replacement | ConnesWeilRH/Basic.lean:14-23 |
| the route consumes a certificate | ConnesWeilRH/Route/RouteTheorem.lean:24-28 |
| the conditional Lean theorem concludes Mathlib RH | ConnesWeilRH/Route/RouteTheorem.lean:2599-2606 |
| the no-argument theorem remains development work | ConnesWeilRH/Dev/UnconditionalSkeleton.lean |
| compact crossing trace reaches the whole-line convolution crossing | ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean:2711 |
| finite-S Euler-log crossing sum is self-adjoint, compact, and trace-readable | ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean:3057-3135 |
| the ordinary CC20 window has a global compact self-adjoint owner | ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean:1629-1652 |
| selected prime translations give the finite-prime quadratic read-off | ConnesWeilRH/Source/CCM25Concrete/SelectedPrimeTranslationQuadratic.lean:78-115 |

Current no-argument frontier, as of 2026-07-13:

```text
normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreFromTheorems
  -> normalizedSelectedNoOffLineSourceZeroCoreFromTheorems
  -> normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems
  -> normalizedSelectedRouteBackedSourceRHFromTheorems
  -> unconditional_rh_skeleton
```

The active blocker has moved beyond the compact operator and finite-prime
trace layers. The missing producer is a genuine finite-S positive semilocal
operator whose single-crossing component is the proved global finite-S sum,
together with a same-domain compact self-adjoint post-Q remainder and its sign.
The published CCM24 and q-series constructions do not supply that trace
identity. The later spectral-triple and finite Guinand--Weil papers also do not
close this sign/positivity gap; they provide convergence or finite-matrix data,
not the required uniform positive owner.

Until that producer and the final exit are proved, `unconditional_rh_skeleton`
is development infrastructure rather than an accepted unconditional proof.

## Current Research Status

The current research conclusion is negative but useful: the recent literature
does not provide the missing finite-S positive owner. The active mathematical
bottom is therefore explicit rather than hidden behind a wrapper:

```text
proved whole-line K_S
  |
  +--> need a genuine finite-S positive owner
  |      whose single-crossing term is exactly K_S
  |
  +--> need same-domain post-Q remainder control
         with the required sign
              |
              v
       restricted-test sufficiency or
       non-circular source-zero exclusion
              |
              v
       SourceRH -> Mathlib _root_.RiemannHypothesis
```

Primary references checked for this status:

| source | current conclusion |
|---|---|
| CCM24, arXiv:2310.18423v2, https://arxiv.org/abs/2310.18423 | establishes the semilocal/Sonin transport framework, but leaves semilocal positivity as further work |
| q-series/Jacobi paper, arXiv:2403.01247, https://arxiv.org/abs/2403.01247 | supplies moment/Jacobi expansions and integrality, not the required positive trace identity |
| Zeta Spectral Triples, arXiv:2511.22755, https://arxiv.org/abs/2511.22755 | studies self-adjoint approximants, but leaves essential prolate/ground-state steps open |
| finite Guinand--Weil dictionary, arXiv:2607.02828, https://arxiv.org/abs/2607.02828 | supplies finite matrices and tail order, not a uniform sign theorem |

The latest Lean declarations are audited by import-facing files under
`ConnesWeilRH/Dev/`. Their `#check`, `#print`, and `#print axioms` commands make
the declaration types and axiom dependencies reviewable. Axiom-clean local
proofs must still be distinguished from unconditional theorems: ordinary
premises and development-only source fields can remain even when no extra
axiom is used.

## Source References

| label | source | role |
|---|---|---|
| CCM24 | Alain Connes, Caterina Consani, Henri Moscovici, "Zeta Zeros and Prolate Wave Operators: Semilocal Adelic Operators", arXiv:2310.18423, https://arxiv.org/abs/2310.18423 | fixed-S semilocal model, support transport, Fourier compatibility, bounded comparison, Sonin comparison |
| CCM25 | Alain Connes, Caterina Consani, Henri Moscovici, "Zeta Spectral Triples", arXiv:2511.22755, https://arxiv.org/abs/2511.22755 | QW, QW_lambda, pole normalization, finite-prime normalization |
| CC20 | Alain Connes, Caterina Consani, "Weil positivity and Trace formula: the archimedean place", arXiv:2006.13771, https://arxiv.org/abs/2006.13771 | archimedean support-square trace, trace-class legality, Mellin convention, finite-vanishing RH criterion |

Source-line audit:

| imported item | arXiv source file and lines | use |
|---|---|---|
| CCM24 canonical semilocal transform | mainc2m24fine.tex:237-253 | defines U_S, M_S, V_S = M_S U_S, and the grading reflection |
| CCM24 support transport | mainc2m24fine.tex:761-771 | transports support through the semilocal periodization map |
| CCM24 fixed-S cyclic pair | mainc2m24fine.tex:786-804 | supplies the canonical Hilbert model |
| CCM24 bounded comparison | mainc2m24fine.tex:806-823 | supplies a bounded comparison map and bounded inverse |
| CCM24 Fourier compatibility | mainc2m24fine.tex:983-1003 | transports the Fourier-side support projection |
| CCM24 Sonin comparison | mainc2m24fine.tex:1050-1060 | supports fixed-window exhaustion |
| CCM25 finite-prime and pole terms | mc2arXiv.tex:445-470 | fixes W_p, W_R, QW, Psi, and W_(0,2) |
| CCM25 restricted quadratic form | mc2arXiv.tex:530-540 | supplies QW_lambda and the prime-power pairing |
| CC20 support-square trace | weil-compo.tex:378-387 | supplies the archimedean trace formula |
| CC20 trace-class verification | weil-compo.tex:448-464 | supplies the trace-class argument |
| CC20 Mellin convention | weil-compo.tex:2014-2030 | fixes the half-density convention |
| CC20 quantized trace ideal | weil-compo.tex:2106-2121 | supplies the trace-ideal template |
| CC20 sign normalizations | weil-compo.tex:2131-2165 | fixes u_infty, qdu, and the archimedean sign |
| CC20 finite-vanishing criterion | weil-compo.tex:2072-2085 | supplies the final RH exit |

Repository evidence:

| file | content |
|---|---|
| docs/manuscripts/connes-weil-rh-proof-draft.md | route-paper proof draft, source-line audit, theorem order |
| docs/audits/source-reread-v0.2.md | source reread audit for Lean boundary declarations |
| docs/audits/unconditional-rh-gap-ledger.md | current gap ledger for the no-argument theorem |
| docs/audits/accepted-source-certification-status-board.md | accepted-source review state |

## Conditional Theorem

Fix a compactly supported half-density test g on R_+^*. Let:

```math
F_g = g^* * g
```

Choose a finite set of places S containing infinity. For a fixed support bound
A, assume:

```math
\mathrm{supp}(F_g) \subset \exp([-A, A])
```

The route takes:

```math
S_A = \{\infty\} \cup \{p : \log p \le A\}
```

This choice prevents a fixed-S trace from omitting a finite-prime atom visible
to F_g.

Choose lambda > 1 and a support window I:

```math
I \subset [\lambda^{-1}, \lambda]
\mathrm{supp}(g) \subset I
```

Assume these source inputs and project lemmas:

| input | content |
|---|---|
| CCM24 fixed-S model | canonical Hilbert model V_S = M_S U_S, bounded comparison, support transport, Fourier transport |
| CC20 trace package | archimedean support-square trace, trace-class legality, Mellin convention, finite-vanishing criterion |
| CCM25 Weil package | QW, QW_lambda, pole functional, finite-prime normalization |
| defect package | fixed-S trace read-off splits into QW_lambda, rank, pole, and endpoint-strip defect |
| exhaustion package | endpoint-strip defect tends to zero after g, S_A, I, and graph order are fixed |
| final sign bridge | QW(g,g) equals the negative CC20 Weil sum for the same F_g |
| final exit target | still open; it must not use the false forall-g criterion on `normalizedCC20TestSpace` |

Then the route proves:

```text
Mathlib _root_.RiemannHypothesis
```

## Proof

### 1. Move objects into the fixed-S canonical model

CCM24 supplies:

```math
V_S = M_S U_S
```

Let H_S be the fixed-S Hilbert space. Let P_S(lambda) be the source support
projection. The canonical support projection is:

```math
P_{S,G}(\lambda) = V_S P_S(\lambda) V_S^{-1}
```

Let F_S be the fixed-S Fourier symmetry. The Fourier-side support projection is:

```math
\widehat P_{S,G}(\lambda)
  = F_S^{-1} P_{S,G}(\lambda) F_S
```

The CCM24 comparison map identifies the semilocal and archimedean support
ranges:

```math
\mathrm{Ran}\,P_S(\lambda)
  =
S\,\mathrm{Ran}\,P_{\mathbb R}(\lambda)
```

The CCM24 Fourier compatibility gives:

```math
F_S S = S F_{\mathbb R}
```

Therefore:

```math
\mathrm{Ran}\,\widehat P_S(\lambda)
  =
S\,\mathrm{Ran}\,\widehat P_{\mathbb R}(\lambda)
```

This keeps the same g, F_g, S, I, and lambda through the trace read-off,
ledger clearing, exhaustion, restricted-to-full bridge, final sign bridge, and
RH exit.

### 2. Form the positive trace before reading it as a Weil expression

Let theta_S(g) be the bounded test operator attached to g in the fixed-S model.
Define:

```math
A_{S,\lambda}(g)
  =
\widehat P_{S,G}(\lambda) P_{S,G}(\lambda) \theta_S(g)
```

The CC20 trace-class input and the project trace-class wrappers prove that
A_(S,lambda)(g) is Hilbert-Schmidt. Hence:

```math
\mathrm{Pos}_{S,\lambda}(g)
  =
\mathrm{Tr}(A_{S,\lambda}(g)^* A_{S,\lambda}(g))
  \ge 0
```

The proof uses positivity only after the trace is defined.

### 3. Read the positive trace as a restricted Weil scalar plus ledgers

The source read-off has the form:

```math
\mathrm{Pos}_{S,\lambda}(g)
  =
QW_\lambda(g,g)
  + \mathrm{Rank}_{S,I}(g)
  + \mathrm{PoleJetExtra}_{S,I}(g)
  + R_{S,I,\lambda,J}(g)
```

| term | meaning |
|---|---|
| QW_lambda(g,g) | CCM25 restricted Weil scalar for the same g |
| Rank_(S,I)(g) | zero-mode ledger |
| PoleJetExtra_(S,I)(g) | two pole-evaluation ledgers |
| R_(S,I,lambda,J)(g) | endpoint-strip and projection-defect remainder |

The CCM25 restricted scalar uses the same square:

```math
F_g = g^* * g
```

and the same prime-power pairing:

```math
\langle g, T(n) g\rangle
  =
n^{-1/2} (F_g(n) + F_g(n^{-1}))
```

The finite-prime sign comes from the CCM25 formula for QW_lambda. The route
does not add a separate finite-prime sign convention.

### 4. Kill the rank and pole ledgers by triple vanishing

Restrict to tests satisfying:

```math
\widehat g(0) = \widehat g(i/2) = \widehat g(-i/2) = 0
```

The rank ledger is supported on g_hat(0). The pole ledger is supported on
g_hat(i/2) and g_hat(-i/2). Hence:

```math
\mathrm{Rank}_{S,I}(g) = 0
\mathrm{PoleJetExtra}_{S,I}(g) = 0
```

The read-off becomes:

```math
\mathrm{Pos}_{S,\lambda}(g)
  =
QW_\lambda(g,g)
  + R_{S,I,\lambda,J}(g)
```

Since Pos_(S,lambda)(g) >= 0:

```math
QW_\lambda(g,g) \ge -R_{S,I,\lambda,J}(g)
```

### 5. Bound and remove the endpoint-strip defect

The defect package proves:

```math
\left|R_{S,I,\lambda,J}(g)\right|
  \le
C_{S,I,J}(g) Cdef_{S,I,\lambda,J}(g)
```

The endpoint-strip norm is:

```math
Cdef_{S,I,\lambda,J}(g)
  =
\sum_\alpha \| \theta(D^r g) X_0 M_b T_a X_1 \theta(D^s g)^* \|_1
  +
\sum_\beta |\mathrm{BoundaryStripTrace}_\beta(g)|
```

Each summand contains an endpoint-strip factor. The fixed-test exhaustion
package gives:

```math
Cdef_{S_A,I,\lambda,J}(g) \to 0
\qquad \lambda \to \infty
```

Therefore:

```math
\liminf_{\lambda \to \infty} QW_\lambda(g,g) \ge 0
```

### 6. Pass from the restricted Weil form to the full Weil form

The restricted-to-full bridge proves that, for this fixed test and fixed
finite-prime visibility set S_A:

```math
QW_\lambda(g,g) \to QW(g,g)
```

Combining this with the previous inequality gives:

```math
QW(g,g) \ge 0
```

The bridge uses fixed-test support, prime-power atom stabilization,
finite-prime support equality, archimedean and pole stability, and endpoint
exhaustion. It does not use finite-operator spectral convergence, determinant
convergence, numerical eigenvalue convergence, or an even-sector
minimum-eigenvector assumption.

### 7. Convert QW positivity into the CC20 Weil inequality

The final sign bridge proves:

```math
QW(g,g)
  =
-\sum_v W_v(F_g)
```

Therefore:

```math
QW(g,g) \ge 0
  \Longrightarrow
\sum_v W_v(F_g) \le 0
```

This is the inequality direction that a valid CC20 exit would need.

### 8. Final exit status

The route cannot close by applying the naive finite-vanishing criterion to the
current concrete normalized CC20 test space. That criterion has the shape:

```text
for every compact smooth g,
  Mellin(g) vanishes on F
    =>
  WeilLocalSum(g * g) <= 0
```

The trace route proves a same-test inequality for tests carried by the selected
route data. It does not by itself prove the forall-g statement above.

The route uses the finite set:

```math
F = \{0, 1/2, 1\}
```

The triple vanishing condition matches this set under the CC20 convention:

```math
s = 1/2 - i t

t = 0    \mapsto s = 1/2
t = i/2  \mapsto s = 1
t = -i/2 \mapsto s = 0
```

The side condition that 1/2 is not a non-trivial zero is now recorded through
the eta-function route in `Source.ZetaHalfNonvanishing`. The points 0 and 1 are
excluded by the source non-trivial-zero convention.

The remaining final exit must use one of these two mathematical interfaces:

```text
Option A: restricted-test exit
  Define a source-backed CC20 subspace C_route.
  Prove the trace route gives the Weil inequality for every g in C_route.
  Prove C_route is sufficient for the CC20 RH exit.
  Current attack plan:
    plan/08A_2026-07-08_D1_restricted_test_cc20_sufficiency_plan.md

Option B: source-zero exclusion
  For each off-critical-line source zero rho, use a Yoshida detector and a
  non-circular route theorem to derive a contradiction.
  The theorem must be strictly weaker than SourceRH and must not be equivalent
  to no-off-line source zero.
  Current attack plan:
    plan/08B_2026-07-08_D1_source_zero_exclusion_plan.md
```

Current Lean evidence rules out the old shortcut. The project proves a compact
normalized CC20 test that vanishes on `{0, 1/2, 1}` but violates the
half-density pole-sum sign needed by the naive forall-g criterion. It also
proves that detector-wide pole-pairing nonnegativity is equivalent to the
no-off-line source-zero statement under Yoshida detector existence.

The RH-definition bridge can still transport a source RH theorem to Mathlib's
`_root_.RiemannHypothesis`. The missing part is the source RH theorem itself,
not the final definition transport.

### 9. Candidate final-exit contract

The next final-exit contract should name the test universe before it states a
Weil inequality.

```text
Restricted-test contract:
  C_route:
    source-backed CC20 tests produced by the route construction

  route inequality:
    for every g in C_route,
      compact(g)
      + Mellin(g) vanishes on {0, 1/2, 1}
      =>
      WeilLocalSum(g * g) <= 0

  sufficiency theorem:
    the restricted family C_route is large enough for the CC20 RH exit
```

That contract avoids the rejected forall-g claim on `normalizedCC20TestSpace`.
It still needs new mathematics: the sufficiency theorem must explain why the
restricted source-backed family detects all off-critical-line zeros needed by
the CC20 argument.

Route A proof tree:

```text
Route A: restricted-test CC20 sufficiency
|
+-- A1. Define C_route
|   |
|   +-- carrier:
|   |     route-backed CC20 tests with a source-backed fixed-S witness
|   |
|   +-- projection:
|         C_route.Test -> normalizedCC20TestSpace.Test
|
+-- A2. Prove route inequality on C_route
|   |
|   +-- use RouteBackedCC20ExitInputData for each route-backed test
|   +-- prove CC20WeilNonpositive for the projected normalized test
|
+-- A3. Prove detector coverage / sufficiency
|   |
|   +-- for each off-critical-line source zero rho
|   +-- produce a Yoshida detector whose test lies in C_route
|   +-- apply A2 to contradict Yoshida positivity
|
+-- rejected shortcuts
    |
    +-- no forall-g criterion on normalizedCC20TestSpace
    +-- no detector-wide pole-pairing nonnegativity
    +-- no selected one-test inequality masquerading as C_route sufficiency
```

Current Route A Lean boundary:

```text
TraceTransportScopedFormulaCalibration
|
+-- exact square pole-pairing transport
+-- support-square trace = no-defect source trace
+-- no-defect source trace = scoped restricted archimedean formula
+-- finite-prime index-difference / archimedean balance
+-- non-pole finite-prime mass vanishing
|
v
SquareRestrictedWeilCriterion
|
+-- detector coverage for off-line Yoshida detectors
|
v
SourceRH
```

The detector-only versions of the transport rows are rejected as lower
producers. Lean proves that both transport detector-coverage sockets are
equivalent to the no-off-line source-zero statement once Yoshida detector
existence is available. The same guard now covers the detector-only atomic and
scoped-formula B2 split.

A source-zero contract can replace it only if it stays below RH:

```text
Source-zero contract:
  input:
    rho is a standard source non-trivial zero
    rho.re != 1/2

  allowed tools:
    Yoshida detector existence
    route-backed sign/read-off theorem for the detector's actual test

  output:
    contradiction

  rejection condition:
    if the contract is equivalent to no-off-line source-zero, it is the RH
    conclusion under another name and cannot count as a lower proof.
```

Route B proof tree:

```text
Route B: non-circular source-zero exclusion
|
+-- B1. Assume rho is a standard source non-trivial zero off the line
|
+-- B2. Use 05C to obtain a Yoshida detector for rho
|
+-- B3. Produce a route-backed theorem for the detector's actual test
|   |
|   +-- must be below no-off-line source-zero
|   +-- must not be same-test Mathlib-bottom or pole-pairing nonnegative
|
+-- B4. Derive contradiction with Yoshida positivity
|
+-- rejected shortcuts
    |
    +-- SourceRH / no-off-line source-zero as input
    +-- detector-wide nonpositive or pole-pairing nonnegative
    +-- local-sum calibration already proved RH-equivalent
```

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
sum_v W_v(F_g) <= 0 for the selected route-backed test
  |
  v
open final exit:
  either restricted-test CC20 sufficiency
  or non-circular source-zero exclusion
  |
  v
SourceRH
  |
  v
Mathlib RiemannHypothesis
```

## Falsification Checks

A reviewer should reject the route if one of these checks fails.

| check | failure mode | first repository file to inspect |
|---|---|---|
| trace scale | the positive trace contains a lambda-growing bulk term outside QW_lambda, rank, pole, and Cdef | docs/proofs/trace-scale-compatibility-proof-package.md |
| fixed-S support transport | the fixed-S projection transport creates a fourth no-strip defect | docs/audits/semilocal-fourth-defect-ledger.md |
| finite-prime visibility | S_A omits a prime-power atom visible to F_g | docs/audits/s-local-global-quantifier-audit.md |
| pole separation | the CCM25 pole term is double-counted with the route pole ledger | docs/proofs/source-rank-pole-ledger-identification-proof-package.md |
| endpoint-strip exhaustion | Cdef_(S_A,I,lambda,J)(g) does not tend to zero for fixed g | docs/proofs/battle-3-cdef-exhaustion-proof-package.md |
| restricted-to-full bridge | QW_lambda -> QW imports a forbidden spectral or numerical convergence assumption | docs/audits/restricted-to-full-qw-source-readiness-audit.md |
| final sign | QW(g,g) has the wrong sign relative to sum_v W_v(F_g) | docs/proofs/final-sign-bridge-proof-package.md |
| final exit quantifier | a selected-test inequality is treated as the forall-g CC20 finite-vanishing criterion | ConnesWeilRH/Source/CC20TestSpace.lean; ConnesWeilRH/Source/CC20YoshidaConstruction.lean |
| RH-equivalent socket | detector-wide pole-pairing nonnegativity is used as if it were a lower lemma | ConnesWeilRH/Route/CC20RouteRealization.lean |
| RH definition | the source zero predicate does not match Mathlib's zeta-zero predicate | docs/proofs/rh-definition-bridge-proof-package.md |

## Lean Status

The active Lean root is:

```text
ConnesWeilRH.lean
```

It imports the source and route modules. It does not import:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
```

The route theorem has this conditional shape:

```text
RouteCertificate(inputs)
  =>
Mathlib _root_.RiemannHypothesis
```

The remaining formalization work is to replace source-facing certificate fields
and development skeleton assumptions by Lean proofs or accepted theorem imports
for the analytic rows.

Useful checks:

```text
lake build ConnesWeilRH
rg -n "sorry|admit|axiom|constant|opaque|unsafe" ConnesWeilRH -g "*.lean" -g "!ConnesWeilRH/Dev/**"
#print axioms ConnesWeilRH.Route.final_connes_weil_rh
```

Current boundary:

| artifact | status |
|---|---|
| mathematical route manuscript | source-conditional, referee-readable |
| Lean route composition | certificate-conditional |
| route-backed Yoshida final sign family | useful as contradiction infrastructure, but not a closed final exit |
| active no-argument blocker | `normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreFromTheorems`, which feeds no-off-line source-zero |
| rejected final-exit shortcut | `CC20FiniteVanishingWeilCriterion normalizedCC20TestSpace cc20TripleFiniteVanishingSet`; Lean proves this route false for the current concrete test space |
| focused axiom audit for final Dev RH outlets | still contains `sorryAx` |
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

## Version 0.2.4-dev Scope

Version 0.2.4-dev records the selected route-backed Yoshida final-sign shape in
the development skeleton. Later 2026-07-08 audits exposed the same-test
Mathlib-bottom and pole-pairing routes as RH-level sockets. The active
no-argument path now needs a new final exit: either a restricted-test CC20
sufficiency theorem, or a non-circular source-zero exclusion theorem.

This release does not change the proof status from conditional to
unconditional.
