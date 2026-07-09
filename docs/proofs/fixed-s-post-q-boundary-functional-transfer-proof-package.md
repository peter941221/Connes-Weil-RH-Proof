# Fixed-S Post-Q Boundary Functional Transfer Proof Package

Status: route-evidence proof package for the second Row 3 subcontract.

This package proves the project-level bridge targeted by:

```text
docs/proofs/fixed-s-post-q-boundary-functional-transfer-theorem-contract.md
```

It is not a CC20 or CCM24 source import. It is not a Lean theorem. It records
the route proof that must later be formalized or replaced by an accepted
external theorem.

## Result

Good result:

```text
FixedSPostQBoundaryFunctionalTransfer is closed at route-evidence level for
the two CC20 post-Q endpoint terms.
```

Boundary:

```text
This does not close Row 3 as a whole.
Series-tail bounded comparison remains open.
Rows 4-7 remain separate.
```

## Target

For the CC20 source boundary terms:

```text
B_lower_n(rho)
  =
rho^(-1/2) (D_u xi_n)(rho^-1) zeta_n(1),

B_upper_n(rho)
  =
-rho^(1/2) xi_n(1) (D_u zeta_n)(rho),
```

prove the route-evidence bridge:

```text
FixedSPostQBoundaryFunctionalTransfer(S,I,lambda,g,F_g,n):
  PostQBoundaryEvaluationTransport(S,I,lambda,g,F_g,n)
  and
  PostQBoundaryFixedSEquality(S,I,lambda,g,F_g,n).
```

## Evidence Boundary

| claim | evidence |
|---|---|
| CC20 source endpoint terms | `weil-compo.tex:1267-1270`, `1308-1333` |
| CC20 domain failure | `weil-compo.tex:1260-1264` |
| CC20 boundary estimate | `weil-compo.tex:2215-2236` |
| CCM24 fixed-S window and coordinate | `mainc2m24fine.tex:761-771`, `983-1003`, `1022-1029` |
| CCM24 non-commutation warning | `mainc2m24fine.tex:846-852` |
| route finite-strip endpoint trace estimate | `docs/proofs/semilocal-q-compact-form.md:283-298` |
| route boundary normal form with strip factor | `docs/proofs/rank-repair-finite-normal-form.md:249-255` |
| fixed finite-S graph boundedness | `docs/proofs/fixed-test-graph-cdef-exhaustion.md:112-141` |
| bulk proof package coordinate convention | `docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md:141-207` |

## Proof Skeleton

```text
CC20 source endpoint terms
        |
        v
log-coordinate endpoint functionals
        |
        v
finite-strip Sobolev trace continuity
        |
        v
fixed finite-S graph/window transport
        |
        v
V_S=M_S U_S common coordinate
        |
        v
fixed-S source-owned boundary objects
        |
        v
inputs for Row 5/6 only
```

The proof stops before rank, pole, or endpoint-strip `Cdef` classification.

## Lemma 1. Source Boundary Objects Are Domain-Repair Terms

Statement:

```text
CC20PostQBoundaryEndpointObjects(n):
  the lower and upper endpoint terms are source-owned terms produced by Lemma
  devil3 after the failed formal D_u domain argument.
```

Proof.

CC20 first records that the formal identity cannot be applied directly to
`xi_n,zeta_n` because they are not in `Dom(D_u)`. Source:

```text
weil-compo.tex:1260-1264
```

Lemma `devil3` repairs the failed formal-domain move by replacing it with:

```text
Qk(rho)
  =
bulk derivative integral
  +
rho^(-1/2)(D_u xi_n)(rho^-1) zeta_n(1)
  -
rho^(1/2) xi_n(1)(D_u zeta_n)(rho).
```

Sources:

```text
weil-compo.tex:1267-1270
weil-compo.tex:1308-1333
```

Therefore the two endpoint terms are not optional error notation. They are
source-owned summands of the repaired post-`Q` formula. This package transports
them. It does not classify them.

Output:

```text
lower_endpoint_source_object
upper_endpoint_source_object
endpoint_terms_repair_domain_failure
endpoint_terms_separated_from_bulk
```

## Lemma 2. Source-To-Log Endpoint Translation

Statement:

```text
SourcePostQBoundaryLogTranslation(n):
  the CC20 endpoint evaluations at rho^-1 and 1 become endpoint functionals
  at -log rho and 0 in the route logarithmic coordinate.
```

Proof.

Use the logarithmic coordinate:

```text
t = log x.
```

Then:

```text
rho^-1 -> -log rho
1      -> 0
```

For a source function `f(x)`, define:

```text
F(t) = f(e^t).
```

Then:

```text
dF/dt = e^t f'(e^t) = D_u f(e^t).
```

Thus the factors:

```text
(D_u xi_n)(rho^-1)
(D_u zeta_n)(rho)
```

are endpoint values of log-derivative representatives at the route endpoints
selected by `rho` and the fixed endpoint `1`.

For the route tuple, `rho` is read inside the same lambda/window gate used by
the fixed-S positive trace and restricted `QW_lambda`. Hence the moving lower
endpoint lies inside the same logarithmic window, and the fixed endpoint `1`
maps to the internal point `0`.

Output:

```text
lower_endpoint_rho_inverse_maps_to_minus_log_rho
upper_endpoint_one_maps_to_zero
source_Du_boundary_factor_is_log_derivative
source_zeta_or_xi_endpoint_factor_kept_visible
```

## Lemma 3. Endpoint Trace Continuity On The Fixed Window

Statement:

```text
FixedWindowEndpointTraceContinuity(S,I,lambda,J_Q):
  at fixed graph order J_Q, the lower and upper endpoint evaluations are
  bounded functionals on the finite-strip graph class used by the route.
```

Proof.

The route already uses the finite-strip Sobolev trace estimate for boundary
terms with a strip factor before evaluation:

```text
|evaluation(A_r v)|
  <=
C_(S,I,J)(h) ||v||_(L2(E_(lambda,a))).
```

Evidence:

```text
docs/proofs/semilocal-q-compact-form.md:283-298
docs/proofs/rank-repair-finite-normal-form.md:249-255
```

The boundary terms in this package have already been translated to endpoint
functionals on the same log window by Lemma 2. Choose a fixed graph order
`J_Q` large enough to contain the one scaling derivative created by the
endpoint factors and the bounded number of derivatives introduced by `Q`.

The Sobolev trace constant depends on the fixed finite data:

```text
S, I, J_Q
```

and on the selected finite strip, not on a fresh source object. It is fixed
before the later lambda limit.

Output:

```text
lower_endpoint_functional_continuous
upper_endpoint_functional_continuous
finite_strip_Sobolev_trace_constant_named
constant_depends_on_fixed_S_I_JQ
constant_fixed_before_lambda_limit
```

## Lemma 4. Fixed Finite-S Boundary Transport

Statement:

```text
FixedFiniteSBoundaryTransport(S,I,lambda,J_Q):
  fixed finite-S Euler/window factors preserve the graph class on which the
  lower and upper boundary functionals are continuous.
```

Proof.

CCM24 supplies the fixed-S support and Fourier transport, plus the Sonin-space
comparison. Sources:

```text
mainc2m24fine.tex:761-771
mainc2m24fine.tex:983-1003
mainc2m24fine.tex:1022-1029
```

Those are model and window facts. They do not alone transport endpoint
evaluation. The graph upgrade comes from the project fixed finite-S calculus:

```text
Since S_A is fixed, multiplying by M_S, M_S^*, or finitely many fixed Euler
graph factors preserves Schwartz-tail decay up to a fixed polynomial weight.
```

Evidence:

```text
docs/proofs/fixed-test-graph-cdef-exhaustion.md:112-141
```

Thus the endpoint functionals from Lemma 3 remain bounded after fixed finite-S
transport into the common route coordinate. This proof does not use:

```text
N_S eta_S = eta_S N_infty.
```

CCM24 warns against that shortcut at:

```text
mainc2m24fine.tex:846-852
```

Output:

```text
fixedS_lowerBoundary_functional
fixedS_upperBoundary_functional
fixedS_boundary_graph_order_JQ_named
no_sonin_isomorphism_endpoint_shortcut
```

## Lemma 5. Fixed-S Boundary Functional Representative

Statement:

```text
FixedSPostQBoundaryFunctionalRepresentative(S,I,lambda,g,F_g,n):
  the two CC20 source endpoint terms have fixed-S boundary functional
  representatives in the common coordinate V_S=M_S U_S.
```

Proof.

Combine:

```text
1. source-owned endpoint terms,
2. log-coordinate endpoint translation,
3. finite-strip endpoint trace continuity,
4. fixed finite-S boundary transport,
5. CCM24 common coordinate and window.
```

The transported boundary objects are defined by applying this chain to the
CC20 source endpoint terms. The tuple is unchanged:

```text
(S,I,lambda,g,F_g,n)
```

No new test, window, finite set, or lambda parameter is introduced.

Output:

```text
fixedS_lowerBoundary_functional
fixedS_upperBoundary_functional
fixedS_boundary_uses_same_S
fixedS_boundary_uses_same_I
fixedS_boundary_uses_same_lambda
fixedS_boundary_uses_same_g_and_Fg
fixedS_boundary_lives_in_VS_coordinate
```

## Lemma 6. Source-Boundary Equality Before Row 5/6

Statement:

```text
PostQBoundaryFixedSEquality(S,I,lambda,g,F_g,n):
  the fixed-S boundary representatives are the transported images of the
  CC20 source endpoint terms, not route-local lookalikes.
```

Proof.

The fixed-S objects in Lemma 5 are not introduced independently. They are
defined as the images of the CC20 source endpoint terms under:

```text
CC20 source endpoint term
        |
        v
log-coordinate endpoint translation
        |
        v
finite-strip trace continuity
        |
        v
fixed finite-S graph/window transport
        |
        v
V_S=M_S U_S coordinate
```

Each arrow is indexed by the same tuple:

```text
(S,I,lambda,g,F_g,n).
```

Thus the equality required before Row 5/6 is definitional at route-evidence
level, once the transport chain is fixed and no fresh local boundary object is
allowed.

This is not a rank, pole, or `Cdef` conclusion. It only says that Row 5/6 will
classify the source-owned transported endpoint terms.

## Theorem. Fixed-S Post-Q Boundary Functional Transfer

Statement:

```text
FixedSPostQBoundaryFunctionalTransfer(S,I,lambda,g,F_g,n):
  PostQBoundaryEvaluationTransport(S,I,lambda,g,F_g,n)
  and
  PostQBoundaryFixedSEquality(S,I,lambda,g,F_g,n).
```

Proof.

`PostQBoundaryEvaluationTransport` follows from Lemmas 2 through 5:

```text
source endpoint evaluation
  =
log endpoint functional
  -> finite-strip bounded functional
  -> fixed-S boundary representative in V_S coordinate.
```

`PostQBoundaryFixedSEquality` follows from Lemma 6.

The proof uses:

```text
source ownership from CC20,
fixed-S model and window from CCM24,
project finite-strip trace continuity,
project fixed finite-S graph boundedness,
same tuple and same window throughout.
```

It does not use:

```text
automatic Sonin-isomorphism transport of endpoint evaluation,
triple vanishing,
rank/pole classification,
endpoint-strip Cdef domination,
series-tail convergence,
or a lambda -> infinity limit.
```

## Output To The Row Ledger

This package supplies, at route-evidence level:

```text
PostQBoundaryEvaluationTransport
PostQBoundaryFixedSEquality
```

It does not supply:

```text
PostQSeriesTailBoundedComparison
CC20PostQRemainderFixedSSoninTransport
SoninProlateDefectEqualsEndpointStripCdef
```

## Current Status

```text
Source endpoint ownership:              proved at route-evidence level
Source-to-log endpoint translation:     proved at route-evidence level
Fixed-window endpoint trace continuity: proved at route-evidence level
Fixed-S boundary representative:        proved at route-evidence level
Source-boundary equality before Row 5/6: proved at route-evidence level

Series-tail bounded comparison:         closed separately at route-evidence level
Full Row 3 transport:                   closed separately at route-evidence level
Sign/defect bridge:                     open
```
