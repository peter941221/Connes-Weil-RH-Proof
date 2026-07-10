# CC20 Fixed-S Remainder Source Certificate

Date: 2026-07-10

Decision:

```text
archimedean remainder source: present
fixed-S remainder object: derivable in the unitary scattering coordinate
remainder vanishes under the route's three conditions: false
exact no-defect read-off: rejected
Phase 5 authorization: denied
```

Superseding proof and counterexample:

```text
docs/proofs/cc20-012-mathematical-verdict.md, Sections 4-6
```

The direct construction replaces the proposed `eta_S` transport. It defines
the fixed-S remainder from `u_S` and the support projection in one Hilbert
space. The archimedean specialization proves that this remainder does not
vanish on the full triple-vanishing test class.

## Target

Plan 012 needs a fixed-S equality that owns every term in

```text
ordinary positive trace
  -> support-square trace
  -> regularized source trace
  -> rank and Tate/pole evaluations
  -> projection-defect traces
  -> endpoint-strip Cdef remainder
```

The source must identify the same finite set `S`, cutoff `lambda`, test `g`,
coordinate, projections, and measures as the operator/kernel owner.

## Archimedean Source Objects

CC20 defines the local trace remainder by

```text
delta(rho)
  = Tr((theta(rho^(-1)) - P theta(rho^(-1)) P)
       (1/2) (u_infinity^* d^-u_infinity)^g).
```

It proves, for `rho >= 1`,

```text
delta(rho)
  = 4 rho^(1/2)
      integral_Delta cos(2*pi*rho*x*y) cos(2*pi*x*y) dx dy,
```

and the symmetry `delta(rho)=delta(rho^(-1))`.

Source: arXiv:2006.13771, Definition 2.1 and Proposition 2.2,
`weil-compo.tex:488-559`.

The same proposition proves

```text
Tr(theta(f) P P_hat P)
  = integral f(rho^(-1)) (delta(rho)-tau(rho)) d*rho,
```

and therefore

```text
W_infinity = L - D.
```

Source: arXiv:2006.13771, formulas (33)-(39),
`weil-compo.tex:500-604`.

CC20 later refines the local error through the Sonin/prolate expansion and the
post-`Q` boundary and series terms. The project source map records the relevant
original TeX ranges as `weil-compo.tex:875-878`, `1132-1140`, `1260-1346`, and
`2168-2250`.

## Semilocal Source Objects

Connes 1999 defines the fixed-S cutoff trace

```text
Trace(R_Lambda U(h))
```

on `L2(X_S)` and proves its asymptotic decomposition into the local principal
values for the places in `S`, plus `o(1)`.

Source: arXiv:math/9811068, Theorem 4, source lines 1893-1910 and proof lines
1925-2216.

CCM24 proves support inclusion and Fourier compatibility for `eta_S`, and a
bounded Sonin-space isomorphism for `theta_S`.

Source: arXiv:2310.18423v2, Propositions 4.1, 4.3, 4.7 and Theorem 4.6,
`mainc2m24fine.tex:761-823` and `935-1029`.

CCM25 gives the restricted Weil quadratic form `QW_lambda` and the finite-prime
pairings. It does not state the fixed-S positive-trace remainder equality.

Source: Alain Connes, Caterina Consani, Henri Moscovici, "Zeta Spectral
Triples", arXiv:2511.22755, `mc2arXiv.tex:445-470` and `530-540`.

URL: https://arxiv.org/abs/2511.22755

## Missing Fixed-S Transport

No checked source proves a map carrying the CC20 post-`Q` remainder to the
fixed-S route while preserving all of these objects:

```text
scaling action and its derivative domain
support and Fourier-support orthogonal projections
regularized trace convention
moving and fixed boundary evaluations
post-Q series tail
projection-defect commutators
endpoint-strip measure and trace norm
```

CCM24 gives direct evidence against a notation-only transport. It states that
`eta_S` is nonunitary and that the semilocal Hermite and multiplication
operators do not intertwine with their archimedean versions. Thus the local
post-`Q` derivative, projection, and boundary formulas do not move through
`eta_S` by conjugation.

Source: arXiv:2310.18423v2, `mainc2m24fine.tex:837-861`.

The project proof packages classify a proposed transport into rank, pole, and
endpoint-strip `Cdef` rows. Those documents are route drafts. They do not supply
a primary-source theorem or a Lean derivation from lower analytic definitions.

## First Missing Equalities

The fixed-S certificate cannot fill these rows:

```text
SourceCC20PostQDerivativeDomainFixedSTransport
SourceCC20PostQBoundaryEvaluationFixedSTransport
SourceCC20PostQSeriesTailFixedSTransport
SourceCC20ProjectionDefectNormalForm
SourceCC20EndpointStripCdefDomination
SourceCC20NoHiddenPositiveDefectOutsideCdef
```

The strongest source result before this gap is the local CC20 post-`Q`
remainder together with the semilocal Sonin-space isomorphism. Their
composition does not preserve the operators required by the target equality.

## Search Coverage

The audit checked the original TeX for:

```text
arXiv:math/9811068
arXiv:2006.13771
arXiv:2106.01715
arXiv:2207.10419
arXiv:2310.18423v2
arXiv:2511.22755
```

Official source pages:

```text
https://arxiv.org/abs/math/9811068
https://arxiv.org/abs/2006.13771
https://arxiv.org/abs/2106.01715
https://arxiv.org/abs/2207.10419
https://arxiv.org/abs/2310.18423
https://arxiv.org/abs/2511.22755
```

No source contains the route's `endpoint-strip Cdef` normal form or a theorem
excluding an additional semilocal defect after transport.

## Verdict

```text
strongest archimedean theorem: CC20 local trace remainder and post-Q expansion
source space: L2(R_+^*) / the single archimedean Sonin model
target space: L2(X_S)^(K_S) with fixed-S orthogonal cutoffs
direct fixed-S definition: available through the unitary scattering phase u_S
counterexample: D o Q is -2 Id plus a compact Hilbert-Schmidt operator
triple-vanishing restriction: still contains a nonzero remainder
decision: reject the exact no-defect target
```

Phase 5, support-square/no-defect read-off, package rewiring, and both Dev-root
removals cannot proceed with the current consumer. A corrected consumer must
retain the source remainder or consume a proved finite-codimension conditioning
theorem.
