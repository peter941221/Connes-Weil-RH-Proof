# Metric Sonin Common-Domain Rejection

Date: 2026-07-12

Status: Plan 024 is rejected as an executable route. The bounded metric
projection formula survives as a research idea, but neither the global
fixed-`S` post-`Q` compact remainder nor its proposed de Branges Rayleigh
problem has been constructed. RH remains unproved.

## 1. Result First

```text
CC20 post-Q test operator: acts on L2(sqrt I, d*rho)
CC20 prolate angle correction: acts in L2(R)_ev
CCM24 de Branges space: realizes the semilocal Sonin space
project theorem identifying these three operators/spaces: none
former <2 gate on B_lambda: not well-typed
```

The immediate failure is not a missing numerical estimate. The proposed
quadratic form uses a vector from one Hilbert space and an operator from
another, without an isometry that transports the operator, norm, route
conditions, and trace identity together.

## 2. CC20 Has Two Different Compact Operators

CC20 first proves the angle decomposition

```text
P P_hat P
  = sum_n lambda(n)^2 |zeta_n><zeta_n| + R_Sonin.
```

Source: CC20, arXiv:2006.13771, `weil-compo.tex:1072-1076`.
The identity

```text
sum_n lambda(n)^2
  = 2(Si(4*pi)/(4*pi)+1)
  approximately 2.237484835
```

is at `weil-compo.tex:1098-1103`. This is the trace of the positive prolate
angle correction in `L2(R)_ev`.

The post-`Q` operator used for the sign argument is different. CC20 Theorem
`thmqkey1` defines, for `xi in L2(sqrt I, d*rho)`,

```text
D o Q(xi*xi*) = <xi,(-2 Id+K_I)xi>,

K_I(v,u) = Q delta(max(u/v,v/u)).
```

Source: `weil-compo.tex:765-808`. Its compactness comes from this explicit
Hilbert-Schmidt kernel on the bounded test-support interval. The number
`2.237484835` does not give the norm, trace, or threshold of this `K_I`.

For the later Sonin remainder `E o Q`, CC20 introduces yet another normalized
operator `Kf_I` with kernel built from `Q epsilon`; see
`weil-compo.tex:1394-1421`. Its largest eigenvalue is about `1.05158`, and the
paper controls it by a separate rank-one condition; see
`weil-compo.tex:1873-1953`.

Therefore the inference

```text
positive trace-class prolate correction
  -> fixed-S post-Q remainder = -2 Id + compact K_S
```

does not follow from the cited CC20 decomposition.

## 3. The De Branges Space Is The Wrong Domain

CCM24 defines `B_lambda` as the image of the Sonin space under the completed
Mellin transform. Source: arXiv:2310.18423v2,
`mainc2m24fine.tex:1031-1050`. Proposition `propbb` identifies the semilocal
Sonin space with that same entire-function vector space while changing its
inner product; see `mainc2m24fine.tex:1050-1073`.

This proves stability of Sonin vectors. It does not identify `B_lambda` with
CC20's `L2(sqrt I, d*rho)` of convolution roots. Consequently the former Plan
024 expression

```text
<F,K_(S,I)F>,  F in B_lambda
```

has no defined owner: `K_(S,I)` was supposed to extend an operator acting on a
test-root space, while `F` was taken from the Sonin-image space.

The correct route vanishing conditions must instead be represented inside the
same test-root Hilbert space on which the explicit fixed-`S` kernel acts. Under
the log-coordinate Fourier/Mellin transform these are evaluation representers
in a Paley-Wiener-type support space, not automatically the reproducing kernels
of CCM24's Sonin de Branges space.

## 4. The Global Fixed-S Identity Is Still Missing

The half-line calculation

```text
Tr(C_h* C_h J_b)=b(h* * h)(b)
```

correctly identifies the local coefficient of one partial translation. It does
not prove that the full metric Sonin projection decomposes into exactly those
single crossings plus one residual compact kernel on `L2(sqrt I)`.
`038_single_crossing_weil_read_off.md:113-123` already records this missing
global angle identification.

Thus a certified Rayleigh computation currently has no exact operator to
discretize. A finite section would certify a chosen proxy, not Contract M3B.

## 5. Reopening Contract

Reopen the metric Sonin lane only after proving one theorem with the following
same-object data:

```text
H_I                    named test-root Hilbert space
xi(g) in H_I           source test and convolution-root map
R_(S,lambda)           metric Sonin projection
K_(S,I) : H_I -> H_I   explicit residual post-Q kernel
trace identity          positive trace = QW + <-c Id+K,->
main-term theorem       every single crossing, both cutoff orientations
compactness theorem     only the residual kernel is compact/self-adjoint
route representers      Mellin evaluations as vectors in H_I
restricted bound        <xi,K xi> < c ||xi||^2 on their kernel intersection
```

The theorem must not use the desired restricted bound as a premise and must not
transport through `B_lambda` merely because the norms are equivalent.

## 6. Route Judgment

```text
metric projection formula: retained
local prime-power coefficient: retained as a local lemma
finite-S compact remainder: unproved
de Branges bad-space ownership: rejected as ill-typed
Plan 016 M3B: unfilled
Lean implementation: unauthorized
RH: unproved
```

Primary sources:

```text
CC20: https://arxiv.org/abs/2006.13771
CCM24: https://arxiv.org/abs/2310.18423
```
