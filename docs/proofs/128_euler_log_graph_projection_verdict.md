# Euler-Log Graph Projection Verdict

Date: 2026-07-12

Status: rejected as a finite-`S` same-square positive owner. The construction
passes the `p^2` coefficient gate but fails at `p^3`; prescribing the exact
Euler-log off-diagonal block is impossible for an orthogonal projection already
at `p=2`. RH remains unproved.

## Proposed new range

Let `P` be the positive-half-line projection, `Q=I-P`, and let `U` translate
left by `b=log(p)`. Put

```text
ell_a(U) = sum_(m>=1) a^m U^m/m,
a=p^(-1/2),
L_a=Q ell_a(U) P.
```

Unlike the rejected transported Sonin range, use the genuinely different
noncompact graph

```text
Graph(L_a) = {x + L_a x : x in Ran(P)}
```

and its orthogonal projection `G_a`. This proposal is source-independent: it
was designed directly from the coefficient requirement in Plan 036.

## Why the second order works

Write

```text
L_a=a L_1+a^2 L_2+O(a^3),
L_1=QUP,
L_2=(1/2)QU^2P.
```

In the decomposition `Ran(Q) direct-sum Ran(P)`, the graph projection is

```text
G_a = [L_a; I] (I+L_a*L_a)^(-1) [L_a*, I].
```

Its expansion through order two is

```text
G_a-P
 = a [0,L_1;L_1*,0]
 + a^2 [L_1L_1*,L_2;L_2*,-L_1*L_1]
 + O(a^3).                                             (G.1)
```

For an even translation-invariant same-square convolution `C`, reflection
interchanges `L_1L_1*` and `L_1*L_1` and commutes with `C`. Their traces in
(G.1) cancel. The off-diagonal term retains the coefficient `1/2`; crossing
length `2 log(p)` therefore gives the correct `p^2` Weil coefficient.

The finite-matrix check in
`128_euler_log_graph_projection_probe.py` compares the graph trace with its
linear Euler-log trace. The residual is `O(a^3)`, not `O(a^2)`:

```text
+-------+------------------+
| a     | residual / a^3   |
+-------+------------------+
| 0.080 | -11.90784348     |
| 0.040 | -11.67703078     |
| 0.020 | -11.55694393     |
| 0.010 | -11.49576592     |
+-------+------------------+
```

This verifies the block expansion but is not used as its proof.

## Third-order contamination

The inverse Gram factor in the graph projection is

```text
(I+L_a*L_a)^(-1)=I-a^2 L_1*L_1+O(a^3).
```

Consequently the off-diagonal block contains, at order `a^3`, not only the
desired `(1/3)QU^3P` term but also

```text
-L_1 L_1* L_1.                                        (G.2)
```

On functions supported in `(0,b)`, `L_1=QUP` is an isometry from that interval
onto `(-b,0)`. Hence

```text
L_1 L_1* L_1 = L_1
```

on an infinite-dimensional subspace. Equation (G.2) therefore inserts an
extra `-a^3 QUP` single-crossing channel. It has crossing length `log(p)`, not
`3 log(p)`, and cannot be assigned to the `p^3` Weil atom or to a compact
remainder.

## Exact-off-diagonal repair is impossible

One might try to replace the raw graph projection by an orthogonal projection
whose off-diagonal block is exactly

```text
K_a=Q ell_a(U) P.
```

Every off-diagonal block `K` of an orthogonal projection satisfies

```text
||K|| <= 1/2.                                          (G.3)
```

This follows from the scalar bound `x(1-x)<=1/4` applied to a diagonal block
`0<=A<=I` and the projection identity `KK*=A-A^2`.

At `p=2`, take a nonzero `f` supported in `(0,b)`. The functions `U^m f` have
pairwise disjoint supports `(-mb,-(m-1)b)`, so

```text
||K_a f||^2
 = (sum_(m>=1) a^(2m)/m^2) ||f||^2
 > a^2 ||f||^2
 = (1/2)||f||^2.
```

Thus

```text
||K_a|| > 1/sqrt(2) > 1/2,
```

contradicting (G.3). No orthogonal projection can own the exact Euler-log
off-diagonal channel at `p=2`.

## Verdict

```text
different noncompact graph range: constructed
positivity: automatic from orthogonal projection
p coefficient: correct
p^2 coefficient: correct after diagonal trace cancellation
p^3 coefficient: polluted by graph normalization
exact Euler-log off-diagonal repair: violates ||K||<=1/2 at p=2
route owner: rejected
Lean declaration: forbidden
```

The useful lesson is narrower than a general no-go theorem: positivity through
one orthogonal projection cannot carry the full Euler logarithm as its
off-diagonal block. A future construction must either use a positive object
that is not a projection or distribute the Euler logarithm through a larger
graded structure while preserving one archimedean bulk.
