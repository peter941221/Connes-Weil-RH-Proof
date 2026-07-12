# De Branges Bad-Space Gate

Date: 2026-07-12

Status: superseded by `040_metric_sonin_domain_rejection.md`. The de Branges
space here realizes semilocal Sonin vectors, while CC20's post-`Q` compact
operator acts on the compactly supported convolution root in `L2(sqrt I)`.
Without a same-object unitary transport theorem, (B.5)--(B.7) are not defined
on one Hilbert space and cannot serve as the final sign gate. RH remains
unproved.

## 1. Same Entire-Function Space

CCM24 proves that every semilocal Sonin space has the same de Branges
realization `B_lambda` as a vector space of entire functions:

```text
upsilon_S o theta_S = upsilon_infinity.                  (B.1)
```

Source: `mainc2m24fine.tex:1031-1062`, especially Proposition `propbb`.

The finite set `S` changes the inner product inherited from

```text
L2(R, ds/|E_S(s)|^2),                                    (B.2)
```

not the underlying entire function. Thus the route subspace

```text
C_route={F in B_lambda | F(0)=F(1/2)=F(1)=0}             (B.3)
```

is literally the same algebraic subspace for every finite `S`.

## 2. Pole-Node Caveat

One must not justify (B.3) by claiming that every local transfer multiplier is
nonzero at the three nodes. For

```text
B_p(t)=1-p^(-1/2-it),                                    (B.4)
```

one has `B_p(i/2)=0`. Stability comes from the commuting de Branges diagram
(B.1), where local factors cancel between the semilocal transform and
`theta_S`, not from pointwise invertibility of the analytic continuation of
`B_p`.

On the real spectral axis `B_p` is bounded away from zero, which is enough for
the Hilbert-space metric projection. These are different statements and must
not be conflated.

## 3. Exact Final Theorem

Plan 037 reduces the post-`Q` remainder to

```text
-2 Id+K_(S,I),  K_(S,I) compact self-adjoint.            (B.5)
```

The route closes if one proves either

```text
<F,K_(S,I)F><2 norm(F)^2  for every nonzero F in C_route, (B.6)
```

or the sharper ownership statement

```text
the spectral subspace of K_(S,I) for eigenvalues >=2
is contained in span of the reproducing kernels at 0,1/2,1.              (B.7)
```

Because functions in (B.3) are orthogonal to those reproducing kernels in the
appropriate de Branges inner product, (B.7) implies (B.6).

## 4. What Equivalent Norms Do Not Prove

CCM24 proves that the semilocal norms are equivalent and each makes
`B_lambda` a de Branges space. Norm equivalence gives bounded invertible metric
operators and continuity of evaluations. It does not imply:

```text
the reproducing kernels are unchanged as vectors;
the compact bad eigenspace is fixed;
the norm of K_(S,I) is less than 2;
or the bad eigenspace lies in the three evaluation kernels.              (B.8)
```

Claiming any item in (B.8) from the common underlying function set would store
the missing RH-level sign theorem in a change of norm.

## 5. Former Attack

The former proposed calculation was `S={infinity,2}`:

```text
1. write K_(S,I)-K_(infinity,I) from the metric resolvent;
2. compress it to C_route using the three-point reproducing-kernel
   Schur complement;
3. obtain a certified upper bound below the archimedean margin 2;
4. reject immediately if a certified Rayleigh quotient reaches 2.        (B.9)
```

This calculation is not legitimate until an explicit fixed-`S` remainder is
constructed on CC20's test-root Hilbert space and the route evaluations are
represented in that same space. The de Branges reproducing kernels above live
in the Sonin-image space and cannot be inserted into the missing operator by
notation alone.

## 6. Verdict

```text
same de Branges function space: source-proved.
same triple-vanishing subspace: exact.
local multiplier nonzero at all nodes: false.
metric Hilbert-space invertibility on real axis: true.
post-Q operator on B_lambda: not defined.
bad-space evaluation ownership: rejected as stated.
next gate: construct the fixed-S kernel on the test-root Hilbert space.
RH: unproved.
```
