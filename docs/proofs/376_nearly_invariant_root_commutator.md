# Proof 376: nearly-invariant root commutator

Date: 2026-07-18

Status: universal condition-number-free Hilbert--Schmidt estimate for a smooth
multiplier against the orthogonal projection onto any scalar nearly invariant
Hardy subspace.  The constant does not depend on the inner function, extremal
multiplier, Euler prefix, or smallest Gram eigenvalue.

This closes the operator-theoretic part of `(MR.6)`.  Proof 377 supplies the
compact-root Sobolev bound for the Cayley coefficient functional.

## 1. Result

Let `M` be a closed nearly invariant subspace of disk `H^2`, and let `P_M` be
its orthogonal projection in boundary `L2`.  If

```text
c(zeta)=sum_(n in Z)c_n zeta^n,
A(c)=sum_(n !=0)sqrt(abs(n)) abs(c_n)<infinity,       (NR.1)
```

then

```text
[M_c,P_M] in S_2,
norm([M_c,P_M])_2<=sqrt(2) A(c).                     (NR.2)
```

The same estimate holds for the full Hardy projection `P_+`.

## 2. Hitt--Sarason representation

Hitt's theorem gives

```text
M=g K_I,                                             (NR.3)
```

where `I` is inner and multiplication by the extremal function `g` is an
isometry from `K_I` onto `M`.  On a dense boundary domain, the orthogonal
projection is

```text
P_M=M_g P_(K_I) M_(conj(g)).                         (NR.4)
```

Hartmann--Ross records both `(NR.3)` and the projection formula:

```text
Hartmann--Ross, Truncated Toeplitz operators and boundary values in
nearly invariant subspaces, Section 2 and Lemma 2.4:
https://arxiv.org/abs/1101.3771
```

No `L-infinity` bound on `g` is used below.

## 3. Rank-two Cayley defect

For a model space,

```text
P_(K_I)=P_+-M_I P_+ M_(conj(I)).                     (NR.5)
```

Multiplication operators commute.  Therefore, first for bounded dense-domain
vectors and then by continuity,

```text
[M_z,P_M]
 =M_g[M_z,P_(K_I)]M_(conj(g)).                       (NR.6)
```

The Hardy commutator `[M_z,P_+]` has rank one.  Equation `(NR.5)` makes
`[M_z,P_(K_I)]` the difference of two rank-one operators.  Hence

```text
rank([M_z,P_M])<=2.                                  (NR.7)
```

This rank statement survives even when the extremal multiplier is unbounded:
the left side of `(NR.6)` is already a bounded commutator, and the dense-domain
range lies in a fixed two-dimensional space.

## 4. Powers

For `n>=1`, the exact telescope is

```text
[M_(z^n),P_M]
 =sum_(k=0)^(n-1)
   M_(z^k)[M_z,P_M]M_(z^(n-1-k)).                    (NR.8)
```

Thus

```text
rank([M_(z^n),P_M])<=2n.                             (NR.9)
```

The negative powers follow by adjointing.  Since `M_(z^n)` is unitary and
`P_M` is an orthogonal projection, its off-diagonal commutator has operator norm
at most one.  Combining this with `(NR.9)` gives

```text
norm([M_(z^n),P_M])_2<=sqrt(2 abs(n)).               (NR.10)
```

## 5. Smooth multiplier

For a trigonometric polynomial, sum `(NR.10)`:

```text
norm([M_c,P_M])_2
 <=sum_(n !=0)abs(c_n)
      norm([M_(z^n),P_M])_2
 <=sqrt(2)A(c).                                      (NR.11)
```

If `A(c)<infinity`, its trigonometric truncations are Cauchy in `S_2` by
`(NR.11)` and converge in operator norm to `[M_c,P_M]`.  This proves `(NR.2)`.

The proof uses rank before norm.  It never estimates the extremal multiplier,
a compressed Gram inverse, or the two physical Sonin branches separately.

## 6. Uniformity for Proof 375

Apply `(NR.2)` to every nearly invariant endpoint `M_j` from Proof 375:

```text
sup_j norm([M_c,P_(M_j)])_2<=sqrt(2)A(c).            (NR.12)
```

Since the bound is independent of `M_j`, it is automatically independent of
the visible prime set and its ordering.  This is the missing structural fact
which the generic Gram and Markov guards did not contain.

## 7. Reproducible certificate

The companion probe constructs a nontrivially transported nearly invariant
polynomial range in a large Laurent coefficient space.  It checks

```text
rank([z^n,P_M])<=2 abs(n),
norm([z^n,P_M])<=1,
norm([c,P_M])_2<=sqrt(2)A(c).                        (NR.13)
```

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/376_nearly_invariant_root_commutator_probe.py
```

The finite certificate checks the rank/telescope mechanism.  Hitt's theorem
and `(NR.5)--(NR.11)` are the continuous proof.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| arbitrary nearly invariant endpoint           | uniform S2 commutator    |
| Euler condition number                        | absent                    |
| extremal multiplier norm                      | absent                    |
| Cayley coefficient functional `A(c)`           | only remaining input     |
| compact-root bound for `A(c)`                  | Proof 377                |
| endpoint theorem `(MR.6)`                      | pending Proof 377        |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
