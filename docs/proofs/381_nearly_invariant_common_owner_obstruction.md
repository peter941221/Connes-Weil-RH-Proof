# Proof 381: nearly-invariant common-owner obstruction

Date: 2026-07-18

Status: exact infinite-dimensional obstruction to deriving Proof 380's common
range-root factor from near invariance, finite commutator rank, and a uniform
Hilbert--Schmidt norm alone.  Standard monomial model spaces already have
rank-two shift commutators whose active source vector escapes through an
orthonormal sequence.

This does not obstruct the actual CCM24 route, because that route also has
compact real-line boundary localization and one fixed causal source carrier.
It proves that this source geometry is mandatory.  Gate 3U, the finite-`S`
sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| every endpoint nearly invariant              | yes                      |
| shift commutator rank                         | exactly two              |
| operator norm                                 | one                      |
| Hilbert--Schmidt norm                         | `sqrt(2)` uniformly     |
| one common `S_2` right owner                  | impossible uniformly    |
| actual boundary-localized CCM24 family        | not rejected            |
| finite certificate                            | supplied                |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

The rejected inference is

```text
uniform rank and S_2 bounds for [C,P_j]
  -X-> [C,P_j]=B_j A_root with
       one fixed Hilbert--Schmidt A_root and
       uniformly bounded B_j.                     (NO.1)
```

## 2. Monomial model spaces

Work on boundary `L^2(T)=ell^2(Z)` with Fourier basis `(e_k)_(k in Z)`.  Let

```text
U e_k=e_(k+1)                                      (NO.2)
```

be the bilateral shift.  For `N>=1`, let

```text
M_N=K_(z^N)=span(e_0,...,e_(N-1)),
P_N=orthogonal projection onto M_N.                (NO.3)
```

Every `M_N` is a scalar Hardy model space and hence nearly invariant.

Define

```text
D_N=[U,P_N]=U P_N-P_N U.                           (NO.4)
```

Directly on the Fourier basis,

```text
D_N e_(-1)=-e_0,
D_N e_(N-1)=e_N,
D_N e_k=0 otherwise.                               (NO.5)
```

Therefore

```text
rank(D_N)=2,
norm(D_N)=1,
norm(D_N)_2^2=2                                    (NO.6)
```

for every `N`.

## 3. No common Hilbert--Schmidt right factor

Suppose there were a Hilbert space `K`, one Hilbert--Schmidt operator

```text
A:L^2(T)->K,                                       (NO.7)
```

and bounded operators `B_N:K->L^2(T)` satisfying

```text
D_N=B_N A,
sup_N norm(B_N)<=C<infinity.                       (NO.8)
```

Apply `(NO.8)` to the moving boundary vector `e_(N-1)`.  Equation `(NO.5)`
gives

```text
1=norm(D_N e_(N-1))
 <=C norm(A e_(N-1)).                              (NO.9)
```

Hence

```text
sum_(N>=1)norm(A e_(N-1))^2
 >=sum_(N>=1)C^(-2)
 =infinity.                                        (NO.10)
```

But the left side is at most `norm(A)_2^2`, contradicting `(NO.7)`.  Thus no
factorization `(NO.8)` exists.

The same proof applies when `A` is a fixed finite direct sum of
Hilbert--Schmidt owners: their column operator is still Hilbert--Schmidt.

## 4. Douglas readback

By Proof 360, `(NO.8)` is equivalent to a uniform positive domination

```text
D_N*D_N<=C^2 A*A.                                  (NO.11)
```

Equation `(NO.5)` shows the failure directly:

```text
<e_(N-1),D_N*D_N e_(N-1)>=1,                       (NO.12)
```

whereas the diagonal sequence

```text
<e_n,A*A e_n>=norm(A e_n)^2                        (NO.13)
```

must be summable.  A uniform Schatten norm is therefore weaker than the
common-domain Douglas inequality required by Proof 351.

## 5. Consequence for Proofs 375--380

Proofs 375--377 establish

```text
sup_j norm([C_g,P_j])_2<infinity                   (NO.14)
```

for the actual Euler-prefix endpoints.  Proof 380 identifies those
commutators as the detector side of the exact root pairing.  Proof 381 shows
that `(NO.14)` cannot, by itself, manufacture the common insertion and
alignment in Proof 380 `(RD.21)--(RD.22)`.

The next theorem must use facts absent from `(NO.2)--(NO.6)`:

```text
one fixed Burnol quotient source;
compact real-line root support;
completed outer-minus-Sonin-plus-prolate boundary localization;
causal Euler transport before the common window is inserted.    (NO.15)
```

The monomial family changes its right endpoint from `N-1` to infinity.  The
physical near route must instead prove that every active endpoint vector is
seen through Proof 357's one fixed finite boundary envelope.

## 6. Reproducible certificate

The companion finite probe truncates `(NO.2)--(NO.5)` and chooses the common
diagonal Hilbert--Schmidt approximation

```text
A e_k=(1+abs(k))^(-1)e_k.                          (NO.16)
```

For each tested `N`, the least exact left factor on the active columns has
norm

```text
norm(B_N)=N.                                       (NO.17)
```

The script checks the rank, operator norm, Hilbert--Schmidt norm, exact
factorization, and growth `(NO.17)`.

Run only after Proofs 380--384 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/381_nearly_invariant_common_owner_obstruction_probe.py
```

The finite table illustrates the exact infinite proof `(NO.9)--(NO.10)`.

## 7. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| MR.6 endpoint `S_2` theorem                   | retained                 |
| generic common-owner inference                | rejected `(NO.10)`      |
| physical boundary common owner                | still viable            |
| source-specific insertion/alignment            | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
