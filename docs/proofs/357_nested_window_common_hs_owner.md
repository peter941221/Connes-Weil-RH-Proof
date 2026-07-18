# Proof 357: nested-window common Hilbert--Schmidt owner

Date: 2026-07-18

Status: exact continuous-kernel construction of one common Hilbert--Schmidt
input for every compact-root half-line boundary crossing whose displacement
lies in a fixed near window.  The common input is formed after boundary
localization, so it avoids Proof 259's infinite-mass obstruction for a raw
whole-line convolution root.

This closes the common-input problem for the physical half-line branches.  It
does not yet prove that Proof 355's moving quotient crossing is a contractive
image of their complete signed recombination.  Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| raw whole-line convolution root               | not Hilbert--Schmidt      |
| root after finite output restriction           | Hilbert--Schmidt, exact  |
| all near boundary windows                      | one nested envelope      |
| common source HS square                        | window length * root L2  |
| dependence on number/spacing of primes         | none                      |
| compatibility with Proof 351 common input      | physical branches only   |
| moving quotient recombination                  | open                      |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Finite-output convolution

Let `g in L2(R)` and let

```text
(C_g f)(x)=integral_R g(x-y)f(y)dy.                 (NW.1)
```

For a finite measurable interval `I`, let `R_I` be restriction from
`L2(R)` to `L2(I)`.  The operator

```text
A_(g,I)=R_I C_g                                     (NW.2)
```

has kernel

```text
k_I(x,y)=1_I(x)g(x-y).                              (NW.3)
```

Tonelli and translation invariance give the exact Hilbert--Schmidt square

```text
norm(A_(g,I))_2^2
 =integral_(x in I) integral_R abs(g(x-y))^2 dy dx
 =abs(I) norm(g)_2^2.                               (NW.4)
```

Equation `(NW.4)` requires no pointwise Fourier multiplier, smoothness, or
finite-dimensional approximation.

## 3. Nested-window factorization

If `I subset J`, restricted restriction

```text
r_(I,J):L2(J)->L2(I)                                (NW.5)
```

is a contraction and

```text
A_(g,I)=r_(I,J) A_(g,J).                            (NW.6)
```

Translations do not change the conclusion.  If `I-b subset J`, then

```text
R_I U_b C_g
 =T_(b,I) r_(I-b,J) A_(g,J),                        (NW.7)
```

where `T_(b,I)` is the unitary change of interval coordinate.  Thus every
translated restricted root whose translated output window lies in `J` is a
contractive image of the one common input `A_(g,J)`.

## 4. Near-displacement envelope

Assume

```text
supp(g) subset [-B_root,B_root],
0<=b<=L.                                            (NW.8)
```

Every output interval occurring in a completed half-line crossing at
displacement `b` is contained, after the harmless translation in `(NW.7)`,
in one fixed envelope `J_(L,B_root)` of length at most

```text
abs(J_(L,B_root))<=L+2B_root.                       (NW.9)
```

Consequently

```text
norm(A_(g,J_(L,B_root)))_2^2
 <=(L+2B_root) norm(g)_2^2.                         (NW.10)
```

The constant is independent of the number, order, and spacing of every prime
or prime power whose displacement lies in `[0,L]`.

## 5. Completed half-line crossing

For the positive half-line projection `E` and `b>=0`, the geometric crossing

```text
(I-E)U_bE                                           (NW.11)
```

is supported on a boundary interval of length `b`.  The legal compact-root
owner from Proof 330 has two Hilbert--Schmidt legs and operator product

```text
C_eta (I-E)U_bE C_xi*.                              (NW.12)
```

For every `b<=L`, both legs in `(NW.12)` factor through the fixed envelope
operators

```text
A_(eta,J_(L,B_eta)),
A_(xi,J_(L,B_xi))                                   (NW.13)
```

by interval restrictions and translations of norm at most one.  Hence one
direct-sum Julia/Bessel consumer may use `(NW.13)` as its common source data.
It must not use the raw operators `C_eta E` or `C_xi E`.

## 6. Why this avoids Proof 259

Proof 259 records, for nonzero `g`,

```text
norm(C_g E)_2^2
 =integral_(y>=0) norm(g)_2^2 dy
 =infinity.                                         (NW.14)
```

There is no contradiction with `(NW.4)`: `(NW.14)` keeps an infinite output
half-line, while `(NW.4)` applies only after the completed boundary crossing
has localized the output to a finite interval.

The legal order is

```text
complete physical boundary crossing
  -> finite output window
  -> common near envelope
  -> Hilbert--Schmidt norm.                         (NW.15)
```

Reversing the first two arrows recreates infinite mass.

## 7. Interface with Proofs 351 and 355

Proof 351 needs one common Hilbert--Schmidt source input before its weighted
range Bessel estimate.  Proof 357 supplies exactly such an input for every
physical half-line branch in the near displacement region.

What remains is a same-object factorization of the surviving Proof 355 row:

```text
(I-P_(j-1)) W P_(j-1)

 =one contraction of the completed signed sum of
   outer crossing
   -Sonin/scattering crossing
   +prolate correction
   +residue and anomaly terms,                      (NW.16)
```

with `(NW.13)` inserted only after the sum in `(NW.16)` is formed.  Proofs
260, 340, and 348 forbid assigning a separate direct-sum norm to each branch.

## 8. Arithmetic budget

The common-input square `(NW.10)` contributes one factor linear in `L` and
root support.  The Julia detector weights contribute

```text
sum_(log(p)<=L) log(p)/(p-1)<=L(1+L).               (NW.17)
```

These are polynomial budgets.  They are not multiplied until `(NW.16)`
constructs the complete contraction.  A resulting power such as
`(1+L)^d` is acceptable for Gate 3U; an exponential support factor or an
Euler condition product is not.

## 9. Reproducible certificate

The companion zero-fill Toeplitz probe uses a compact discrete convolution
kernel and output intervals strictly inside a larger input grid.  It checks

```text
the discrete analogue of `(NW.4)` exactly;
nested restriction factorization `(NW.6)`;
translated nested factorization `(NW.7)`;
one common envelope for all tested near displacements.           (NW.18)
```

Run only in the unified verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/357_nested_window_common_hs_owner_probe.py
```

The unified WSL2 run reports envelope Hilbert--Schmidt formula error
`4.689752325585e-14` and exact zero for both nested-factorization errors.

The continuous result is the direct Tonelli calculation `(NW.4)`; the probe
is an implementation certificate, not its proof.

## 10. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| finite-output convolution HS norm             | exact `(NW.4)`            |
| common nested near window                      | exact `(NW.6)--(NW.10)`   |
| physical half-line common input                | available                |
| raw whole-line root as common input             | forbidden                |
| complete moving quotient factor `(NW.16)`      | open, active bottom      |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
