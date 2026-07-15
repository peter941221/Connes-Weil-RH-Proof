# Proof 263: Endpoint response distribution

Date: 2026-07-15

Status: exact reformulation and survivor diagnostic, not Gate 3U.  Proof 262's
endpoint scalar is a Hermitian response form on pairs of compact roots.  It
factors through their compactly supported cross-correlation, but it must not be
defined pointwise as `Tr(U_z(B_S-B))`: the raw translated projection difference
need not be trace class.  The correct infinite-dimensional object is a
factorized response distribution.

A new Hermite whole-line probe removes periodic wraparound and prime-log grid
rounding.  It verifies the endpoint two-commutator identity and keeps the
complete Euler product whole by orthonormalizing after each local factor.  Its
localized responses stay order one through `p<=10000`, but the results are not
converged across Hermite sizes.  More importantly, the sharp second-support
invariance has an order-one finite-section residual, so these values are
survivor diagnostics only.

The same probe gives an explicit negative ordered minor for the `p=2,3`
two-sided geometric kernel.  Total positivity on the incommensurate prime-log
group is false.  The next proof must use the one-sided causal factorization of
`T_S^-1` and the exact source half-line orientation, not a symmetric Markov or
Pólya-frequency shortcut.  Gate 3U, the same-object arithmetic identity,
Burnol's explicit formula in Lean, and RH remain open.  No Lean owner or route
consumer is changed.

## 1. Result first

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| fixed-S trace legality                         | closed by Proof 261          |
| endpoint two-commutator formula                | exact by Proof 262           |
| compact-root sesquilinear response             | exact owner                  |
| factorization through cross-correlation        | exact                        |
| raw point response Tr(U_z(B_S-B))              | not generally legal          |
| full C_c-infinity distribution extension       | unnecessary and unproved     |
| non-periodic Hermite response screen           | survivor, not converged      |
| finite-section Q-invariance                    | fails in operator norm        |
| prime-log total-positivity shortcut            | rejected by negative minor   |
| one-sided causal boundary estimate             | open, active successor       |
| Gate 3U                                        | open                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

## 2. The legal response owner

Let `E` be the outer source support, `R<=E` the Sonin projection, and

```text
B=E-R,
B_S=the transported finite-S band projection.                  (Z.1)
```

For compact smooth roots `eta,xi`, let `C_eta,C_xi` be their whole-line
convolution operators.  Proof 261 gives

```text
C_eta(B_S-B)C_xi* in S1.                                     (Z.2)
```

Define the fixed-S endpoint response by the ordinary trace

```text
Q_S(eta,xi)
 :=Tr(C_eta(B_S-B)C_xi*).                                    (Z.3)
```

This is sesquilinear in the two roots.  Since `B_S-B` is self-adjoint,

```text
Q_S(xi,eta)=conj(Q_S(eta,xi)).                               (Z.4)
```

The route detector is the diagonal value

```text
Q_S(g,g)=Tr(C_g(B_S-B)C_g*).                                 (Z.5)
```

Ordinary cyclicity is legal by `(Z.2)`.  Hence

```text
Q_S(eta,xi)
 =Tr(C_xi* C_eta(B_S-B)).                                    (Z.6)
```

The multiplier `C_xi* C_eta` is convolution by the compactly supported
cross-correlation

```text
F_(eta,xi)=xi^star*eta,

supp(F_(eta,xi))
 subset supp(eta)-supp(xi).                                  (Z.7)
```

Thus `(Z.3)` depends on the two roots only through `(Z.7)`.  If both roots are
supported in `[-B_root,B_root]`, then

```text
supp(F_(eta,xi)) subset [-2B_root,2B_root].                   (Z.8)
```

Equations `(Z.2)--(Z.8)` are the exact coefficientization needed by Gate 3U.
They do not assert that the unsmoothed operator `U_z(B_S-B)` is trace class.

## 3. Why the pointwise kappa notation is dangerous

In a finite-dimensional model one may define

```text
kappa_(N,S)(z)=Tr(U_z(B_(N,S)-B_(N,0))).                     (Z.9)
```

Then a convolution detector pairs with `(Z.9)` by integrating its kernel in
`z`.  In the source Hilbert space, however, Proof 261 proves only the
root-sandwiched trace-class statement `(Z.2)`.  Proof 260 already gives compact
zero-diagonal examples which are not trace class.  Therefore the expression

```text
kappa_S(z)=Tr(U_z(B_S-B))                                    (Z.10)
```

is not a licensed infinite-dimensional definition.

The legal object is the factorized functional

```text
Lambda_S(F_(eta,xi)):=Q_S(eta,xi).                           (Z.11)
```

It is enough for the route because every selected detector is a Hermitian
convolution square.  Extending `(Z.11)` to all of `C_c^infinity(R)` would need
a quantitative compact-support convolution factorization, for example a
support-controlled Dixmier--Malliavin theorem.  Gate 3U does not require this
stronger statement, so it must not become a new premise.

Primary factorization context:

```text
M. Francis, A Dixmier--Malliavin theorem for Lie groupoids
https://arxiv.org/abs/2009.13760
```

That source records the qualitative finite convolution-sum theorem.  It does
not supply the polynomial support/Sobolev constant required here.

## 4. Exact Gate 3U norm contract

For a support radius `B_root` and Sobolev order `r`, put

```text
H_(B_root)^r
 ={g in H^r(R): supp(g) subset [-B_root,B_root]}.             (Z.12)
```

The response `(Z.3)` is a Hermitian form on `(Z.12)`.  The active theorem can
be stated without a raw distribution:

```text
|Q_S(eta,xi)|
 <=C (1+B_root)^d
      ||eta||_(H^r) ||xi||_(H^r),                            (Z.13)
```

for all finite `S`, with `C,d,r` independent of `S`.

For `eta=xi=g`, `(Z.13)` is Proof 262's Gate 3U contract.  Conversely, a
uniform diagonal bound for `Q_S(g,g)` gives `(Z.13)` by complex polarization:

```text
Q_S(eta,xi)
 =1/4 sum_(k=0)^3 i^k
    Q_S(eta+i^k xi,eta+i^k xi).                              (Z.14)
```

All four roots in `(Z.14)` remain in the same support window.  Therefore the
diagonal detector theorem and the bounded Hermitian-form theorem are
equivalent up to a fixed polarization constant.  This is the correct local
functional-analytic owner for the causal path proof.

## 5. Endpoint two-commutator form for cross roots

Let

```text
W_(eta,xi)=C_xi* C_eta.                                      (Z.15)
```

It commutes with the complete Euler multiplier.  Proof 262's algebra is linear
in `W`, so the endpoint formula extends from the Hermitian square to `(Z.15)`:

```text
Q_S(eta,xi)
 =Tr_B(mathcalD_S*
   (C_0[W_(eta,xi),E]B
      -[W_(eta,xi),R]R L_S)).                               (Z.16)
```

Using

```text
R=E E_hat E-K_prol,                                         (Z.17)
```

every detector commutator in `(Z.16)` is an outer crossing, a
scattering-conjugate second crossing, or a prolate commutator.  Equation
`(Z.8)` must be applied before the coframe and graph are expanded.

The required order remains

```text
cross-root factorization
  -> outer-minus-Sonin bracket
  -> compact displacement support
  -> common causal path law
  -> absolute value.                                        (Z.18)
```

## 6. Non-periodic Hermite whole-line probe

The new probe uses normalized Hermite functions on the real line.  Gauss--
Hermite quadrature gives a unitary nodal transform, and the Fourier transform
is diagonal in the Hermite basis.  Therefore

```text
U_b=F* M_(exp(-i b xi)) F                                   (Z.19)
```

uses the literal real displacement `b`; `log(p)` is never rounded.  The source
scattering is

```text
mathcalS=F* M_(u_infinity) F.                               (Z.20)
```

There is no periodic spatial wraparound.

For every prime, the model updates the outer and Sonin columns by

```text
columns <- qr((I-p^(-1/2)U_(log p)) columns).                (Z.21)
```

QR changes the basis but not its range.  Applying it after every local factor
keeps the complete Euler product whole without forming its exponentially
conditioned matrix.

At size `64`, `S={p<=11}`, and displacements
`-2,-1/2,1/2,2`, the direct endpoint response and `(Z.16)` agree with maximum
relative error below `1e-12`.  The detector commutes with the complete
transport to the same precision.

The default response cohort uses `z in [-4,4]`:

```text
+------+-------+-------+--------+---------+----------+
| size | band  | p<=   | primes | max|k|  | local L2 |
+------+-------+-------+--------+---------+----------+
|   64 |     9 |    11 |      5 | 0.6832  | 1.3136   |
|   64 |     9 |   997 |    168 | 1.3284  | 1.9689   |
|   64 |     9 | 10000 |   1229 | 3.9674  | 4.6575   |
|   96 |    12 |    11 |      5 | 0.6992  | 1.0021   |
|   96 |    12 |   997 |    168 | 1.0225  | 1.2918   |
|   96 |    12 | 10000 |   1229 | 2.3708  | 3.5267   |
|  128 |    12 |    11 |      5 | 1.1023  | 1.3004   |
|  128 |    12 |   997 |    168 | 2.9141  | 3.3780   |
|  128 |    12 | 10000 |   1229 | 3.3663  | 3.7999   |
|  160 |    12 |    11 |      5 | 0.4873  | 0.5490   |
|  160 |    12 |   997 |    168 | 1.6203  | 2.7698   |
|  160 |    12 | 10000 |   1229 | 2.5547  | 2.8962   |
+------+-------+-------+--------+---------+----------+
```

The response at `z=0` is below `1e-12` in every cohort.  This is the exact
finite-rank identity

```text
Tr(B_(N,S)-B_(N,0))=0.                                     (Z.22)
```

The data show no prime-count growth comparable to `sum p^(-1/2)`, but they are
not converged in the Hermite size and cannot establish `(Z.13)`.

## 7. Sharp-boundary finite sections remain polluted

The source orientation has an exact invariant support half-line.  In the
Hermite finite sections the first Euler factor has residual

```text
||(I-Q_N)(I-2^(-1/2)U_(log 2))Q_N|| approximately 2^(-1/2). (Z.23)
```

The value remains order one as the Hermite size increases from `64` to `160`.
This is not a contradiction to source invariance.  A sharp half-line and a
translation do not converge in operator norm under global spectral truncation.

Consequences:

```text
the response cohort is a survivor diagnostic;
it is stronger than a periodic FFT screen because it has no wraparound;
it still cannot prove or reject the source Gate 3U estimate;
larger Hermite sections are not the next mathematical action.             (Z.24)
```

The next proof must use exact one-sided support algebra before any finite
section.

## 8. Total positivity is false on the prime-log group

For `p=2,3`, identify a prime-log point with `(n,m)` at real position

```text
x(n,m)=n log(2)+m log(3).                                   (Z.25)
```

The product two-sided geometric kernel, up to a positive normalization, is

```text
K((n,m),(n',m'))
 =2^(-|n-n'|/2)3^(-|m-m'|/2).                              (Z.26)
```

Choose the ordered pairs

```text
x_1=(3,-4) < x_2=(-4,1),
y_1=(-4,1) < y_2=(4,-4),                                   (Z.27)
```

where the inequalities use `(Z.25)`.  Direct substitution gives

```text
det [K(x_i,y_j)]_(i,j=1)^2
 =-0.707084047558... <0.                                   (Z.28)
```

Hence `(Z.26)` is not even totally positive of order two on the real ordering.
Each one-prime geometric sequence may be Pólya frequency on its own lattice;
that property does not survive the incommensurate embedding generated by
`log(2),log(3)`.

This rejects the proposed shortcut

```text
symmetric Markov convolution
  -> total positivity
  -> variation-diminishing Schur complement.                (Z.29)
```

The surviving probability route must use the one-sided causal inverse

```text
Ttilde_S^(-1)
 =E[U_(sum_p N_p log(p))],
P(N_p=n)=(1-p^(-1/2))p^(-n/2),                              (Z.30)
```

whose paths are monotone in the actual source half-line orientation.

Total-positivity context, not a route producer:

```text
Belton--Guillot--Khare--Putinar,
Preservers of totally positive kernels and Pólya frequency functions
https://arxiv.org/abs/2110.08206
```

## 9. Reproduction

Run from the Windows source snapshot in WSL2:

```text
OPENBLAS_NUM_THREADS=4 python3 -B \
  docs/proofs/263_endpoint_response_distribution_probe.py
```

The script fails if:

```text
the Hermite/Fourier/scattering algebra exceeds tolerance;
the endpoint two-commutator identity exceeds tolerance;
the finite-rank response at zero is nonzero;
the response loses Hermitian symmetry;
the ordered prime-log minor is no longer strictly negative.               (Z.31)
```

The response magnitudes and the finite-section invariance residual are printed
as diagnostics and are not acceptance assertions.

## 10. Route judgment

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| compact-root response Q_S(eta,xi)              | exact and trace legal        |
| cross-correlation support factorization        | exact                        |
| diagonal/bilinear Gate 3U equivalence          | exact by polarization        |
| raw translation-response trace                 | forbidden in source space    |
| non-periodic exact-log finite section          | implemented                  |
| endpoint two-commutator finite check           | passes                       |
| response growth through p<=10000               | order one, not converged     |
| finite-section sharp Q-invariance              | polluted in operator norm    |
| prime-log total positivity                     | false by explicit minor      |
| exact causal stopped-path representation       | open, next bottom            |
| uniform polynomial response bound              | open, Gate 3U                |
| same-object finite-S arithmetic identity       | open                         |
| Burnol explicit formula in Lean                | open                         |
| Lean owner or route rewire                     | none                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

Proof 263 makes the legal analytic target smaller and rejects two tempting
overstatements: a raw pointwise response trace and prime-log total positivity.
Finite-section enlargement cannot close the remaining theorem.  The active
successor is an exact one-sided causal representation of `(Z.16)` which keeps
the outer-minus-Sonin bracket on one monotone path before taking an absolute
value.
