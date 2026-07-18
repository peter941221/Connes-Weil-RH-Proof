# Proof 344: relative Szego quadratic ledger

Date: 2026-07-18

Status: unconditional closure of the near Euler logarithm's quadratic
prime-power ledger, together with a source audit of model-space Szego and
Borodin--Okounkov formulas.  The ledger has the required polynomial support
cost and uses no prime number theorem.  No available theorem identifies its
quadratic norm with Proof 343's complete root-sandwiched relative determinant
derivative.

Thus the arithmetic half of a relative Szego estimate is closed, while the
same-object operator theorem remains open.  Gate 3U, the finite-S sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| endpoint Euler logarithm                       | exact prime-power series  |
| near H^(1/2) energy                            | exact square ledger       |
| uniform finite-S arithmetic bound              | <=L(1+L)                 |
| PNT / RH input                                 | none                      |
| compact-root Sobolev ledger                    | polynomial                |
| Hardy strong Szego formula                     | source theorem            |
| finite model-space BOGC formulas               | source theorems           |
| Proof 343 relative-owner identification        | absent                    |
| Gate 3U / RH                                   | open / unproved           |
+------------------------------------------------+---------------------------+
```

The viable mechanism is

```text
complete relative determinant
  -> cancel the Hardy/bulk channel before a norm
  -> one quadratic Hankel/Szego energy
  -> p^(-m/2) is squared to p^(-m)
  -> elementary logarithmic counting gives polynomial support cost.   (SQ.1)
```

Only the last three arrows of `(SQ.1)` are proved here.  The first two arrows
are the remaining same-object theorem and may not be assumed from analogy.

## 2. Endpoint Euler logarithm

Use Proof 253's normalized endpoint transport.  Scalar normalization does not
affect a projection or a relative determinant derivative which kills
constants.  For one prime write

```text
a_p=p^(-1/2),
ell_p=log(p).                                           (SQ.2)
```

On the real Mellin line,

```text
log(1-a_p exp(-i ell_p s))
 =-sum_(m>=1) a_p^m exp(-i m ell_p s)/m.               (SQ.3)
```

Therefore the positive-frequency coefficient at displacement

```text
z_(p,m)=m ell_p                                        (SQ.4)
```

has magnitude

```text
c_(p,m)=p^(-m/2)/m.                                    (SQ.5)
```

Unique factorization implies that two prime-power frequencies in `(SQ.4)`
coincide only when both the prime and exponent coincide.  There are no hidden
cross terms in the atomic quadratic ledger.

## 3. Exact near quadratic energy

Let `L>=0` be a displacement cutoff.  The continuous strong-Szego
`H^(1/2)` weight is the displacement `z`.  Hence the near energy is

```text
mathcalE_S(L)
 :=sum_(p in S) sum_(m>=1, m log(p)<=L)
     (m log(p)) |p^(-m/2)/m|^2

  =sum_(p in S) sum_(m>=1, m log(p)<=L)
     log(p) p^(-m)/m.                                 (SQ.6)
```

This is the desired half-power-to-full-power conversion.  It occurs only
after the complete logarithm has entered a quadratic determinant/Hankel
quantity.  Squaring prime channels before identifying that owner would repeat
the invalid ledger rejected in Proof 269.

## 4. Elementary uniform bound

Every prime occurring in `(SQ.6)` satisfies `p<=exp(L)`.  Dropping the
exponent cutoff and summing the geometric logarithm gives

```text
mathcalE_S(L)
 <=sum_(p<=exp(L)) log(p)
      sum_(m>=1) p^(-m)/m

 =sum_(p<=exp(L)) log(p)[-log(1-p^(-1))].             (SQ.7)
```

For `p>=2`,

```text
-log(1-p^(-1))<=1/(p-1).                              (SQ.8)
```

Enlarge primes to all integers and put `N=floor(exp(L))`.  Then

```text
mathcalE_S(L)
 <=sum_(2<=n<=N) log(n)/(n-1)
 <=L sum_(1<=k<N) 1/k
 <=L(1+L).                                            (SQ.9)
```

Equation `(SQ.9)` is uniform in the finite set `S`.  It uses only the
elementary harmonic-sum estimate and does not use Chebyshev, the prime number
theorem, a zero-free region, or RH.

For the Gate near/far split from Proof 336, take

```text
L=4B_correlation+4<=8B_root+4.                        (SQ.10)
```

Thus `(SQ.9)` costs `O((1+B_root)^2)`.

## 5. Compact-root ledger

For roots `eta,xi` supported in `[-B_root,B_root]`, their cross-correlation

```text
phi=xi^star*eta                                        (SQ.11)
```

is supported in `[-2B_root,2B_root]`.  For every fixed derivative order `j`,
Young and Cauchy--Schwarz give

```text
norm(partial^j phi)_infinity
 <=norm(xi)_2 norm(partial^j eta)_2,                  (SQ.12)

norm(partial^j phi)_1
 <=4B_root norm(xi)_2 norm(partial^j eta)_2.          (SQ.13)
```

The same estimates with derivatives split between the two roots give, for
`Q=-partial^2+1/4`,

```text
norm(Q phi)_(W^(k,1))
 <=C_k(1+B_root)
   norm(xi)_(H^(k+2)) norm(eta)_(H^(k+2)).            (SQ.14)
```

Hence every fixed Besov/Sobolev norm of the compact detector required by a
valid relative determinant theorem has polynomial support cost.  The root
side is not the obstruction.

## 6. What the model-space literature proves

Burnol proves that the completed Mellin image of the source Sonin space is the
de Branges space `B(E_lambda)`:

```text
Burnol, Sur les espaces de Sonine associes par de Branges a la
transformation de Fourier, Theorem 8, arXiv:math/0208121
https://arxiv.org/abs/math/0208121
```

After division by its Hermite--Biehler generator, an abstract de Branges space
has a standard Hardy model-space representation.  This fact alone does not
transport Proof 343's compact-root detector and Euler quotient action to the
standard truncated-Toeplitz symbols with their support ledger.

The closest determinant source is

```text
Bottcher, Borodin--Okounkov and Szego for Toeplitz Operators on
Model Spaces, IEOT 78 (2014), 407--414
https://doi.org/10.1007/s00020-013-2118-5
```

Its stated contract concerns determinants of compressions to
finite-dimensional model spaces and their asymptotics.  The later trace-type
results also concern increasing finite Blaschke model spaces:

```text
Strouse--Timotin--Zarrabi,
A Szego type theorem for truncated Toeplitz operators,
arXiv:1702.08147
https://arxiv.org/abs/1702.08147

Miheisi, Szego Limit Theorem for Truncated Toeplitz Operators (2025)
https://doi.org/10.1007/s00020-025-02793-y
```

None of these statements supplies a fixed infinite Burnol-space relative
determinant derivative, a continuous prime-log almost-periodic symbol, or
Proof 261's root-sandwiched trace domain.

Carey--Pincus treats Steinberg symbols modulo the ambient trace class:

```text
Carey--Pincus, Steinberg symbols modulo the trace class, holonomy,
and limit theorems for Toeplitz determinants,
https://doi.org/10.1090/S0002-9947-05-03858-4
```

The route has fixed-S trace legality only after compact-root completion.  Its
raw continuous Euler/half-line commutators are not ambient trace class, so the
Carey--Pincus quotient cannot be imported before constructing a root-relative
version.

## 7. Exact missing owner theorem

Let `tau_S` be the complete normalized Euler multiplier and let
`W_(eta,xi)=C_xi* C_eta`.  A sufficient successor to Proof 343 must construct
one relative determinant `D_S(s)` satisfying

```text
partial_s log D_S(s)|_(s=0)
 =Tr[W_(eta,xi)(P_(A_SK)-P_K)]                       (SQ.15)
```

for the literal `K,A_S` of Proof 343, and then factor it as

```text
D_S(s)
 =exp(quadratic Szego cocycle of log(tau_S) and sW)
   det(I+root-relative Hankel remainder).              (SQ.16)
```

The factorization must have all of the following properties:

```text
same fixed Burnol quotient carrier;
complete finite-S Euler product before expansion;
root-sandwiched, not ambient, trace domain;
fixed-boundary/Hardy bulk cancellation built in;
Proof 335 half-density residue cancellation retained;
remainder norm controlled by the same quadratic ledger `(SQ.6)`;
Proof 336 far tail inserted before the final absolute value.       (SQ.17)
```

If `(SQ.15)--(SQ.17)` are proved, `(SQ.9)` and `(SQ.14)` give the polynomial
near bound, while Proof 336 gives the far bound.  That would close Gate 3U.

At present no cited theorem has contract `(SQ.17)`.  Naming `(SQ.16)` without
constructing it would be another stored premise.

## 8. Reproducible arithmetic certificate

The companion script evaluates `(SQ.6)` for several prime cutoffs and checks
the elementary bound `(SQ.9)`.  It tests the arithmetic ledger only and makes
no operator-theoretic claim.

Run without a Lean build:

```text
python3 -B docs/proofs/344_relative_szego_quadratic_ledger_probe.py
```

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| near quadratic Euler ledger                   | closed unconditionally    |
| compact-root Sobolev ledger                    | closed                    |
| fixed-S model-space asymptotic sources         | real but wrong contract   |
| root-relative BOGC identity `(SQ.15)--(SQ.17)` | open, exact Gate 3U owner |
| Proof 336 far lane                             | already closed            |
| Gate 3U                                        | not yet closed            |
| finite-S sign / Burnol identity / RH           | open / open / unproved    |
+------------------------------------------------+---------------------------+
```
