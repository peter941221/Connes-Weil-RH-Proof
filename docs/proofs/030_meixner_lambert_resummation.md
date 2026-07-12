# Meixner--Lambert Fixed-Q Resummation

Date: 2026-07-11

Status: exact Meixner Poisson resummation and fixed-`q` diagonal asymptotic
obtained. The q-matrix retains an `n^(-1/2)` oscillatory edge term at `q=1/2`.
Uniform Schur transfer to the Jacobi coefficient and prolate trace remain
open. RH status is unchanged.

## 1. Source Q-Matrix

For `S={infinity,p}`, put `q=1/p`. Consani--Moscovici write the normalized
Hankel perturbation as the Lambert sum of rank-one matrices

```text
A_n^+/- (q)
  = +/- 2 sqrt(2) sum_(ell>=0)
      alpha_ell q^(2ell+1)/(1-q^(2ell+1))
      |eta_ell^+/-><eta_ell^+/-|,                         (M.1)

alpha_ell=(-4)^(-ell) binomial(2ell,ell),

eta_ell(m)
  = 2^(-m)sqrt(binomial(2m,m)) p_ell(m),                  (M.2)

p_ell(m)
  = sum_(k=0)^ell 8^k binomial(m,k)binomial(ell,k)
                    /binomial(2k,k).                     (M.3)
```

Source: arXiv:2403.01247, `pqfile1.tex:1024-1094`, Proposition 5.3.

## 2. Rejected Fredholm Shortcut

For fixed `ell`,

```text
p_ell(m)=Theta(m^ell),
eta_ell(m)=Theta(m^(ell-1/4)).
```

Thus the vectors in (M.1) do not converge to vectors in ordinary `ell^2` as
`n` grows. The finite matrices do not approach a trace-class rank-one sum on
the unweighted infinite sequence space. A naive Fredholm determinant limit is
invalid.

## 3. Hidden Meixner Kernel

The polynomial in (M.3) is exactly

```text
p_ell(m) = 2F1(-m,-ell;1/2;2)
         = M_ell(m; beta=1/2, c=-1).                     (M.4)
```

It is a self-dual Meixner polynomial. DLMF 18.23.4 gives its generating
function

```text
G_m(z)
  := sum_(ell>=0) (1/2)_ell/ell! p_ell(m) z^ell
   = (1+z)^m (1-z)^(-m-1/2).                             (M.5)
```

Source: https://dlmf.nist.gov/18.23.E4

Since

```text
alpha_ell=(-1)^ell (1/2)_ell/ell!,
```

the bilinear sum needed in (M.1) is the analytically continued Meixner Poisson
kernel

```text
S_t(m,n)
  := sum_(ell>=0) alpha_ell t^ell p_ell(m)p_ell(n)

  = (1-t)^(m+n)/(1+t)^(m+n+1/2)
    2F1(-m,-n;1/2; -4t/(1-t)^2).                         (M.6)
```

The hypergeometric series terminates because `m,n` are nonnegative integers.
The signs and parameter are checked at `m=0`, where (M.6) reduces to the
linear Meixner generating function, and at `m=n=1`, where direct summation of
the first two weighted moments gives the same result. Thus every Lambert layer
has a closed finite special-function kernel.

Expanding the Lambert denominator gives

```text
q^(2ell+1)/(1-q^(2ell+1))
  = sum_(r>=1) q^r (q^(2r))^ell.                         (M.7)
```

Therefore every fixed-`q` matrix entry is a convergent sum of the explicit
Meixner Poisson kernels `S_(q^(2r))`.

## 4. Fixed-Q Diagonal Asymptotic

For `m=n=N`, Pfaff's hypergeometric transformation converts (M.6) exactly to

```text
S_t(N,N)
  = (1+t)^(-1/2) N!/(1/2)_N
    P_N^(-1/2,0)(1-8t/(1+t)^2),                          (M.8)
```

where `P_N^(-1/2,0)` is a Jacobi polynomial. Put

```text
theta_t=arccos(1-8t/(1+t)^2)=4 arctan(sqrt(t)).           (M.9)
```

The classical Darboux asymptotic for Jacobi polynomials, together with
`N!/(1/2)_N~sqrt(pi N)`, gives

```text
S_t(N,N)
  = (1-t)^(-1/2)
    cos((N+1/4)theta_t)
    + O(N^(-1)).                                         (M.10)
```

Reference: DLMF 18.15(i), https://dlmf.nist.gov/18.15

For the `r`-th Lambert layer, `t=q^(2r)`, so its exact edge frequency is

```text
theta_r(q)=4 arctan(q^r).                                 (M.11)
```

Unlike the erroneous double-weight Hadamard estimate, (M.10) is order one.
Multiplying by the two normalization factors in (M.2) gives

```text
eta-normalized diagonal layer
  = 1/sqrt(pi N(1-q^(2r)))
    cos((N+1/4)4 arctan(q^r))
    + O(N^(-3/2)).                                       (M.12)
```

The geometric coefficient `q^r` in (M.7) makes the diagonal Lambert sum
uniform in `r`. Thus the fixed-`q` q-matrix retains an oscillatory
`N^(-1/2)` boundary term. The `sqrt(N)` first Taylor correction is not merely
an artifact of expanding at `q=0`; fixed `q=1/2` still has the edge scale
needed to affect the prolate Jacobi coefficients.

## 5. What This Does And Does Not Close

The diagonal is not an isolated edge effect.  For every fixed integer
`d>=0`, a second Pfaff transformation gives the exact fixed-width identity

```text
S_t(N,N-d)
  = (1+t)^(d-1/2)/(1-t)^d
    N!/(1/2)_N
    P_N^(-1/2,-d)(1-8t/(1+t)^2).                         (M.13)
```

Here `N>=d`; in an actual `+` or `-` parity block the original polynomial
indices have the same parity, so only even offsets `d` are used.  Formula
(M.13) was checked directly against the terminating sum (M.6):

```text
(N,d,t)=(8,1,0.25):  absolute error 0
(12,2,0.10):         absolute error 1.22e-15
(20,3,0.25):         absolute error 3.60e-14
```

The fixed-parameter Darboux formula remains algebraically valid for these
Jacobi polynomials.  Since

```text
cos(theta_t/2)=(1-t)/(1+t),
```

all offset-dependent amplitude factors in (M.13) cancel, leaving

```text
S_t(N,N-d)
  = (1-t)^(-1/2)
    cos((N+1/4-d/2) 4 arctan(sqrt(t)))
    + O(N^(-1)).                                         (M.14)
```

Thus each Lambert layer produces a coherent Toeplitz-like boundary wave
across every fixed-width corner.  This rules out the easy failure mode in
which (M.12) is merely diagonal noise.  It does not rule out cancellation by
the full growing boundary row in the Schur complement.

```text
fixed-q resummation formula exists: yes, through (M.6)--(M.7).
N^(-1/2) q-matrix edge survives at fixed q: yes, by (M.8)--(M.12).
fixed-width boundary coherence: yes, by (M.13)--(M.14).
ordinary trace-class Fredholm limit: rejected.
explicit edge frequencies: 4 arctan(q^r), r>=1.
determinant-ratio asymptotic: open.
prolate cross-energy to Szego phase: open.
```

The next theorem must perform steepest descent uniformly in the Lambert index
`r`, then pass from the q-matrix kernel to the determinant ratio. This transfer
has an exact one-row reduction. Define

```text
s_n(q)=Delta_n(q)/Delta_(n-1)(q).
```

Then

```text
Delta_(n-1)Delta_(n+1)/Delta_n^2=s_(n+1)/s_n.             (M.15)
```

Writing `A_n` in its last-coordinate block, the determinant quotient is the
Schur complement

```text
s_n(q)
  = 1+A_(n,n)
    -A_(n,<n)(I+A_(<n,<n))^(-1)A_(<n,n),                 (M.16)
```

with the parity blocks treated separately. Thus no global determinant
asymptotic is needed: the owner is a boundary resolvent of the explicit
Meixner--Lambert kernel.

The boundary resolvent cannot develop a hidden small-denominator instability.
There is one normalization factor that must be retained here.  The source
moments `c(2k,p)` have the same normalized moment ratios as the bare
`|L_p|^2` measure, but their unnormalized measure is `(1-q)|L_p|^2` times the
archimedean measure.  With `a=p^(-1/2)` and `q=a^2`, the pointwise bound is

```text
(1-a)/(1+a) dm_infinity
  <= dm_(infinity,p)
  <= (1+a)/(1-a) dm_infinity.                              (M.17)
```

The factor was checked independently from the source Lambert zeroth moment
and direct Gamma integration: for `p=2,3,5,7`, the ratios between the two
unnormalized conventions are respectively `1/2,2/3,4/5,6/7=1-q`.

After conjugating both finite Gram matrices by the archimedean inverse square
root, (M.17) gives the uniform Loewner estimate

```text
(1-a)/(1+a) I
  <= D_n(0)^(-1/2) D_n(q) D_n(0)^(-1/2)
  <= (1+a)/(1-a) I.                                       (M.18)
```

Thus the inverse in (M.16), interpreted in this self-adjoint Gram
normalization, is uniformly bounded in `n`. Any surviving edge term must come
from the Meixner boundary row itself, not from a determinant zero or an
uncontrolled resolvent amplification.

The target remains

```text
Delta_(n-1)(q) Delta_(n+1)(q) / Delta_n(q)^2,
```

which owns the Jacobi coefficient. An oscillatory `s_n-1=O(n^(-1))` would give
a relative Jacobi correction of order `n^(-1)` and hence an absolute
`a_n(q)-a_n(0)=O(1)` correction. At the prolate edge `n~lambda^2`, this changes
`D^2` by `O(n)`, the same scale as the linear `lambda^2 N` edge spacing. Thus
fixed-`q` resummation need not retain the formal `sqrt(n)` Taylor growth to
remain arithmetically visible.

The geometric `q^r` factor in (M.7) makes the uniform `r`-sum plausible.
Uniform invertibility is closed by (M.18); the boundary action of the resolvent
in (M.16) is now the decisive analytic gate.

## 6. Verdict

```text
fixed-q large-degree Euler deformation: explicit at the q-matrix boundary.
edge-survival gate: passes before the Schur transfer.
route status: alive.
next attack: boundary resolvent/Schur asymptotic in (M.16).
```
