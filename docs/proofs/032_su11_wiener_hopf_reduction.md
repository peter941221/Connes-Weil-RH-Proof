# SU(1,1) Wiener--Hopf Reduction

Date: 2026-07-12

Status: exact operator reduction obtained. The fixed-`q` Schur conjecture is
now one explicit half-space Wiener--Hopf coefficient for a metaplectic squeeze.
The coefficient is not yet proved nonzero. RH remains unproved.

## 1. Route Obligation

```text
route obligation:
  prove the fixed-q Schur--Cayley edge asymptotic without RH

old weak path:
  finite floating-point Schur sections through degree 513

new mathematical owner:
  the Poisson kernel of one SU(1,1) squeeze, compressed to the number filtration

consumer to rewire:
  semilocal prolate Jacobi edge, then the positive cross-spectral trace

forbidden circular inputs:
  SourceRH, Weil positivity, detector coverage, zero-free conclusions

smallest verification target:
  one nonzero half-space coefficient B(q) for every q=1/p

focused axiom audit:
  none until an actual Lean analytic producer exists
```

## 2. Exact Poisson-Kernel Owner

Let `D` be the archimedean scaling generator in its cyclic
Meixner--Pollaczek basis `e_n`, and put

```text
q=1/p,  a=sqrt(q),  L=log(p),  U_p=exp(-i L D).
```

The source semilocal moment measure, including its unnormalized `1-q` factor,
is

```text
dm_p(s)
  = (1-q)/|1-a exp(-iLs)|^2 dm_infinity(s).               (W.1)
```

Source: Consani--Moscovici, arXiv:2403.01247,
`pqfile1.tex:742-786` for the Lambert moments and `1452-1456` for the local
factor measure. The factor `1-q` is forced by comparing their zeroth Lambert
moment with the bare local-factor integral; it is also the scalar Poisson
normalization.

Functional calculus turns (W.1) into the exact bounded positive operator

```text
G_p
  = (1-q)(I-a U_p)^(-1)(I-a U_p*)^(-1)
  = T_p* T_p,

T_p=sqrt(1-q)(I-a U_p*)^(-1).                            (W.2)
```

Since `U_p` is unitary and `a<1`, no domain or summability premise is hidden in
(W.2). It also gives the exact prime-power expansion

```text
G_p
  = I + sum_(r>=1) a^r (U_p^r + U_p^(-r)).               (W.3)
```

Thus all powers `p^r` already belong to the same pre-cutoff positive owner.
They do not have to appear as separate leading frequencies in one Jacobi
coefficient.

For `V_n=span(e_0,...,e_n)`, define

```text
G_(p,n)=P_n G_p P_n | V_n.
```

Then the exact determinant pivot is

```text
s_n(q)
  = det(G_(p,n))/det(G_(p,n-1))
  = dist(T_p e_n, T_p V_(n-1))^2.                        (W.4)
```

Equation (W.4) is the same Schur complement used in plan 031, but now it is
owned before matrix expansion. The density bound gives

```text
(1-a)/(1+a) I <= G_(p,n) <= (1+a)/(1-a) I                (W.5)
```

uniformly in `n`.

## 3. Exact SU(1,1) Phase

The even metaplectic representation is the lowest-weight `SU(1,1)` disk model
with monomial normalization

```text
c_n=sqrt((1/2)_n/n!)=2^(-n)sqrt(binomial(2n,n)).          (W.6)
```

This is exactly the normalization of the source vectors `eta_ell(n)` in
`pqfile1.tex:1082-1094`. The hyperbolic element `U_p^r` has disk Cayley
parameter

```text
b_r=tanh(rL/2)=(1-q^r)/(1+q^r).                          (W.7)
```

Comparing the scalar Poisson expansion (W.3) with Proposition 5.3 gives its
matrix coefficients in terms of the exact Meixner kernel from plan 030:

```text
<e_m,U_p^r e_n>
  = parity_sign * sqrt(2) q^(r/2) c_m c_n
    S_(q^(2r))(m,n).                                     (W.8)
```

The check at `m=n=0` is

```text
sqrt(2 q^r/(1+q^(2r)))=1/sqrt(cosh(rL)),
```

the cyclic matrix coefficient of the squeeze. The fixed-width Darboux
formula therefore has phase

```text
omega_(p,r)
  = pi-4 arctan(q^r)
  = 4 arctan(b_r).                                       (W.9)
```

This derives the numerical Cayley phase from the exact group element; it is
not a fitted choice of frequency.

## 4. Minimal Boundary Theorem

The required new theorem is now:

```text
there exist sigma(q)>0 and B(q) != 0 such that

log s_n(q)
  = log sigma(q)
    + n^(-1/2) Re(B(q) exp(i n omega_(p,1)))
    + O(n^(-1)).                                         (W.10)
```

Using the source identity

```text
a_n(q)^2=(n+1/2)(n+1)s_(n+1)(q)/s_n(q),                 (W.11)
```

(W.10) gives, without another determinant estimate,

```text
(a_n(q)-a_n(0))/sqrt(n)
  = 1/2 Re(
      B(q)(exp(i omega_(p,1))-1) exp(i n omega_(p,1)))
    + O(n^(-1/2)).                                       (W.12)
```

The Jacobi-wave amplitude is therefore

```text
A(q)=|B(q)| sin(omega_(p,1)/2).                          (W.13)
```

Since `0<omega_(p,1)<pi`, proving `B(q) != 0` is exactly the remaining
non-cancellation gate.

## 5. Cross-Prime Rejection Test

The same guarded computation was run through degree 513 for five primes.
Every minimum eigenvalue remains above (W.5), and fitting only the exact
frequency (W.9) gives:

```text
p    q         omega_p       amplitude    residual RMS (128..512)
2    0.500000  1.287002218   0.651350     0.01935
3    0.333333  1.854590436   0.498360     0.00863
5    0.200000  2.352010414   0.317984     0.00304
7    0.142857  2.574004435   0.229987     0.00152
11   0.090909  2.778953105   0.146908     0.00059
```

As `q` decreases, `A(q)/q` approaches the rigorous first-variation prediction

```text
2 sqrt(2/pi)=1.595769...
```

coming from `alpha_n~(-1)^n/sqrt(pi n)` and the source coefficient
`2sqrt(2)(alpha_(n+1)-alpha_n)q`. This is evidence for nonzero `B(q)` at all
prime points, not its proof.

A double-precision attempt at degree 1024 produced nonfinite hypergeometric
entries and was rejected before fitting. It is not evidence in either
direction.

## 6. Existing-Theorem Screen

The 2025 generalized Szego/Moyal determinant theorem of Fagotti--Marić
(arXiv:2406.12781) requires matrix entries that decay exponentially with
distance from the diagonal, and its computable expansion assumes slow
variation along diagonals. The squeeze matrix in (W.8) is a Fourier integral
operator with a growing boundary interaction region, not such a locally
Toeplitz matrix. That theorem cannot be cited as (W.10).

Standard strong Szego theorems likewise control Laurent/Toeplitz symbols, not
the number-filtration compression of a hyperbolic `SU(1,1)` map. No checked
source supplies (W.10). The missing analysis is a half-space semiclassical
Wiener--Hopf factorization for the squeeze canonical relation.

## 7. Nondegenerate-Crossing Attack

In oscillator action-angle coordinates, write

```text
I=(x^2+xi^2)/2,
x=sqrt(2I) cos(theta),
xi=sqrt(2I) sin(theta).
```

The classical dilation underlying `U_p` sends

```text
I'/I=e^L cos(theta)^2+e^(-L) sin(theta)^2.
```

Its canonical relation crosses the number cutoff `I'=I` at

```text
tan(theta)^2=e^L=p.                                      (W.14)
```

For every finite prime these crossings are transverse: the theta derivative
of `I'/I-1` is nonzero at (W.14). Hence each local stationary-phase symbol is
nonzero. The only remaining way to obtain `B(q)=0` is exact cancellation among
the parity-related crossing contributions; there is no degenerate stationary
point that forces zero amplitude.

Fitting (W.10) directly, rather than fitting the derived Jacobi coefficient,
gives:

```text
p    sigma(q)   Re B(q)   Im B(q)   |B(q)|
2    0.664171   1.049836   0.264130   1.082552
3    0.846967   0.616272   0.081168   0.621594
5    0.945462   0.343351   0.017626   0.343804
7    0.972534   0.239029   0.005975   0.239103
11   0.989059   0.149072   0.001048   0.149076
```

The smallest proof strategy is therefore:

```text
1. construct the two-crossing half-space parametrix;
2. prove B(q) is real-analytic for 0<q<1;
3. recover B'(0)=2sqrt(2/pi) from the source first variation;
4. use an explicit remainder bound to prove B(q)!=0 for 0<q<=q_0;
5. certify the finite set of prime points 1/p>q_0 by interval bounds on
   the same crossing formula.
```

Step 3 is already source-backed. Analyticity plus a nonzero derivative alone
only handles an unspecified neighborhood of zero; it does not justify the
small-prime cases without Step 4 or Step 5.

## 8. Verdict

```text
Poisson positive owner before cutoff: exact.
all prime powers in one owner: exact by (W.3).
Cayley phase: exact by SU(1,1), (W.7)--(W.9).
uniform inverse bound: exact by (W.5).
nonzero boundary coefficient B(q): open.
off-the-shelf Szego/Moyal closure: rejected by hypotheses.
route status: alive, with one explicit new microlocal theorem at Gate 1.
RH status: unproved.
```

The next analytic attack must construct the half-space parametrix at the two
stationary crossings of the squeeze canonical relation with the action
boundary. A proof that the two crossing symbols cancel exactly would reject
the route; a nonzero crossing sum proves (W.10) and opens the prolate trace
gate.
