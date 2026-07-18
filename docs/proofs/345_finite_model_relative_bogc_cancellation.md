# Proof 345: finite-model relative BOGC cancellation

Date: 2026-07-18

Status: exact cancellation of the geometric-mean/bulk term in the
Borodin--Okounkov formula for every finite Blaschke model-space approximant.
The normalized determinant jet is the same transported-model projection
response as Proof 343, and after division by the source response it contains
only one relative Hankel Fredholm quotient.

This proves that Proof 344's quadratic Hankel ledger has the correct algebraic
location in finite model spaces.  Passing to Burnol's fixed infinite inner
function in the continuous prime-log, root-sandwiched trace domain remains
open.  Gate 3U and RH remain unproved.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| finite Blaschke model compression             | exact source theorem      |
| transported determinant first jet             | projection response       |
| source determinant first jet                  | source response           |
| geometric-mean term in their quotient         | cancels exactly           |
| remaining finite-model owner                  | relative Hankel Fredholm  |
| Burnol singular-inner limit                   | open                      |
| continuous root-relative trace domain         | open                      |
| Gate 3U / RH                                   | open / unproved           |
+------------------------------------------------+---------------------------+
```

The finite-model chain is

```text
complete Gram-corrected projection response
  -> normalized compressed determinant jet
  -> BOGC formula
  -> geometric/bulk derivative cancels against the source jet
  -> one relative Fredholm quotient.                           (FB.1)
```

Unlike Proof 339's path corner, `(FB.1)` starts from the full endpoint
projection and differentiates back to that same scalar.

## 2. Böttcher's exact finite-model formula

Let `u` be a finite Blaschke product and let

```text
K_u=H^2 minus-orthogonal uH^2,
P_u=projection onto K_u,
Q_u=I-P_u.                                             (FB.2)
```

For a nonvanishing scalar symbol `a` in the Wiener--Krein class with canonical
factorizations

```text
a=w_- w_+=v_+ v_-,                                    (FB.3)
```

put

```text
b=v_- w_+^(-1),
c=w_-^(-1)v_+,
mathcalK(a)=H(b)H(tilde(c)).                           (FB.4)
```

Böttcher Theorem 1.1 states

```text
det T_u(a)
 =Product_(alpha in sigma(u)) G(a o mu_(-alpha))

   *det(I-Q_u mathcalK(a)Q_u)
    /det(I-mathcalK(a)),                              (FB.5)
```

where

```text
T_u(a)=P_u M_a|_(K_u).                                (FB.6)
```

Primary source, including `(FB.5)` as formula (1):

```text
Albrecht Bottcher,
Borodin--Okounkov and Szego for Toeplitz operators on model spaces,
arXiv:1307.0329, Theorem 1.1
https://arxiv.org/abs/1307.0329
```

The theorem is finite dimensional on `K_u`, while the two Fredholm
determinants in `(FB.5)` act on the ambient Hardy space.

## 3. The determinant jet is the transported projection response

Let `tau` be a bounded invertible analytic multiplier and let `w` be a real
detector symbol.  Set

```text
a_(tau,s)=|tau|^2 exp(s w),
a_(tau,0)=|tau|^2.                                    (FB.7)
```

The orthogonal projection onto `tau K_u` is

```text
P_(tau K_u)
 =M_tau P_u T_u(|tau|^2)^(-1)P_u M_(conj(tau)).        (FB.8)
```

Finite-dimensional rectangular cycling gives

```text
partial_s log det T_u(a_(tau,s))|_(s=0)
 =Tr[M_w P_(tau K_u)].                                (FB.9)
```

At `tau=1`,

```text
partial_s log det T_u(exp(sw))|_(s=0)
 =Tr[M_w P_u].                                        (FB.10)
```

Therefore the normalized relative determinant

```text
mathcalD_(u,tau,w)(s)
 :=det T_u(a_(tau,s))
   /[det T_u(a_(tau,0)) det T_u(exp(sw))]              (FB.11)
```

satisfies

```text
mathcalD_(u,tau,w)(0)=1,

partial_s log mathcalD_(u,tau,w)(s)|_(s=0)
 =Tr[M_w(P_(tau K_u)-P_u)].                           (FB.12)
```

After the fixed Hardy boundary is canceled as in Proof 342, `(FB.12)` is the
finite-model version of Proof 343 `(PN.17)`.

## 4. Exact cancellation of the geometric term

Write the geometric factor in `(FB.5)` as

```text
mathcalG_u(a)
 :=Product_(alpha in sigma(u))G(a o mu_(-alpha)).      (FB.13)
```

For each zero `alpha`,

```text
log G(a_(tau,s) o mu_(-alpha))
 =log G(|tau|^2 o mu_(-alpha))
  +s [w o mu_(-alpha)]_0.                             (FB.14)
```

The coefficient of `s` in `(FB.14)` is independent of `tau`.  Consequently,

```text
partial_s log[
 mathcalG_u(a_(tau,s))
 /(mathcalG_u(a_(tau,0))mathcalG_u(exp(sw)))
]|_(s=0)=0.                                           (FB.15)
```

This is an exact cancellation for every finite `u`, not an asymptotic strong
Szego statement.

## 5. One finite-model Fredholm owner

Define

```text
mathcalF_u(a)
 :=det(I-Q_u mathcalK(a)Q_u)
   /det(I-mathcalK(a)).                               (FB.16)
```

Substitute `(FB.5)` into `(FB.11)` and use `(FB.15)`.  The full endpoint jet
is

```text
partial_s log mathcalD_(u,tau,w)|_(0)

 =partial_s log[
    mathcalF_u(a_(tau,s))
    /(mathcalF_u(a_(tau,0))mathcalF_u(exp(sw)))
   ]|_(0).                                            (FB.17)
```

Thus the relative model response has no surviving geometric/bulk derivative.
All dependence on the Euler transport lies in the Hankel factors of
`mathcalK(a_(tau,s))`.

At `tau=1`, the source-normalizing quotient in `(FB.17)` is essential.  It
removes the detector-only Fredholm jet, just as `(FB.15)` removes the
detector-only geometric jet.

## 6. Why this earns the quadratic prime ledger

For a scalar positive symbol, the two Wiener--Hopf factorizations in `(FB.3)`
may be chosen from the positive and negative Fourier parts of `log(a)`.  The
Hankel factors in `(FB.4)` therefore depend on

```text
(log a)_--(log a)_+.                                  (FB.18)
```

Differentiating `(FB.17)` in `s` gives products with one detector Hankel leg
and one Euler Hankel leg.  A legal `S_2*S_2 -> S_1` estimate has Euler square
energy

```text
sum_(p,m) (m log p)|p^(-m/2)/m|^2,                    (FB.19)
```

which is exactly Proof 344 `(SQ.6)`.  The finite-model BOGC formula therefore
places the `p^(-m)` ledger on the correct complete determinant owner.

Equation `(FB.19)` is not yet the full estimate: differentiating the Fredholm
determinants also produces their resolvents.  Those resolvents must remain in
the relative quotient `(FB.17)` or be eliminated by a positive/compressed
metric identity.  Bounding either inverse determinant factor separately can
recreate the rejected Euler condition number.

## 7. Infinite Burnol limit

Böttcher Theorem 1.2 passes `(FB.5)` along increasing finite Blaschke products.
If the zeros satisfy the Blaschke condition, the limit retains

```text
det(I-Q_B mathcalK(a)Q_B)/det(I-mathcalK(a))           (FB.20)
```

for the limiting Blaschke product `B`.

Burnol's de Branges inner function may also contain a singular/exponential
inner factor coming from the half-plane and exponential-type geometry.  The
finite-Blaschke theorem does not by itself pass to that factor.  A valid route
limit needs:

```text
finite inner approximants u_n -> Theta_Burnol locally;
P_(u_n) -> P_Theta strongly;
root-relative Hankel products converge in S_1;
the normalized determinant jets `(FB.12)` converge;
the geometric cancellation `(FB.15)` is retained before the limit.         (FB.21)
```

Generic strong convergence of projections is not enough for determinant
convergence; the `S_1` statement in `(FB.21)` is mandatory.

## 8. Continuous prime-log guard

The source formula is written on the disk for Wiener--Krein symbols.  After
Cayley transport, the route's Euler logarithm has atomic continuous
frequencies `m log p`.  Its raw half-line commutator is not Hilbert--Schmidt.
Only the compact-root completed derivative is trace class by Proof 261.

Therefore one must not claim that `(FB.5)` applies directly to the unsmoothed
Euler symbol.  The required extension is a root-relative version of
`(FB.16)--(FB.17)` whose derivative, rather than each ambient Hankel operator,
lies in `S_1`.

Proof 344 closes the numerical/Sobolev ledger once that extension exists.
Proof 336 closes its far displacement tail.  The remaining analytic tasks are
exactly the two convergence/resolvent statements in `(FB.21)` and this
root-relative continuous extension.

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| finite-model determinant jet owner            | exact                     |
| finite-model BOGC identity                    | source-proved             |
| geometric/bulk derivative                     | cancels exactly           |
| quadratic Euler Hankel location               | exact                     |
| relative Fredholm resolvent control           | open                      |
| Burnol singular-inner/root-relative limit     | open                      |
| Proof 344 arithmetic/Sobolev ledger           | closed                    |
| Gate 3U                                        | not yet closed            |
| finite-S sign / Burnol identity / RH           | open / open / unproved    |
+------------------------------------------------+---------------------------+
```
