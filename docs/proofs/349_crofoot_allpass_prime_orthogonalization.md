# Proof 349: Crofoot all-pass prime orthogonalization

Date: 2026-07-18

Status: exact nonlinear orthogonalization of the complete finite Euler product
on its canonical cumulative-delay model space.  The inverse Euler multiplier
maps one inner model space onto another, so its Gram-corrected range projection
is the target model projection.  The target all-pass inner function then has an
orthogonal prime-by-prime cascade decomposition.  Arbitrarily close prime-log
delays do not form the coherent Hilbert--Schmidt block of Proof 348 on this
owner.

This is not yet Gate 3U.  Proof 343 acts on one fixed Burnol quotient `K`, while
the source space constructed here is the `S`-dependent cumulative-delay model
space `K_(Theta_S)`.  No theorem currently intertwines those two carriers while
preserving the complete outer-minus-Sonin-prolate detector response.  The
finite-`S` sign, Burnol identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| one Euler denominator                         | Crofoot multiplier        |
| complete inverse Euler product                 | model-space multiplier    |
| Gram-corrected transported projection          | exact target projection   |
| complete all-pass target                       | orthogonal prime cascade  |
| close prime-log modes in that cascade          | separated before a norm  |
| quadratic prime-power ledger                   | exact diagonal ledger     |
| Proof 348 raw localized S2 route               | still rejected            |
| identification with Proof 343 fixed K          | open, exact next bridge   |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

The new order is

```text
complete Euler denominator q_S
  -> form its all-pass inner quotient beta_S
  -> identify q_S^(-1) K_(Theta_S)=K_(beta_S)
  -> replace the full Gram inverse by P_(beta_S)
  -> split K_(beta_S) into orthogonal prime blocks
  -> only then insert the compact-root functional.               (CA.1)
```

This is the first exact continuous identity after Proof 348 which performs
nonlinear orthogonalization before a Hilbert--Schmidt norm.  It applies to a
canonical Euler carrier, not yet to the route's fixed Burnol carrier.

## 2. One atomic Crofoot factor

Work in the Hardy space of the upper half-plane.  For `z>0`, put

```text
theta_z(s)=exp(i z s).                                      (CA.2)
```

This is an atomic singular inner function.  For `0<a<1`, define its Frostman
shift and Crofoot multiplier by

```text
beta_(a,z)(s)
  =[theta_z(s)-a]/[1-a theta_z(s)],

m_(a,z)(s)
  =sqrt(1-a^2)/[1-a theta_z(s)].                      (CA.3)
```

A direct calculation gives the reproducing-kernel identity

```text
1-beta_(a,z)(s) conjugate(beta_(a,z)(t))

 =m_(a,z)(s) conjugate(m_(a,z)(t))
    [1-theta_z(s) conjugate(theta_z(t))].             (CA.4)
```

After division by the Hardy kernel denominator, `(CA.4)` says that
multiplication by `m_(a,z)` is unitary:

```text
M_m : K_(theta_z) -> K_(beta_(a,z)).                  (CA.5)
```

The scalar difference between `m_(a,z)` and the normalized Euler inverse

```text
(1-a)/[1-a theta_z]
```

does not affect a transported range or its orthogonal projection.  Thus one
Euler inverse factor is exactly a Crofoot range transport, not merely an
approximately orthogonal shift.

Primary evidence for this standard model-space transform is:

```text
Lopatto--Rochberg, Schatten-class Truncated Toeplitz Operators,
the Crofoot transform around Remark 3,
arXiv:1410.1906:
https://arxiv.org/abs/1410.1906

Crofoot, Multipliers between invariant subspaces of the backward shift,
Pacific J. Math. 166 (1994), 225--246:
https://msp.org/pjm/1994/166-2/p03.xhtml
```

Only the elementary identity `(CA.4)` is needed below.

## 3. The complete all-pass inner function

For a finite ordered prime set `S`, write

```text
a_p=p^(-1/2),
z_p=log(p),
theta_p=theta_(z_p).                                  (CA.6)
```

Define

```text
q_S=product_(p in S)(1-a_p theta_p),
Theta_S=product_(p in S)theta_p,

q_S^sharp=product_(p in S)(theta_p-a_p),
beta_S=q_S^sharp/q_S
      =product_(p in S) beta_(a_p,z_p).               (CA.7)
```

On the real boundary,

```text
q_S^sharp=Theta_S conjugate(q_S).                     (CA.8)
```

Every factor of `q_S` is bounded away from zero for fixed finite `S`.
Consequently `q_S,q_S^(-1)` belong to `H^infinity`, and `(CA.8)` proves that
`beta_S` is inner.

The scalar normalizations used in Proofs 253 and 343 do not change the range,
so their complete inverse Euler multiplier has the same range action as
`q_S^(-1)`.

## 4. Exact model-space range equality

The complete nonlinear identity is

```text
q_S^(-1) K_(Theta_S)=K_(beta_S).                     (CA.9)
```

Here equality means equality of closed sets after multiplication; it does not
claim that `M_(q_S^(-1))` is unitary in the source norm.

To prove the forward inclusion, take `f in K_(Theta_S)` and put
`g=f/q_S`.  Since `q_S^(-1) in H^infinity`, one has `g in H^2`.  For every
`h in H^2`, use `(CA.8)`:

```text
<g,beta_S h>

 =integral (f/q_S) conjugate(beta_S h)
 =integral f conjugate(Theta_S h/q_S)
 =0.                                                  (CA.10)
```

Thus `g in K_(beta_S)`.  Conversely, if `g in K_(beta_S)`, put `f=q_S g`.
For every `h in H^2`, test the beta-orthogonality with `q_S h`:

```text
<f,Theta_S h>
 =<g,beta_S(q_S h)>
 =0.                                                  (CA.11)
```

Hence `f in K_(Theta_S)`, proving `(CA.9)`.

Let `P_Theta` and `P_beta` be the corresponding orthogonal projections.  The
canonical frame projection onto the left side of `(CA.9)` is therefore

```text
M_(q_S^(-1)) P_Theta
 [P_Theta M_(|q_S|^(-2))P_Theta]^(-1)
 P_Theta M_(conjugate(q_S)^(-1))

 =P_beta.                                             (CA.12)
```

Equation `(CA.12)` is exactly the Gram-corrected formula used by Proof 343,
but on the cumulative-delay carrier.  The inverse is not estimated: it is
consumed by the exact range identification.

The general multiplier relation between model spaces is also discussed in:

```text
Camara--Carteiro--Ross, Multipliers and equivalences between
Toeplitz kernels, arXiv:2307.05453:
https://arxiv.org/abs/2307.05453
```

The proof `(CA.10)--(CA.11)` is included so that no external multiplier theorem
is being used as a stored route premise.

## 5. Orthogonal prime cascade

For two inner functions `alpha,gamma`, the standard model-space product
identity is

```text
K_(alpha gamma)=K_alpha orthogonal-direct-sum alpha K_gamma.  (CA.13)
```

Iterating `(CA.13)` gives

```text
K_(Theta_S)
 =orthogonal-sum_(p in S)
   Theta_(<p) K_(theta_p),

K_(beta_S)
 =orthogonal-sum_(p in S)
   beta_(<p) K_(beta_(a_p,z_p)).                     (CA.14)
```

The ordering may be arbitrary but must be the same in the prefix products.
By `(CA.5)`, every target atomic block is a Crofoot-unitary image of the
corresponding delay block.

At the reproducing-kernel level the second equality is the telescoping identity

```text
1-beta_S(s)conjugate(beta_S(t))

 =sum_(p in S)
   beta_(<p)(s)conjugate(beta_(<p)(t))
   [1-beta_p(s)conjugate(beta_p(t))].                 (CA.15)
```

Equations `(CA.12)--(CA.15)` are the promised nonlinear orthogonalization.
The prime blocks are orthogonal before any Schatten norm is taken.  Their
separation does not depend on a lower bound for
`|log(p)-log(q)|`; hence the short-cluster coherence in Proof 348 `(PC.13)` is
not present in this owner.

## 6. Exact quadratic ledger

The logarithm of the same complete denominator is

```text
log(q_S)
 =-sum_(p in S)sum_(m>=1)
    p^(-m/2) theta_p^m/m.                            (CA.16)
```

The displacement of `theta_p^m` is `m log(p)`.  Unique factorization makes
these positive frequencies distinct.  Therefore the scalar half-Sobolev
cocycle is diagonal:

```text
mathcalE_S
 =sum_(p in S)sum_(m>=1)
    [m log(p)] |p^(-m/2)/m|^2

 =sum_(p in S) log(p)[-log(1-p^(-1))].               (CA.17)
```

With a displacement cutoff, `(CA.17)` is exactly Proof 344 `(SQ.6)`.  The
all-pass model does not by itself prove that Proof 343's detector derivative is
bounded by `(CA.17)`.  It does identify a continuous complete-product carrier
where the Gram inverse and prime orthogonalization occur in the required order.

## 7. Same-cluster audit

The companion probe reuses Proof 348's clusters

```text
X<=p<=(1+epsilon)X.                                  (CA.18)
```

It reports three quantities:

```text
raw Gram:
  the coherent compact-root S2 square from Proof 348;

cascade ledger:
  sum_p log(p)[-log(1-p^(-1))];

one-channel whitening guard:
  raw_Gram/(1+raw_Gram).                              (CA.19)
```

The last value is only the scalar Gram normalization of one fully coherent
leakage channel.  It is not the Gate response.  It records algebraically why a
large pre-Gram crossing does not authorize a large post-Gram projection.

The default WSL2 run gives, at `X=10^6`, approximately

```text
raw coherent Gram       =665.296,
all-pass cascade ledger =0.09536,
one-channel whitening   =0.99850.                    (CA.20)
```

Thus the same cohort has an exploding prematurely localized norm and a bounded
complete-product diagonal ledger.  Equations `(CA.9)--(CA.15)`, not the scalar
guard in `(CA.19)`, supply the exact nonlinear mechanism.

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/349_crofoot_allpass_prime_orthogonalization_probe.py
```

## 8. Why this does not yet apply to Proof 343

Proof 343 owns the fixed source quotient

```text
K=Ran(I-Q) minus-orthogonal Ran(R),                   (CA.21)
```

and transports it by the one-sided quotient Euler operator `A_S`.  In
contrast, `(CA.9)` starts from

```text
K_(Theta_S),
Theta_S(s)=exp(i s sum_(p in S)log(p)),               (CA.22)
```

whose Paley--Wiener length grows with `S`.  These carriers are not equal, and
no existing route theorem identifies one as a detector-compatible dilation or
compression of the other.

In particular, it is invalid to write

```text
Proof 343 K = K_(Theta_S),

or

P_(A_S K)-P_K =P_(beta_S)-P_(Theta_S).                (CA.23)
```

The missing bridge must preserve all of the following before an absolute
value:

```text
the fixed Burnol quotient frame U_0;
the complete Euler product q_S^(-1);
the outer-minus-Sonin-prolate detector bracket;
Proof 335's half-density cancellation;
Proof 336's far-tail subtraction;
the ordinary root-sandwiched trace owner.             (CA.24)
```

A generic contractive compression is insufficient because Proofs 254 and 340
show that it can lose the shorting defect and the boundary trace anomaly.

There is also a direct mean-type obstruction.  Let `Theta_B` be any fixed
nonzero upper-half-plane inner function.  Its canonical factorization has a
finite exponential factor `exp(i sigma_B s)`, and its mean type is
`-sigma_B`.  On the real boundary,

```text
Theta_B conjugate(q_S)/q_S                         (CA.24a)
```

could define an inner function only if `Theta_B conjugate(q_S)` has a bounded
analytic continuation.  The largest negative frequency of
`conjugate(q_S)` is

```text
D_S=sum_(p in S)log(p),                              (CA.24b)
```

with nonzero coefficient `product_p(-p^(-1/2))`.  Along the positive imaginary
axis that term grows like `exp(D_S y)`, while the fixed inner exponential can
cancel at most `exp(-sigma_B y)`.  Therefore `(CA.24a)` is not bounded analytic
once `D_S>sigma_B`.

The mean-type/canonical-factor statement is recorded, for example, in:

```text
Mitkovski--Poltoratski, Polya sequences, Toeplitz kernels and gap theorems,
Section 1.2, arXiv:0903.4499:
https://arxiv.org/abs/0903.4499
```

Thus no fixed scalar Burnol inner function can absorb every cumulative Euler
delay.  The bridge in `(CA.25)` must be a dilation, a vector-valued cascade, or
an equivalent completed determinant-line compression.  It cannot be the
direct scalar replacement

```text
Theta_B ->Theta_B conjugate(q_S)/q_S.                (CA.24c)
```

## 9. Corrected next theorem

The next viable producer is now concrete.  Construct a source-owned dilation
from Proof 343's fixed quotient response to the relative all-pass cascade such
that

```text
Tr[W(P_(A_S K)-P_K)]

 =one completed, detector-compatible compression of
   Tr[W(P_(beta_S)-P_(Theta_S))],                     (CA.25)
```

or prove an equivalent vector-valued determinant-line identity.  The
compression in `(CA.25)` must retain `(CA.24)` and be contractive only after the complete
signed bracket is formed.  Once such an identity exists, `(CA.14)` supplies
prime orthogonality, `(CA.17)` supplies the square ledger, and Proof 336 supplies
the far tail.

## 10. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| complete Euler all-pass inner                  | explicit                  |
| inverse multiplier model-space range           | exact `(CA.9)`            |
| Gram inverse on cumulative-delay carrier       | eliminated `(CA.12)`      |
| prime cascade orthogonality                     | exact `(CA.14)`           |
| Proof 348 close-frequency obstruction there    | avoided before S2         |
| fixed Burnol quotient -> cascade bridge         | open, active near bottom |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
