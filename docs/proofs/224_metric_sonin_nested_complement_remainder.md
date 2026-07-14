# Proof 224: metric-Sonin nested-complement remainder

Date: 2026-07-14

Status: exact same-object global trace reduction and reproducible finite-matrix
certificate.  The direct metric Sonin trace is now split into Proof 222's
complete prime-power series and one canonically defined nested-complement
remainder.  The remainder has an explicit Schur-complement owner and an exact
Mellin-diagonal/Berezin-flow formulation.  A sharp high-energy decay statement
for one named residual symbol is sufficient for its post-`Q` compactness, while
a nonzero stable or periodic tail rejects compactness.  That decay/tail verdict
and the final three-row sign are not proved here.  No Lean owner is authorized,
and RH remains unproved.

## 1. Why another operator is needed

Proof 222 computes the relative metric projection for the half-line boundary:

```text
Tr(C_F(P_a-P))
 =-L sum_(m>=1) a^m [F(mL)+F(-mL)],
a=p^(-1/2), L=log(p).                                  (N.1)
```

Proof 223 shows that one cannot finish by moving CC20's positive prolate angle
correction to finite `S`.  The finite Euler angle and the half-line metric
projection differ by a central term whose post-`Q` form grows quadratically.

The remaining calculation must therefore use the full Sonin projection
directly.  The point of this record is that the required remainder is not an
arbitrary difference and is not CC20's `K_prol`.  It is forced by one nested
projection identity.

Primary source inputs are:

```text
CC20, https://arxiv.org/abs/2006.13771
  weil-compo.tex:1072-1076   Sonin/angle spectral decomposition
  weil-compo.tex:1132-1186   positive Sonin trace and epsilon remainder
  weil-compo.tex:1194-1421   post-Q Sonin compact-form calculation
  weil-compo.tex:2105-2120   smoothed boundary commutators

CCM24 v2, https://arxiv.org/abs/2310.18423
  mainc2m24fine.tex:946-981   finite Euler multiplier
  mainc2m24fine.tex:983-1029  bounded Sonin isomorphism
  mainc2m24fine.tex:1031-1073 common de Branges vector space, changed norm

Burnol, https://arxiv.org/abs/math/0208121
  equations (1)-(2)           de Branges evaluation kernel
  Theorems 8-9                explicit Sonin structure function and endpoint
```

## 2. Abstract nested metric projections

Let `R` and `E` be orthogonal projections on one Hilbert space with

```text
Ran(R) subset Ran(E).                                  (N.2)
```

For the one-prime Euler multiplier put

```text
T_a=I-aU,
H_a=T_a* T_a,
0<a<1.                                                  (N.3)
```

The metric bounds

```text
(1-a)^2 I <= H_a <= (1+a)^2 I                          (N.4)
```

make every compression below boundedly invertible.  For `J=R,E`, define

```text
A_(J,a)=J H_a J | Ran(J),
J_a=T_a J A_(J,a)^(-1) J T_a*.                         (N.5)
```

Then `J_a` is the orthogonal projection onto `T_a Ran(J)`.  Since `T_a` is
invertible, `(N.2)` implies

```text
Ran(R_a) subset Ran(E_a).                              (N.6)
```

Consequently

```text
B_0:=E-R,
B_a:=E_a-R_a                                           (N.7)
```

are themselves orthogonal projections, and the following identity is exact:

```text
R_a-R=(E_a-E)-(B_a-B_0).                               (N.8)
```

This is the missing global bookkeeping.  It is just subtraction of the two
nested orthogonal decompositions

```text
E=R direct-sum B_0,
E_a=R_a direct-sum B_a.                                (N.9)
```

For the Sonin problem, choose `E` to be the half-line cutoff orientation
crossed by the CCM24 multiplier.  The other support orientation is preserved
by the source transfer.  This is the orientation relabelled in Proof 222,
Section 2.  Thus `(E_a-E)` is exactly the half-line metric projection in
`(N.1)`, while `R_a` is the orthogonal projection onto the full transported
Sonin space.

## 3. Explicit Schur-complement owner

Identity `(N.8)` names the remainder, but its internal owner is also explicit.
Decompose

```text
Ran(E)=Ran(R) direct-sum Ran(B_0)                       (N.10)
```

and write the compressed metric in blocks:

```text
A=R H_a R | Ran(R),
C=R H_a B_0 : Ran(B_0) -> Ran(R),
D=B_0 H_a B_0 | Ran(B_0),
S=D-C* A^(-1) C.                                       (N.11)
```

The Schur complement `S` is positive and boundedly invertible.  Put

```text
Z=(I-R A^(-1) R H_a)B_0,
G=T_a Z.                                                (N.12)
```

For `b in Ran(B_0)`, a vector `T_a(r+b)` is orthogonal to `T_a Ran(R)`
exactly when

```text
R H_a(r+b)=0,
r=-A^(-1) Cb.                                          (N.13)
```

Hence `G Ran(B_0)=Ran(B_a)`.  Direct multiplication gives

```text
G*G=S,                                                  (N.14)
```

and therefore

```text
B_a=G S^(-1) G*
   =T_a Z S^(-1) Z* T_a*.                              (N.15)
```

Equations `(N.7)` and `(N.15)` define the residual projection difference
without a spectral choice, a stored trace value, or a transported CC20
correction.

## 4. Exact direct trace split

Let `C_F` be a legally smoothed scaling convolution.  It commutes with `T_a`.
For either `J=R,E`, bounded/trace-class cyclicity in `(N.5)` gives

```text
Tr(C_F J_a)-Tr(C_F J)
 =Tr(J C_F (I-J) H_a J A_(J,a)^(-1))
 =-a Tr(J C_F (I-J)(U+U*)J A_(J,a)^(-1)).              (N.16)
```

This is the direct formula used in Proof 042, now retained without its
superseded factor-two quotient.

Taking the trace of `(N.8)` and applying Proof 222 to `E_a-E` yields

```text
Tr(C_F R_a)-Tr(C_F R)
 =-L sum_(m>=1)a^m[F(mL)+F(-mL)]-G_a(F),               (N.17)

G_a(F):=Tr(C_F(B_a-B_0)).                              (N.18)
```

Thus the exact one-prime semilocal remainder is

```text
E_a(F)=E_infinity(F)-G_a(F),                           (N.19)
```

where `E_infinity` is CC20's Sonin remainder at
`weil-compo.tex:1132-1199`.  Formula `(N.19)` uses the same `F`, the same
transported Sonin projection, and the same convolution-root Hilbert space.
It is not the false bridge rejected in Proof 223.

The signs are fixed by `(N.17)`:

```text
positive semilocal Sonin trace
  = archimedean Sonin trace
      - exact finite-prime Weil series
      - nested-complement change.                      (N.20)
```

## 5. Mellin-diagonal form of the remaining problem

Pass to the unitary Mellin coordinate used by CCM24.  Scaling convolutions
become multiplication.  Let `K_a(s,t)` be the projection kernel of `R_a` in
that coordinate and put

```text
k_a(s)=K_a(s,s).                                       (N.21)
```

For a convolution square `F=g* * g`, the direct positive trace is

```text
Tr(C_g R_a C_g*)
 =integral_R |g_hat(s)|^2 k_a(s) ds.                   (N.22)
```

This is also the diagonal reproducing-kernel density of the CCM24 de Branges
space with its `S`-dependent norm.  Burnol `math/0208121`, equations (1)-(2)
and Theorems 8-9, gives the evaluation kernel and explicit archimedean Sonin
structure function.  CCM24 proves that the entire-function vector space is
common while the norm changes; neither source computes `k_a-k_0` for the Euler
metric.

Under the Fourier convention

```text
F(b)=(1/(2*pi)) integral_R F_hat(s) exp(i s b) ds,
```

the positive prime series in `(N.17)` has multiplier

```text
pi_a(s)=2L sum_(m>=1)a^m cos(mLs)
       =2L Re(a exp(iLs)/(1-a exp(iLs))).               (N.23)
```

Absorb the fixed `2*pi` trace normalization into the definition of `k_a` and
`pi_a` consistently.  The residual multiplier is the unambiguous difference

```text
m_a(s)=k_a(s)-k_0(s)+pi_a(s),                           (N.24)
```

because `(N.17)` says that `k_a-k_0` already contains `-pi_a`.

For the genuine `Q`-root, write

```text
L_+=d/dx+1/2,
g=L_+ xi,
F=g* * g=Q_+(xi* * xi).                                (N.25)
```

The nested-complement post-`Q` form is therefore the compression to the root
support interval `I` of the Fourier multiplier

```text
mu_a(s)=(s^2+1/4)m_a(s).                               (N.26)
```

This gives the following rigorous decision tests:

```text
mu_a belongs to C_0(R):
  nested-complement post-Q correction is compact on L2(I);

mu_a(s) -> c != 0:
  correction is c Id + compact;

mu_a has a nonzero periodic tail, or has one sign and |mu_a|>=delta on
translates of one fixed-width interval:
  correction is noncompact on every interval of positive length.           (N.27)
```

The forward implication in the first line follows by uniformly approximating
a `C_0` multiplier by compactly supported multipliers; their finite-window
compressions are Hilbert-Schmidt.  The rejection tests use normalized
modulations `exp(itx)phi(x)`: they are weakly zero, while their multiplier
quadratic forms sample fixed-width high-energy translates of `mu_a`.

Pointwise non-decay alone is not a general noncompactness theorem.  A rapidly
oscillating bounded symbol can have vanishing local averages and a compact
finite-window convolution kernel.  Any converse here must therefore prove the
relevant slow/periodic symbol class or apply the modulation test directly.

Finite Mellin rows cannot repair the third case.  Their common kernel still
contains weakly zero modulated sequences, so any nonzero essential tail
survives the three route conditions.

## 6. Exact Berezin-flow formula

The diagonal density can be differentiated without expanding
`A_(R,a)^(-1)`.  In the Mellin coordinate, `T_a` is multiplication by

```text
tau_a(s)=1-a exp(-iLs),
x_a(s)=(partial_a tau_a(s))/tau_a(s)
      =-exp(-iLs)/(1-a exp(-iLs)).                     (N.28)
```

The projection flow is

```text
partial_a R_a
 =(I-R_a)M_(x_a)R_a+R_a M_(conj(x_a))(I-R_a).          (N.29)
```

Using the projection-kernel identity

```text
integral_R |K_a(s,t)|^2 dt=k_a(s),                     (N.30)
```

the diagonal of `(N.29)` becomes

```text
partial_a k_a(s)
 =2 Re integral_R
    (x_a(s)-x_a(t)) |K_a(s,t)|^2 dt.                   (N.31)
```

Equation `(N.31)` is the exact new analytic bottom.  The half-line kernel has
the universal boundary value whose integral is `(N.23)`; Proof 222 computes
that value at every Euler order.  What remains is the second-order asymptotic
of the difference between the Sonin Berezin density in `(N.31)` and that
half-line density.  In the notation above, a clean direct sufficient target
for compactness is

```text
k_a(s)-k_0(s)+pi_a(s)=o(|s|^(-2)).                     (N.32)
```

A weaker oscillatory theorem could also prove compactness through vanishing
local translates, but it would need to be stated at the compressed-kernel
level rather than inferred from pointwise bounds.  A mere trace-class angle
theorem does not imply `(N.32)`.  Post-`Q` spends two derivatives, and Proof
223 shows that a missed central coefficient becomes a quadratically growing
form.

## 7. Reproduction and diagnostic boundary

The companion script has two layers.

The certificate layer uses deterministic finite nested subspaces.  It checks:

```text
R_a <= E_a,
R_a-R=(E_a-E)-[(E_a-R_a)-(E-R)],
the Schur formula (N.15),
the direct trace split (N.16),
and the exact half-line coefficients from Proof 222.
```

The scattering layer uses the source archimedean phase

```text
u_infinity(s)
 =pi^(-is) Gamma(1/4+is/2)/Gamma(1/4-is/2)
```

and selects the near-intersection modes of the finite pair of half-line
projections.  It reports convergence of the first three metric atoms and
samples `(N.26)`.  This layer is a rejection diagnostic only: the Sonin cutoff
and high-energy limits do not commute automatically.

```text
python3 -B docs/proofs/224_metric_sonin_nested_complement_remainder.py
```

The default algebraic errors are below `1e-12`; the half-line atom ratios are
`1` to at least nine decimal places.  The finite Sonin atom ratios rise with
the spectral cutoff, while the post-`Q` residual samples remain order one and
change sign on the tested window.  Therefore the experiment neither certifies
compactness nor supplies a sign theorem.  It rules out treating the residual
as numerically negligible before the two limits are separated.

## 8. Route judgment

```text
direct full metric trace formula:              exact
complete half-line prime-power subtraction:    exact, from Proof 222
same-object residual projection:               B_a-B_0
residual Schur-complement owner:                exact
same root Hilbert space:                        retained
CC20-angle compact lift from Proof 223:         not reused
post-Q compactness gate:                        (N.32) is sufficient, open
three-Mellin-row sign:                          open
Lean owner or route rewire:                     none
RH:                                             unproved
```

The next proof must attack `(N.31)--(N.32)` directly.  A successful
`o(s^-2)` theorem produces the compact correction required by the route.  A
nonzero limiting, periodic, or fixed-width stable tail of `mu_a` rejects
compactness; its sign on modulated vectors then decides whether an unbounded
common-form-domain replacement can survive.
