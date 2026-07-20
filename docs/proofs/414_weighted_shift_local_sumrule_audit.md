# Proof 414: Weighted compressed shift and localized sum-rule audit

Date: 2026-07-19

Status: exact weighted compressed-shift identity, analytic counterexample to
the one-parameter rank-one shortcut, and source audit of the available
Schatten/Szego theorems.  The calculation leaves one possible determinant
route: a Burnol-specific localized sum rule that reduces the complete signed
relative response to the Euler square ledger after compact support acts.

This proof does not establish that sum rule.  Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------------+---------------------+
| layer                                                | judgment            |
+------------------------------------------------------+---------------------+
| weighted compression of the Cayley shift             | rank-one formula    |
| isometric Hitt multiplier                             | one scalar v        |
| general route weight                                  | full Gram inverse   |
| compressed shift determines all multiplier responses | false analytically  |
| Bessonov general Schatten characterization           | conjectural         |
| finite-model Szego limit                              | wrong quantifiers   |
| global Euler H^(1/2) energy                           | divergent in S      |
| frequency-localized Euler square ledger               | O((1+L)^2)          |
| Burnol-localized signed sum rule                      | open Gate producer  |
| Gate 3U / RH                                          | open / unproved     |
+------------------------------------------------------+---------------------+
```

The calculation rules out the implication

```text
rank-one compressed shift
  -> one Schur/Frostman parameter
  -> all weighted multiplier traces
  -> Gate 3U.                                           (WS.1)
```

The first two arrows hold for the shift itself.  The third arrow fails even
for a two-dimensional model space and an isometric multiplier.

## 2. Exact weighted shift identity

Work in disk Hardy space.  Let `theta` be inner with `theta(0)=0`, and put

```text
K=K_theta=H^2 minus theta H^2,
d=theta/z,
S_theta=P_theta M_z|K.                                (WS.2)
```

The model space has the orthogonal decomposition

```text
K=K_(theta/z) direct-sum C d.                         (WS.3)
```

Let `h` be a bounded positive weight for which

```text
G_h=A_theta(h)=P_theta M_h|K                          (WS.4)
```

is invertible.  If `f=f_0+alpha d` according to `(WS.3)`, then

```text
z f=z f_0+alpha theta,
S_theta f=z f_0.                                     (WS.5)
```

Project `h z f` back to `K`.  Equations `(WS.4)--(WS.5)` give

```text
A_theta(h z)
 =G_h S_theta+P_theta(h theta) tensor d,              (WS.6)

G_h^(-1)A_theta(h z)
 =S_theta+u_h tensor d,

u_h=G_h^(-1)P_theta(h theta).                         (WS.7)
```

Here `(x tensor y)f=<f,y>x`.  Formula `(WS.7)` is algebraic.  It uses no
finite section, asymptotic, or Schatten premise.

For the route,

```text
m_S=g_0 tau_S,
h_S=abs(m_S)^2,
G_S=A_theta(h_S).                                    (WS.8)
```

Thus the route shift has a rank-one defect, but its left vector is the full
Gram solution

```text
u_S=G_S^(-1)P_theta(h_S theta).                      (WS.9)
```

Rank one does not remove `G_S^(-1)`.

## 3. The isometric special case

Suppose multiplication by `g` maps `K_theta` isometrically into `H^2`.  Then

```text
A_theta(abs(g)^2)=I.                                (WS.10)
```

Liang and Partington compute the weighted compressed shift in this setting.
With

```text
v=<theta,abs(g)^2>,
abs(v)<1,                                           (WS.11)
```

their Proposition 2.3 gives

```text
A_theta(abs(g)^2 z)
 =S_theta+v (1 tensor d).                           (WS.12)
```

Their Crofoot transform identifies `(WS.12)` with the standard compressed
shift for the Frostman transform

```text
theta_v=(theta-v)/(1-conjugate(v)theta).             (WS.13)
```

Source:

```text
Y. Liang and J. R. Partington,
Spectra and invariant subspaces of compressed shifts on nearly invariant
subspaces, Proposition 2.3 and Sections 3--4:
https://arxiv.org/html/2506.18646v2
```

This theorem applies after one has found the canonical Hitt isometric
multiplier.  It does not find that multiplier from the non-isometric route
frame `(WS.8)`.

Indeed, let `J_m:K_theta->m K_theta` be multiplication by `m`.  The orthogonal
range projection is

```text
P_(mK)=J_m G_h^(-1)J_m*.                            (WS.14)
```

Since `J_m*1` is a scalar multiple of the reproducing kernel `k_0`, Hitt's
extremal vector for `mK_theta` is proportional to

```text
m G_h^(-1)k_0.                                      (WS.15)
```

Consequently, conversion of the route range to its canonical isometric
model-space representation first requires the same inverse `G_S^(-1)` that
Gate 3U must control.  The Crofoot coordinate does not bypass the inverse.

## 4. One compressed-shift parameter does not determine the detector

The failure has an exact two-dimensional witness.  Set

```text
theta(z)=z^2,
K_theta=span{1,z},
h_epsilon(e^(it))=1+2 epsilon cos(3t),
abs(epsilon)<1/2.                                   (WS.16)
```

The weight is strictly positive.  Put

```text
delta=sqrt(1-4 epsilon^2),
a=sqrt((1+delta)/2),
b=epsilon/a,
g_epsilon(z)=a+b z^3,

a^2+b^2=1,
a b=epsilon,
abs(g_epsilon)^2=h_epsilon.                         (WS.17)
```

For nonzero `epsilon`, `abs(b)<a`, so all zeros of `g_epsilon` lie outside
the disk.  Thus `g_epsilon` is outer.  The constant case `epsilon=0` is outer
as well.

For `f=a+bz`, the function `abs(f)^2` has frequencies only `0,+/-1`, while
`h_epsilon-1` has frequencies only `+/-3`.  Orthogonality of circle
characters gives

```text
integral h_epsilon abs(f)^2=abs(a)^2+abs(b)^2.       (WS.18)
```

Thus multiplication by `g_epsilon` is isometric on `K_(z^2)`.  Moreover,

```text
<z^2,h_epsilon>=0,
A_(z^2)(h_epsilon z)=S_(z^2)                        (WS.19)
```

for every allowed `epsilon`.  All these spaces therefore have the same
rank-one parameter `v=0` and the same compressed shift.

The next multiplier separates them.  In the ordered basis `(1,z)`, direct
Fourier projection gives

```text
A_(z^2)(h_epsilon z^2)
 =[0  epsilon]
  [0     0   ].                                    (WS.20)
```

At `epsilon=0`, this operator is zero.  For `epsilon!=0`, it is nonzero.
Hence the compressed shift and its Frostman parameter do not determine the
weighted response even for the next analytic monomial.  A scalar spectral
shift theorem for `(WS.12)` cannot recover the Gate detector.

## 5. The available Schatten and Szego results

```text
+----------------------+--------------------------------+----------------------+
| source               | theorem contract               | Gate mismatch        |
+----------------------+--------------------------------+----------------------+
| Bessonov 1407.3466   | compact Hankel, one-component  | S_p rule is conjecture|
| Lopatto--Rochberg    | analytic symbols; complete S_2 | full mixed symbol and |
| 1410.1906            | characterization               | inverse absent       |
| Miheisi--O'Loughlin  | finite Blaschke B_N and        | normalized N->infinity|
| 2404.03087           | trace-density limit            | asymptotic only      |
| Liang--Partington    | one weighted compressed shift  | higher multipliers   |
| 2506.18646           | and Crofoot model              | not determined       |
+----------------------+--------------------------------+----------------------+
```

Bessonov states the general `S_p` characterization as a conjecture in Section
4.3, even under the one-component hypothesis:

```text
https://arxiv.org/pdf/1407.3466
```

Lopatto and Rochberg state that cancellation between analytic and
anti-analytic pieces can dominate the operator; their complete general result
stops at Hilbert--Schmidt class:

```text
https://arxiv.org/pdf/1410.1906
```

Miheisi and O'Loughlin prove a first Szego limit for increasing finite
Blaschke model spaces.  Theorem 2.1 controls `N^(-1)Tr` as `N->infinity`; it
does not give an exact bound for Burnol's fixed infinite model space or the
moving nonconstant weight `h_S`:

```text
https://arxiv.org/html/2404.03087v1#S2.Thmtheorem1
```

No cited theorem supplies the route's finite-`S`, inverse-after-weighted-Gram
estimate.

## 6. The Euler square ledger

Write

```text
a_p=p^(-1/2),
ell_p=log(p),
tau_S(s)=product_(p in S)(1-a_p exp(i ell_p s)).     (WS.21)
```

The logarithm has the exact expansion

```text
log tau_S(s)
 =-sum_(p in S)sum_(m>=1)
    p^(-m/2) exp(i m ell_p s)/m.                    (WS.22)
```

The ordinary quadratic strong-Szego energy of `(WS.22)` contains

```text
E_S
 =sum_(p in S)sum_(m>=1)
   log(p) p^(-m)/m
 =sum_(p in S)log(p)[-log(1-1/p)].                  (WS.23)
```

This quantity has no bound independent of `S`: its `m=1` part is
`sum_(p in S)log(p)/p`, which diverges along initial prime sets.  A global
`H^(1/2)` or strong-Szego norm therefore recreates an `S`-dependent constant.

Compact support suggests a smaller ledger.  For a displacement cutoff `L`,
put

```text
E_S(L)
 =sum_(p in S,m>=1,m log(p)<=L)
   log(p) p^(-m)/m.                                 (WS.24)
```

For `n=p^m`, each summand in `(WS.24)` satisfies

```text
log(p)/(m p^m)
 <=log(n)/n.                                          (WS.25)
```

Discarding the prime-power restriction and comparing the remaining sum with
an integral gives

```text
sup_(finite S) E_S(L)
 <=sum_(2<=n<=exp(L))log(n)/n
 <=C(1+L)^2.                                       (WS.26)
```

Thus the square ledger has the polynomial support budget required by Gate
3U after frequency localization.

Proof 413 prevents applying `(WS.26)` term by term.  Compact support also
retains off-diagonal pairs with

```text
abs(m log(p)-n log(q))<=2B_root.                    (WS.27)
```

A valid theorem must cancel or resum those pairs inside the weighted relative
determinant before it replaces them by `(WS.24)`.  The standard global Szego
energy, rank-one shift parameter, and primewise absolute value do not perform
that resummation.

## 7. Exact remaining theorem

Proof 413 defines the legal compact-test functional

```text
Lambda_S(F)
 =Tr[G_S^(-1)A_theta(h_S w_F)
      -G_0^(-1)A_theta(h_0 w_F)].                   (WS.28)
```

The only surviving model-space route must prove a Burnol-specific localized
sum rule of the following form:

```text
complete weighted relative determinant
  +Q-completed compact root
  +Burnol outer-minus-Sonin boundary identity
  -> diagonal Euler square ledger `(WS.24)`
     plus a uniformly summable remainder.           (WS.29)
```

The output must imply

```text
sup_(finite S) norm(Lambda_S)_(R_B^r)*
 <=C(1+B)^d.                                        (WS.30)
```

Equation `(WS.29)` is not available in the audited literature.  Proving it
would close Gate 3U after adding Proof 336's far tail.  The rank-one identity
`(WS.7)` supplies one boundary coordinate for that proof, but the counterexample
`(WS.16)--(WS.20)` forbids treating it as the whole determinant.

## 8. Route judgment

```text
weighted shift rank-one formula:             proved `(WS.7)`;
Crofoot scalar shortcut for all detectors:   rejected `(WS.20)`;
global strong-Szego majorant:                 rejected `(WS.23)`;
localized diagonal square budget:            proved `(WS.26)`;
off-diagonal determinant resummation:         open `(WS.29)`;
Gate 3U / finite-S sign / Burnol / RH:        open / open / open / unproved.
```

The next proof must target `(WS.29)` on the full weighted Gram.  More
compressed-shift spectral data, a one-component assumption, or a global
Schatten norm cannot supply the missing off-diagonal cancellation.
