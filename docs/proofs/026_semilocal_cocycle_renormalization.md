# Semilocal Cocycle Renormalization

Date: 2026-07-11

Status: rejected for the direct finite-S remainder. Exact cocycle algebra
controls the mixed term, but it leaves a pure finite-place term whose post-Q
quadratic form has a nonzero second-order principal part.

## 1. Exact Cocycle

Let `P` be the half-line projection and, for a unitary scattering multiplier
`u`, define

```text
Omega(u) := u* P u - P = (1/2) u* d u.
```

For two unitaries `u,v`, direct multiplication gives

```text
Omega(uv) = v* Omega(u) v + Omega(v).                       (C.1)
```

This is the operator cocycle behind additivity of local Weil terms. If the
smoothed trace is legal and the test multiplier commutes with `u,v`, cyclicity
gives the corresponding trace additivity.

For `S={infinity,p}`, take `u=u_infinity` and `v=u_p`. Formula (C.1) shows that
the noncompact Euler Hankel block belongs to the finite-prime local cocycle
`Omega(u_p)`. It must not be included in the candidate compact remainder after
the finite local Weil term has been subtracted.

Source normalization:

```text
CC20, weil-compo.tex:171-175, 351-362, 536-559
  local Weil trace uses (1/2) u* d u and the support compression P.

CCM24, mainc2m24fine.tex:232-259, 761-779
  u_S is the product of the local Euler scattering factors.
```

Primary sources:

```text
https://arxiv.org/abs/2006.13771
https://arxiv.org/abs/2310.18423
```

## 2. Exact Remainder Decomposition

Let `V=V(f)` be the smoothed scaling/convolution operator, commuting with the
scattering multipliers, and define

```text
R_P(V) := V - P V P,
D_u(f) := Tr(R_P(V) Omega(u)).
```

Put `Q_v:=v P v*`. Using (C.1), cyclicity, and `v V = V v`, one obtains

```text
D_(uv)(f)
  = D_v(f) + D_u(f) + Cross_(u,v)(f),                       (C.2)

Cross_(u,v)(f)
  := Tr((P V P - Q_v V Q_v) Omega(u)).                     (C.3)
```

Indeed,

```text
Tr(R_P(V) v* Omega(u) v)
  = Tr(v R_P(V) v* Omega(u))
  = Tr((V-Q_v V Q_v) Omega(u)).
```

Subtracting `D_u(f)=Tr((V-PVP)Omega(u))` gives (C.3).

This identifies exactly where the raw noncompactness argument stops. It does
not remove `D_v`: the positive-trace identity has already subtracted the local
Weil trace before defining `D_(uv)`. Moving `D_v` into that local term would
change the identity and requires a new source theorem. No such theorem has
been found. The direct semilocal remainder contains all three terms in (C.2).

## 3. Mixed-Term Gate

For the post-`Q` square `f=Q(xi*xi*)`, prove or reject

```text
Cross_(u_infinity,u_p)(Q(xi*xi*))
  = <xi, K_cross,p,I xi>,

K_cross,p,I compact and self-adjoint.                       (C.4)
```

If (C.4) holds, conjugating the archimedean normal form preserves its scalar
part and compactness:

```text
v* (-2 Id + K_I) v = -2 Id + v* K_I v.
```

This only controls `D_u+Cross_(u,v)`. Gate A additionally requires control of
the pure finite-place term `D_v`, which remains in (C.2).

The smoothing in `PVP` means the raw partial-translation argument does not
decide (C.4). A proof must derive the same-object kernel of (C.3), not merely
inspect `[P,u_p]`.

## 4. Operator-Ideal Estimate

The compactness mechanism can be isolated before computing the final
quadratic kernel. Let `T=PVP`. Since `v V=V v`,

```text
PVP-Q_v V Q_v
  = T-v T v*
  = [T,v]v*,

[T,v] = P V [P,v] + [P,v] V P.                             (C.5)
```

For `v=u_p`, write its Fourier series as in the 025 verdict. A translation
block `A_b=[P,T_b]` crosses the half-line only for one variable in an interval
of length `|b|`. If `V=V_h` is convolution by a Schwartz kernel `h`, then

```text
kernel(V_h A_b)(x,y)
  = h(x-y-b) (P(y+b)-P(y)),

norm(V_h A_b)_HS^2 = |b| norm(h)_2^2.                      (C.6)
```

The Euler coefficients decay geometrically like `p^(-|m|/2)`, so

```text
sum_m |c_m| sqrt(|m| log p) < infinity.
```

Consequently both terms in (C.5) are Hilbert--Schmidt. Using derivatives of
the Schwartz kernel and a standard Sobolev factorization strengthens each
finite translation block to trace class with at most polynomial growth in
`|m|`; geometric Euler decay makes the trace-norm series converge. Therefore

```text
PVP-Q_vVQ_v is trace class.                                (C.7)
```

Multiplication by the bounded archimedean `Omega(u_infinity)` preserves trace
class. Thus the trace in (C.3) is legal. This controls the mixed cocycle
correction; it does not alter the separate `D_v` summand.

There is also a distribution-level distinction that will be decisive below.
Expand both occurrences of `v` in (C.3) into translations. Every coefficient
of the mixed trace is then a translate and finite boundary compression of the
archimedean coefficient `delta_infinity`. CC20 gives that coefficient as the
piecewise smooth, locally integrable function in `weil-compo.tex:561-565`; its
only relevant singularities are cusps, not Dirac measures. The Euler
coefficients are absolutely summable with every polynomial translation
weight, so the translated mixed series has the same piecewise regularity. In
particular, `Cross_(u_infinity,u_p)` contains no Dirac mass; applying `Q_+`
can create order-zero point evaluations from cusps, but not a second-order
point interaction.

For `h=Q(xi*xi*)` and `xi` supported in a fixed compact interval `I`, the same
expansion gives an `L2(I x I)` kernel term by term after integration by parts;
geometric Euler decay controls the sum. This supplies a compact quadratic-form
owner for the mixed term. Hermitian symmetry follows by pairing the `m` and
`-m` translation rows and taking the real quadratic form. Thus the mixed term
is lower order than the finite-place Dirac contribution below.

## 5. Pure Finite-Place Obstruction

The pure term can be computed before any archimedean estimate. Use the
additive convention

```text
(T_b psi)(x) = psi(x-b),
P = 1_[0,infinity),
L = log p.
```

Write the Euler phase as

```text
v = sum_n c_n T_(nL),
c_1 = -a,
c_(-j) = (1-a^2) a^j  for j>=0,
a = p^(-1/2).
```

Unitarity lets one expand the cocycle as

```text
Omega(v) = sum_k M_(a_k) T_(kL),

a_k(x) = sum_m conjugate(c_m)c_(m+k)
                 (P(x+mL)-P(x)).                          (C.8)
```

The boundary remainder for a translation is

```text
R_r = T_(-r)-P T_(-r)P.
```

Taking the trace of `R_r Omega(v)` forces `r=kL`. Therefore the pure
finite-place remainder is a Dirac comb

```text
delta_p(r) = sum_k d_k Dirac_(kL).                         (C.9)
```

The central coefficient needs only `c_1`:

```text
d_0
  = integral_(x<0) sum_m |c_m|^2(P(x+mL)-P(x)) dx
  = |c_1|^2 L
  = p^(-1) log p > 0.                                    (C.10)
```

The first off-centre coefficient is also nonzero:

```text
d_1 = -L sum_(j>=1) conjugate(c_(-j))c_(-j+1)
    = -L a(1-a^2) != 0.                                  (C.11)
```

For `f=xi*xi*`, applying `Q_+=-partial_r^2+1/4` gives

```text
D_p(Q_+ f)
  = sum_k d_k (-f''(kL)+(1/4)f(kL)).                      (C.12)
```

Choose a nonzero smooth `phi` in a subinterval of width strictly less than
`L`. Then its autocorrelation and all derivatives vanish at every nonzero
`kL`. Modulate it by

```text
xi_s(x)=exp(isx) phi(x),
f_s(r)=exp(isr) f_0(r).
```

Thus only `k=0` survives in (C.12), and its leading term is

```text
d_0 s^2 ||phi||_2^2.
```

There is therefore no possible cancellation from the other Dirac atoms. If a
larger support is used, (C.11) additionally produces the nonconstant
`s log p` phase seen in the numerical probe. The sequence `xi_s/||phi||_2`
converges weakly to zero as `|s|` tends to infinity. A compact quadratic
perturbation tends to zero on this sequence, while a scalar term stays
bounded. Equation (C.12) instead grows quadratically. Hence

```text
D_p o Q_+ != -c Id + compact.                             (C.13)
```

In fact the left side is not represented by any bounded operator on the
fixed-support `L2` space. Neither the archimedean term nor the mixed term can
cancel it. Before applying `Q`, both are locally integrable coefficient
functions, while (C.9) has the nonzero Dirac mass `d_0 Dirac_0`. Applying
`Q_+` therefore leaves the unique second-derivative singularity
`-d_0 Dirac_0''`; a locally integrable coefficient cannot supply an opposite
Dirac mass before `Q_+`. Equivalently, the mixed post-Q kernel is compact,
whereas (C.12) has the explicit second-order principal part (C.10).

## 6. Reproducible Discrete Check

`025_finite_euler_remainder_probe.py` discretizes precisely the pure `p=2`
coefficient before mixing it with the archimedean factor. Stable phase-bin
means include:

```text
grid     |s| band   phase-bin means
1024     10--20     4.4154, 1.3155, 1.3157, 4.4157
2048     10--20     4.4155, 1.3154, 1.3155, 4.4155
1024     20--30    11.2253, 3.9308, 3.9313, 11.2266
2048     20--30    11.2258, 3.9306, 3.9307, 11.2260
```

The grid-refinement stability supports the Dirac-comb calculation and the
quadratic growth in (C.12). It is evidence only; equations (C.8)--(C.13) are
the continuous rejection argument.

## 7. Decision

```text
raw finite Euler quantized differential: non-scalar modulo compact.
finite local cocycle subtraction: exact algebraically.
renormalized cross term trace legality: passes by smoothing and Euler decay.
pure finite-place post-Q term: unbounded second-order Dirac-comb form.
Gate A for the direct u_S remainder: rejected.
only reopening condition: prove an exact same-object cancellation of (C.12)
before the positive trace read-off, or construct a different pre-cutoff
trace/supertrace in which the pure finite-place term never occurs.
```

No source checked so far prints (C.2)--(C.4) as a semilocal remainder theorem.
The cocycle algebra is lower than RH. It does not provide the cancellation
needed to remove the pure finite-place principal part.
