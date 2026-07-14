# Proof 225: Sonin triangular-band principal compactness

Date: 2026-07-14

Status: for every fixed triangular width `q>0`, the normalized high-energy
scattering channel of Proof 224 is settled.  Its post-`Q` compression to every
finite root interval is Hilbert--Schmidt even though its pointwise symbol need
not converge to zero.  The mechanism is a compact triangular frequency filter
followed by the archimedean chirp, whose inverse Fourier response is smooth on
every compact set.  This removes the fixed-mode principal noncompact
partial-translation threat.  It does not yet prove a uniform Euler-mode sum or
control the nonconstant de Branges amplitude produced by the finite-`S` norm.
The full metric residual and its three-row sign therefore remain open.  No
Lean owner is authorized, and RH remains unproved.

## 1. The normalization that must not be skipped

CCM24 proves two different statements:

```text
the entire-function vector space B_lambda is independent of S;
the norm on B_lambda is induced by |E_S(s)|^(-2) ds and depends on S.
```

These are equations `(57)--(62)` and Section 4.8.3 of
<https://arxiv.org/abs/2310.18423v2>.  Here `E_S` denotes the product of local
Euler factors used in the ambient weight.  It is not automatically the
Hermite--Biehler structure function of the Sonin de Branges subspace.

Consequently the tempting implication

```text
same entire functions + Euler weight
  => new structure function = old structure function / tau_a
```

is false without an additional theorem.  Equivalently, the actual projection
kernel on the fixed Mellin `L2` carrier contains a nonconstant isometric
multiplier amplitude.  The phase-only formula

```text
4 sin^2(phi(s)-phi(t))/(s-t)^2
```

describes the normalized principal channel, not the complete kernel in
Proof 224's equation `(N.31)`.  This distinction is why the result below is a
principal-channel theorem rather than the full compactness theorem.

## 2. Source scattering response

In the archimedean scattering coordinate put

```text
u_infinity(s)
  = pi^(-is) Gamma(1/4+is/2)/Gamma(1/4-is/2).          (T.1)
```

For the Fourier convention

```text
Fourier(k)(s)=integral_R k(x) exp(-isx) dx,
```

the exact Mellin-cosine calculation gives

```text
k_infinity(x)=2 exp(x/2) cos(2*pi*exp(x)),
Fourier(k_infinity)=conjugate(u_infinity).              (T.2)
```

Indeed, after `y=exp(x)`, the left side is

```text
2 integral_0^infinity y^(-1/2-is) cos(2*pi*y) dy,
```

and Gamma duplication/reflection reduce its closed value to the conjugate of
`(T.1)`.  The equality is distributional: the right tail is interpreted by
the displayed oscillatory integral, while on every compact interval
`k_infinity` is the ordinary smooth function shown above.  Burnol's de Branges
evaluator kernel and its endpoint structure are the source objects behind this
scattering normalization:

```text
https://arxiv.org/abs/math/0208121
  equations (1)-(2)
  source lines 353-385: endpoint Sonin distributions
  source lines 393-431: structure function and evaluator jump
```

The crucial analytic fact is visible directly in `(T.2)`: the oscillatory
distribution is represented by a `C^infinity` function on every finite
logarithmic interval.  It grows at one end, but a fixed compact convolution
only probes a compact enlargement of the requested difference interval.

## 3. Exact triangular low-pass identity

For `q>0` define

```text
a_q(r)=(1-cos(qr))/r^2.                                (T.3)
```

As a tempered distribution,

```text
Fourier(a_q)(xi)=pi*(q-|xi|)_+.                         (T.4)
```

Let `theta` be the principal scattering phase and use the normalized kernel

```text
|K_theta(s,t)|^2
  =4 sin^2((theta(s)-theta(t))/2)/(s-t)^2.              (T.5)
```

Expanding the sine square in the structure factor gives, after the half-line
term has entered its interior cone,

```text
S_q(s)-q
 =-(1/pi) Re[
     exp(i theta(s))
     (a_q * exp(-i theta))(s)
   ].                                                   (T.6)
```

By `(T.2)--(T.4)`, the convolution in `(T.6)` is the inverse Fourier transform
of the compactly supported profile

```text
F_q(xi)=pi*(q-|xi|)_+*k_infinity(xi).                   (T.7)
```

This is the exact reason that ordinary pointwise tail tests are too strong.
The term in `(T.6)` is a high-frequency phase multiplied by a compact-band
function.

## 4. What two integrations by parts really leave

The profile `F_q` vanishes at `+-q`, is continuous, and has one derivative
jump at `0`.  Two piecewise integrations by parts give

```text
s^2 (1/(2*pi)) integral_(-q)^q F_q(xi) exp(is xi) dxi

  = k_infinity(0)
    -(1/2)[
       k_infinity(-q) exp(-iqs)
       +k_infinity(q) exp(iqs)
     ]
    +O(1/|s|).                                         (T.8)
```

Thus post-`Q` can leave a bounded, nondecaying expression.  It is not a fixed
periodic multiplier by itself: `(T.6)` still multiplies it by
`exp(i theta(s))`, and `theta'(s)` has the unbounded archimedean Gamma slope.
The surviving oscillation therefore runs to higher frequency with `|s|`.

This distinguishes two superficially similar tails:

```text
fixed periodic tail:
  noncompact partial translation on a finite interval;

archimedean chirp times a compact-band amplitude:
  locally smooth inverse Fourier kernel.                (T.9)
```

## 5. Finite-window Hilbert--Schmidt theorem

Fix `q>0`, and let `mu_q` be the principal post-`Q` symbol obtained from
`(T.6)`.  Fourier multiplication turns its inverse transform into a finite sum
of derivatives of convolutions of `k_infinity` (and its reflected conjugate)
with the compact profile `F_q`.  Since `k_infinity` is smooth on compact sets,
this inverse transform, denoted `kappa_q`, belongs to `L2(J)` for every compact
interval `J`.

For a bounded root interval `I`, the compressed Fourier multiplier has kernel
`kappa_q(x-y)`.  Its Hilbert--Schmidt norm is therefore

```text
norm(P_I M_(mu_q) P_I)_HS^2
  = integral_(I-I)
      measure(I intersect (I-r)) * |kappa_q(r)|^2 dr
  < infinity.                                          (T.10)
```

This proves compactness of the normalized fixed-`q` principal channel.  It does
not use the stronger and generally false requirement `mu_q in C_0(R)`.

The complete Euler flow requires `q=m log(p)` and
`0<=alpha<=p^(-1/2)`.  The periodic Euler factor does have geometrically
decaying Fourier coefficients, but that fact alone is insufficient: translated
derivatives of the archimedean response need a compatible local `L2` bound.
No uniform-in-`alpha`, summable-in-`m` estimate is claimed here.  That estimate
is part of the remaining gate below.

## 6. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/225_sonin_triangular_band_principal_compactness.py
```

The certificate independently checks:

```text
the Gamma/cosine identity (T.2);
the scaled triangular asymptotic (T.8);
local L2 convergence of a representative twice-differentiated convolution
term.
```

The numerical layer checks the ingredients and quadrature stability; the
finite-window theorem follows from the local smoothness argument, not from the
grid.  The script does not test the missing amplitude or uniform Euler-mode
theorem.  Its default quadrature is scoped to `p=2,3`; larger widths require a
higher or adaptive order because `k_infinity''` becomes rapidly oscillatory.

## 7. Remaining same-object bottom

The full kernel in Proof 224 has the form

```text
principal scattering kernel
  + de Branges amplitude/norm correction.               (T.11)
```

CCM24 proves that the norms are equivalent and that the entire-function space
is unchanged.  It does not give the uniform two-derivative Fourier-response
estimate for the correction in `(T.11)`.  Burnol gives the endpoint structure
at `alpha=0`, but the required theorem must hold uniformly for
`alpha in [0,p^(-1/2)]` and with polynomial control in the Euler mode `m`.

The corrected next gate is therefore:

```text
prove that the exact amplitude correction has a locally H^2 Fourier response,
uniformly in alpha;

prove a compatible locally H^2 bound for the principal q=m log(p) modes whose
growth is summable against the exact Euler coefficients;

or exhibit a fixed-frequency atom in that correction and reject compactness.
                                                               (T.12)
```

The phase-only triangular channel cannot supply such an atom.  If `(T.12)`
passes, Proof 224's full post-`Q` compactness gate closes.  The sign of the
resulting compact self-adjoint correction on the three-Mellin-row subspace is
still an independent final gate.

## 8. Route judgment

```text
same-object residual from Proof 224:             retained
principal scattering normalization:              exact
triangular frequency localization:                exact
fixed-q principal finite-window compactness:       proved
uniform Euler-mode principal sum:                  open
full de Branges amplitude correction:             open
full metric residual compactness:                 open
three-Mellin-row sign:                             open
Lean owner or route rewire:                        none
RH:                                                unproved
```
