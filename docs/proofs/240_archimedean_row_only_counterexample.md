# Proof 240: certified failure of the row-only archimedean sign

Date: 2026-07-14

Status: **accepted rejection of the universal row-only claim**. A fixed smooth
compact test satisfies the two independent pre-root Mellin rows but has a
strictly positive value for the continuous archimedean form
`D_infinity=-2 Id+K_infinity`. This does not evaluate the finite-S correction
and does not reject a sign theorem after the correct finite-dimensional
control space is imposed.

## 1. Exact target

The current route convention has source nodes `s=0,1/2,1` (Proof 072). For
the genuine Q-root

```text
g = L xi,                  L=d/dx+1/2,
```

integration by parts gives

```text
M_s(g)=(1/2-s)M_s(xi).
```

The `s=1/2` row is automatic, so the two independent pre-root constraints are

```text
M_0(xi)=0,                 M_1(xi)=0.                 (A.1)
```

This is the coordinate used by Proof 239. Proof 220 uses a centered
`M_{-1/2}` notation in a different coordinate; it is not silently interchanged
here.

On `I=[0,L]`, with `L=3 log(2)/2 < log(3)`, let

```text
phi_n(x)=sqrt(2/L) sin(n pi x/L),
xi(x)=sum_(n in {1,2,3,5}) c_n phi_n(x).              (A.2)
```

Set `c_1=-8/15`, `c_3=c_5=1`, and define `c_2` by the exact `M_1`
equation. If

```text
a_n=n pi/L,       E=exp(L)=2 sqrt(2),
b_n=a_n(1-(-1)^n E)/(1+a_n^2),
```

then

```text
c_2=-(c_1 b_1+c_3 b_3+c_5 b_5)/b_2.                 (A.3)
```

The first row is exact because

```text
c_1/1+c_3/3+c_5/5=-8/15+1/3+1/5=0.                 (A.4)
```

The second row is exact by (A.3). Numerically, only for orientation,
`c_2=0.2055188692101416...`.

## 2. Removing the derivative singularity

Write `delta(t)=delta(exp(t))` for `t>=0`, and let

```text
C_xi(t)=integral_0^(L-t) xi(x+t) xi(x) dx.
```

For `t>0`, the ordinary CC20 kernel is

```text
K_infinity(t)=delta(t)/4-delta''(t).
```

The one-sided logarithmic derivative satisfies `delta'(0+)=1`; this is the
jump which produces the separate `-2 Dirac` term in the CC20 distribution.
Because the sine basis vanishes at both endpoints,
`C_xi(0)=||xi||^2`, `C_xi'(0)=C_xi(L)=C_xi'(L)=0`. Two integrations by parts
give

```text
-2||xi||^2 + 2 integral_0^L K_infinity(t) C_xi(t) dt
 = 2 integral_0^L delta(t) (C_xi(t)/4-C_xi''(t)) dt. (A.5)
```

With `g=L xi`, the bracket is the one-sided autocorrelation

```text
H_g(t)=integral_0^(L-t) g(x+t)g(x) dx.                (A.6)
```

Thus (A.5) evaluates the exact `D_infinity` form without numerically
differentiating the oscillatory `Si` profile or resolving its diagonal.

## 3. Arb certificate

`240_archimedean_row_only_counterexample.py` evaluates `H_g` as a finite sum
of complex exponentials and applies Arb's rigorous complex quadrature only to
the outer integral in (A.5). Run in WSL:

```text
uv run --with python-flint python \
  docs/proofs/240_archimedean_row_only_counterexample.py
```

Accepted values at 100 bits and eight integration pieces are

```text
norm_squared = 2.3266824500458597349962479930...
quadratic    = 1.3868001172690784429...
Rayleigh     = 0.59604185231282598168...
```

The program aborts unless Arb proves `quadratic>1` and `Rayleigh>1/2`.
The residual balls printed for `M_0` and `M_1` contain zero because the script
evaluates the exact formulas with finite precision; (A.3)--(A.4) are the exact
row equalities.

The direct regular-kernel Gauss--Legendre calculation in Proof 239 converges
to the same value from below. The new certificate does not use a finite
scattering section, a Sonin cutoff, a grid boundary mode, or an eigenvalue
solver.

## 4. Route consequence

The universal implication

```text
M_0(xi)=M_1(xi)=0  ==>  <xi,D_infinity xi> <= 0
```

is false on this bounded interval. This is exactly the scale at which the
first prime can enter, while `1.5 log(2)<log(3)` keeps the visible prime set at
`p=2`.

The result does **not** say that the complete finite-S route is impossible.
It says that the two Mellin rows cannot be the whole control mechanism. Any
surviving route must provide, on the same finite-S owner,

```text
finite-S compact remainder K_(S,I)
  + its finite-dimensional bad/control space B_(S,I)
  + exact detector orthogonality to B_(S,I)
  + the Burnol all-zero identity for that same owner.
```

Proof 113 already rejects replacing this conditioning by a prime-free
orthogonalization shortcut. The next bottom is a same-object finite-S
conditioning theorem, not a stronger row-only archimedean estimate.

## 5. Scope and status

```text
row-only archimedean sign:            rejected by Arb certificate
finite-S sign after control space:    open
finite-S positive owner:              open
Burnol spectral identity in Lean:     open
Lean declaration:                     none
RH:                                   unproved
```
