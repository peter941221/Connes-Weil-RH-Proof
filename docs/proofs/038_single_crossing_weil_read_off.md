# Single-Crossing Weil Read-Off

Date: 2026-07-12

Status: the half-line single-crossing trace gives the exact prime-power Weil
coefficient and the same convolution square. This closes the local principal
channel used by plans 036--037. The global Sonin decomposition and compact
remainder sign remain open. RH remains unproved.

## 1. Partial Translation Geometry

Use the additive log coordinate and conventions

```text
(U_b psi)(x)=psi(x-b),
P=1_[0,infinity),
Q=I-P.
```

For `b>0`, one cross-half-line block is

```text
J_b=Q U_(-b) P.                                          (R.1)
```

It translates `L2(0,b)` unitarily onto `L2(-b,0)` and vanishes on the rest of
`Ran(P)`.

Let `C_h` be convolution by a compact smooth function `h`, and put

```text
F_h=h* * h.
```

Then `C_h* C_h` is convolution by `F_h`. The trace of the single crossing is

```text
Tr(C_h* C_h J_b)=b F_h(b).                               (R.2)
```

Indeed, the diagonal trace of the product forces the translation relation
`x-y=b`; the cutoff conditions restrict the free variable to one interval of
length exactly `b`, while the convolution kernel is constant along that
translation graph and equals `F_h(b)`.

The adjoint crossing supplies the reflected value:

```text
Tr(C_h* C_h (J_b+J_b*))
  = b(F_h(b)+F_h(-b)).                                   (R.3)
```

For Hermitian convolution squares this is `2b Re(F_h(b))`.

## 2. Prime-Power Coefficient

For the `m`-th Euler power, put

```text
b=m log(p),
a=p^-1/2.
```

The logarithmic metric flow in plan 036 gives coefficient `a^m/m` for the
single-crossing `U_p^m` channel. Combining it with (R.3) gives

```text
(a^m/m) b(F_h(b)+F_h(-b))

  = p^(-m/2) log(p)
    (F_h(m log(p))+F_h(-m log(p))).                      (R.4)
```

Under the multiplicative dictionary, the two values in (R.4) are exactly the
`p^m` and `p^-m` evaluations of the same convolution square. Thus (R.4) is the
finite-prime Weil atom with no additional sign or normalization convention.

## 3. Consequence For The Old Noncompact Block

The project sign is fixed as well. The first metric-projection variation is

```text
P_1=-(J_b+J_b*),                                         (R.5)
```

so the single-prime contribution to the positive Sonin trace carries the
negative of (R.3). CCM25 defines

```text
QW=archimedean+pole-sum_p W_p,                           (R.6)
```

with each local atom `W_p` positive in the normalization (R.4). Therefore the
metric trace and `QW` have the same finite-prime sign. No sign is absorbed into
the local atom.

The unsmoothed partial translation `J_b` has infinite rank and is not compact.
Plans 025--026 correctly rejected treating it as part of a compact remainder.
Equation (R.4) identifies its proper owner: it is the finite-prime Weil main
term itself.

After subtracting the signed main term (R.5)--(R.6) from the metric Sonin
trace, every remaining Euler word
either:

```text
crosses a cutoff boundary at least twice, or
contains the trace-class prolate correction K_prol.      (R.5)
```

Those are precisely the trace-class classes established in plan 037.

## 4. Remaining Global Identification

The archimedean Sonin projection is built from both the support cutoff and its
Fourier conjugate. To finish the fixed-S trace identity one must expand the
metric projection through the CC20 angle decomposition and verify that its
two single-crossing orientations are exactly the pair in (R.3). The local
kernel calculation cannot determine the final project sign by itself, but it
fixes the magnitude, prime-power index, and same-test ownership.

The remaining global remainder is compact. Its norm/sign is the only open
part of this read-off lane.

## 5. Verdict

```text
partial translation geometry: exact.
same convolution square: exact.
p^(-m/2) log(p) coefficient: exact.
CCM25 QW sign: exact and matching.
raw noncompact Euler block: assigned to Weil main term, not remainder.
multi-crossing remainder: trace class by plan 037.
global Sonin sign and compact norm: open.
RH: unproved.
```
