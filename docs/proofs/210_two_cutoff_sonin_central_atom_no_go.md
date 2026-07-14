# Proof 210: two-cutoff Sonin central-atom no-go

Date: 2026-07-13

Status: the bounded two-cutoff positive-angle family is rejected as the
finite-S post-Q owner.  Every nonzero finite-cutoff angle, including a
positive difference of nested Fourier cutoffs, carries a strictly positive
central Euler atom.  After Q this is an unbounded positive second-order form.
Changing the two cutoffs can make its coefficient small, but cannot make it
zero at any finite cutoff.  RH remains unproved.

## 1. Result

For one prime put

```text
a = p^(-1/2),
L = log(p),
(T_b xi)(x) = xi(x-b),
P_r = 1_[r,infinity).
```

The finite Euler phase has the norm-convergent Laurent expansion

```text
v_a = sum_m c_m T_(mL),
c_1 = -a,
c_(-j) = (1-a^2)a^j  for j >= 0.
```

For independently chosen support and Fourier thresholds, the natural positive
angle owner is

```text
B_(r,s)(a) = P_r v_a^* (1-P_s) v_a P_r >= 0.            (A.1)
```

Its trace against a convolution-square kernel has a central `F(0)` coefficient

```text
b_(r,s)(a)
  = sum_m |c_m|^2 (s-r-mL)_+ > 0                        (A.2)
```

for every finite pair `(r,s)`.  At the equal cutoff `r=s`, formula (A.2)
reduces exactly to

```text
b_(r,r)(a) = a^2 log(p),                                (A.3)
```

the central coefficient found in proof 026.  Thus the extra cutoff parameter
does not cancel the obstruction.

## 2. What the two parameters really are

CC20 defines

```text
S(alpha,beta)
  = {xi : xi vanishes on [-alpha,alpha]
          and Fourier(xi) vanishes on [-beta,beta]}.
```

Source: `weil-compo.tex:986-988`, Definition `defnsonine`,
https://arxiv.org/abs/2006.13771.

The scaling action is

```text
(rho(t)xi)(x) = t^(-1/2) xi(t^(-1)x).
```

Source: `weil-compo.tex:908-910`, equation `vrepdefnadd`.

Direct Fourier covariance gives

```text
rho(t) S(alpha,beta) = S(t alpha,beta/t).
```

Therefore `alpha beta` is the only scaling-invariant cutoff parameter.  In the
additive log coordinate, if

```text
r = log(alpha),
s = -log(beta),
```

then the invariant is

```text
c = r-s = log(alpha beta).                              (A.4)
```

This is why two apparent cutoff knobs reduce to one genuine separation.

CC20 uses `alpha=beta=1`.  Its projection relations are recorded at
`weil-compo.tex:882-918`.  Connes 1999 likewise defines the infrared and
Fourier cutoffs using the same `Lambda`, not two independent parameters;
see `zeta.tex:1387-1403`, equations (15)-(16), in
https://arxiv.org/abs/math/9811068.  Thus (A.1) is the most direct independent
two-cutoff extension, not a theorem already supplied by either source.

## 3. Exact angle algebra

Let

```text
H_s = 2P_s-1,
T_s(v) = v^* H_s v-H_s.
```

Then

```text
v^*(1-P_s)v = (1-H_s-T_s(v))/2,
```

and hence

```text
B_(r,s)(a)
  = P_r(1-P_s)P_r - (1/2)P_r T_s(v_a)P_r.              (A.5)
```

The first term is the explicit cutoff-overlap bulk

```text
P_r(1-P_s)P_r = 1_[r,s)  if r<s,
                 0       if r>=s.                       (A.6)
```

At `r=s`, (A.5) is exactly the CC20 projection algebra

```text
P P_hat P = -(1/2) P T P.
```

Source: `docs/proofs/016_corrected_trace_identity.md`, equations (4)-(8),
derived from CC20 `weil-compo.tex:536-559` and `1141-1186`.

For `r<s`, the new term (A.6) has positive sign.  It cannot be advertised as
the negative correction needed to remove the finite Euler principal part.

## 4. Derivation of the central coefficient

Expand (A.1).  A term with indices `(m,n)` translates by `(n-m)L`.  Only
`m=n` contributes to the coefficient of `F(0)`.  For that diagonal term,

```text
T_(-mL) (1-P_s) T_(mL) = 1_(-infinity,s-mL),
```

so the spatial interval surviving both `P_r` factors has length

```text
length([r,infinity) intersect (-infinity,s-mL))
  = (s-r-mL)_+.
```

This proves (A.2).  The coefficients satisfy

```text
sum_m |c_m|^2 = 1,
sum_m m |c_m|^2 = 0.                                   (A.7)
```

Put `q=a^2` and `c=r-s`.  Summing the geometric series gives the closed form

```text
b_c(a) = -c,                                  c <= -L;

b_c(a) = (1-q)(-c)+qL,                       -L <= c <= 0;

b_c(a) = q^(n+1) [L-(1-q)(c-nL)],
                 nL <= c <= (n+1)L, n >= 0.             (A.8)
```

Every line in (A.8) is strictly positive for finite `c`.  In the last line,

```text
L-(1-q)(c-nL) >= qL > 0.
```

At integer positive separations this becomes

```text
b_(nL)(a) = L a^(2n+2).                                 (A.9)
```

Thus moving the cutoff by `n log(p)` only pushes the obstruction to the next
geometric scale.  It never removes it.

## 5. Positive cutoff differences do not escape

The one genuine monotonicity is obtained by varying the outer Fourier
projection while keeping `P_r` fixed.  For `s_2<s_1`,

```text
P_r v_a^* 1_[s_2,s_1) v_a P_r >= 0.                    (A.10)
```

This is the positive difference of two nested Fourier-cutoff angles.  Its
central coefficient is

```text
sum_m |c_m|^2
  length([r,infinity) intersect [s_2-mL,s_1-mL)).       (A.11)
```

Formula (A.11) is strictly positive for every nonempty band.  Indeed, for all
sufficiently large `j`, the term `m=-j` contributes the full band length
`s_1-s_2`, and `|c_(-j)|^2>0`.

Varying the inner support compression does not provide a second monotonicity.
For nested projections `P_2<=P_1` and a positive `Q`, the difference

```text
P_1 Q P_1-P_2 Q P_2
```

has block form

```text
[ Q_00  Q_01 ]
[ Q_10    0  ].                                        (A.12)
```

Positivity of (A.12) forces `Q_01=0`.  The Fourier/Euler angle projection does
not commute with a support boundary, so its off-diagonal block is nonzero.
Consequently a support-cutoff difference is not positive in general.  If one
replaces it by an actual positive support shell, the same diagonal calculation
as (A.11) again gives a strictly positive central coefficient.

## 6. Post-Q death test

The finite-prime Weil distribution has atoms only at nonzero
`+/-m log(p)`.  It has no atom at zero.  Therefore the central term (A.2)
belongs to the two-cutoff remainder, not to the desired prime read-off.

Apply

```text
Q_+ = -partial_r^2+1/4.
```

The central atom contributes

```text
b_(r,s)(a) [-F''(0)+(1/4)F(0)].                         (A.13)
```

Choose a real nonzero smooth `phi` supported in an interval of width less than
`L`, and set

```text
xi_t(x) = exp(itx) phi(x),
F_t = xi_t * xi_t^*.
```

All values and derivatives of `F_t` at nonzero `mL` vanish.  The leading term
of (A.13) is

```text
b_(r,s)(a) t^2 ||phi||_2^2.                             (A.14)
```

It tends to positive infinity.  The archimedean CC20 post-Q remainder is
`-2 Id+compact`, hence bounded on this normalized modulation sequence.  The
mixed archimedean/Euler cocycle term has no Dirac mass before Q and becomes a
compact fixed-window form; this was proved in
`docs/proofs/026_semilocal_cocycle_renormalization.md`, Sections 4-5.  Neither
can cancel (A.14).

Taking `c` to positive infinity makes (A.9) tend to zero, but at the same time
the compressed positive angle tends strongly to zero on every fixed smoothed
test.  The remainder tends to the negative of the entire uncompressed Weil
functional.  This limiting tautology supplies no uniform sign theorem, and
for every finite `c` the modulation test (A.14) still fails.

## 7. Scope and route judgment

```text
independent finite Sonin cutoffs:       one invariant c=log(alpha beta)
single positive two-cutoff angle:       rejected by b_c(a)>0
positive Fourier-band difference:      rejected by a positive central atom
support-compression difference:         not positive unless the cross block dies
finite cutoff sent to infinity:         positive owner collapses; no uniform sign
bounded two-cutoff post-Q route:         rejected
common-domain relative form:            not covered
Lean owner:                              forbidden for the rejected family
RH:                                      unproved
```

The remaining operator lane must subtract or renormalize the central
second-order form on a common domain while proving that the resulting relative
form is still positive.  That is an unbounded relative-form problem; it cannot
be obtained from another finite positive cutoff angle or from a positive band
difference.

Primary sources:

```text
https://arxiv.org/abs/2006.13771
https://arxiv.org/abs/math/9811068
```
