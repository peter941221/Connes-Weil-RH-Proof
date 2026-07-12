# Metric Projection Second Variation

Date: 2026-07-12

Status: superseded by `042_metric_sonin_second_prime_power_rejection.md`. The
raw central identity cancels, but the surviving `U^2` single-crossing
coefficient is twice the Weil `p^2` coefficient. RH remains unproved.

## 1. Setup

Work with one prime and write

```text
a=p^-1/2,
U=exp(-i log(p)D),
T_a=I-aU,
H_a=T_a* T_a=I-a(U+U*)+a^2 I.                           (V.1)
```

Let `R` be the archimedean Sonin projection and `Q=I-R`. On `Ran(R)` put

```text
K=R(U+U*)R,
A_a=R H_a R=I_R-aK+a^2 I_R.                             (V.2)
```

The semilocal metric Sonin projection is

```text
R_a=T_a R A_a^-1 R T_a*.                                (V.3)
```

All inverses are bounded for `0<=a<1` by the metric bounds in plan 034.

## 2. Exact Expansion

On `Ran(R)`,

```text
A_a^-1
  = I_R+aK+a^2(K^2-I_R)+O(a^3).                         (V.4)
```

Substitution in (V.3) gives

```text
R_a=R+aP_1+a^2P_2+O(a^3),                               (V.5)

P_1=-UR-RU*+R(U+U*)R
   =-QUR-RU*Q.                                           (V.6)
```

Thus the first variation is purely off-diagonal relative to
`Ran(R) direct_sum Ran(Q)`, as every differentiable family of orthogonal
projections requires.

Put

```text
J=QUR : Ran(R) -> Ran(Q).                                (V.7)
```

Differentiating `R_a^2=R_a` through second order, or expanding (V.3), gives

```text
R P_2 R=-J*J,
Q P_2 Q= JJ*.                                            (V.8)
```

The off-diagonal blocks of `P_2` are determined by (V.3) but are not needed
for the central-term test.

## 3. Central Euler Cancellation

The source metric (V.1) contains the positive scalar term `a^2 I`, which is
the operator-level precursor of the fatal central `p^-1` coefficient in the
direct scalar remainder. In (V.4), compression and inversion produce the
opposite term `-a^2 I_R`. Equations (V.3)--(V.8) show that no scalar
`+a^2 R` survives.

Instead, the diagonal second variation is

```text
diag(P_2)=diag(-J*J, JJ*).                               (V.9)
```

Whenever the smoothed defect products are trace class, their unweighted traces
agree:

```text
Tr(J*J)=Tr(JJ*).                                         (V.10)
```

Thus the central term has become a defect commutator/spectral-flow pair, not a
positive multiple of the identity. This cancellation occurs before applying
the support-preserving differential operator `Q=-partial^2+1/4`; the wave
packet proof against the raw scalar `D_p o Q` does not apply to (V.9).

## 4. What Remains

For a fixed test multiplier `C(g)`, the second-order contribution is not
automatically zero:

```text
Tr(C(g) P_2 C(g)*)                                       (V.11)
```

weights the two defect spaces differently because `C(g)` does not preserve
Sonin space. The next calculation must:

```text
1. include the off-diagonal blocks of P_2;
2. identify the U^2 terms with the p^2 Weil atoms;
3. prove that the central part of (V.11) is trace class after the same test
   smoothing;
4. determine the sign of the resulting fixed-support remainder after Q.
```

The easiest old death mechanism has nevertheless been removed: there is no
uncancelled `p^-1 log(p) Id` at the metric-projection level.

## 5. Verdict

```text
raw central finite-prime identity: canceled before read-off.
first Euler coefficient: off-diagonal Sonin defect J.
second Euler coefficient: paired defects -J*J and JJ* plus off-diagonal terms.
p^2 Weil coefficient: factor 2 too large in the endpoint projection.
post-Q compact remainder: impossible with the excess single crossing.
metric Sonin escape: rejected.
RH: unproved.
```

The full parameter flow is recorded in
`docs/proofs/036_metric_projection_logarithmic_flow.md`. Its logarithmic
generator contains every `U_p^m` with coefficient `a^(m-1)`, but differentiating
the moving projection factors adds another direct channel. The resulting
endpoint coefficient is already wrong at `m=2`.
