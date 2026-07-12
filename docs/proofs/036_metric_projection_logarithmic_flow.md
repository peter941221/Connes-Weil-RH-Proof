# Metric Projection Logarithmic Flow

Date: 2026-07-12

Status: superseded and rejected by
`042_metric_sonin_second_prime_power_rejection.md`. The logarithmic generator
does contain `a^(m-1)U^m`, but differentiating the moving projection factors
adds another direct channel. At `p^2` the endpoint projection coefficient is
twice the Weil coefficient, so the nonlinear terms cannot all be assigned to a
compact defect remainder. RH remains unproved.

## 1. Exact Projection Flow

For one prime, let

```text
T_a=I-aU,
U=exp(-i log(p)D),
R_a=projection onto T_a Ran(R),
0<=a<1.                                                  (L.1)
```

The metric formula of plan 034 defines `R_a` exactly. Its right logarithmic
generator is

```text
X_a=(partial_a T_a)T_a^-1
   =-U(I-aU)^-1
   =-sum_(m>=1) a^(m-1) U^m.                             (L.2)
```

The series converges in operator norm for `a<1`.

For any differentiable closed-subspace flow `Ran(R_a)=T_a Ran(R)`, the
orthogonal projection satisfies

```text
partial_a R_a
  =(I-R_a)X_aR_a+R_aX_a*(I-R_a).                         (L.3)
```

Equation (L.3) follows by differentiating `R_a^2=R_a` and the fact that
`X_a` transports vectors in the moving range. At `a=0`, it reproduces
`-QUR-RU*Q` from plan 035.

## 2. Prime-Power Channel

Every term `U^m` in (L.2) is scaling translation by `m log(p)`. At the base
projection, its single-boundary-crossing part is
`Q U^m R+R U*^m Q`. Integrating the generator coefficient gives

```text
integral_0^a t^(m-1) dt = a^m/m.                         (L.4)
```

This is exactly the coefficient in

```text
log(1-aU)=-sum_(m>=1) a^m U^m/m.                         (L.5)
```

The support-preserving scaling differential contributes `m log(p)` on the
`m log(p)` translation. Thus the direct channel has coefficient

```text
(a^m/m) * m log(p)=p^(-m/2) log(p),                      (L.6)
```

the finite-prime Weil coefficient.

This is an operator generating-series match for the single-crossing channel.
Turning it into a trace read-off still requires cyclicity, trace-class control,
and proof that multi-crossing words remain in the remainder rather than
changing the arithmetic coefficient.

## 3. Where Nonlinear Terms Go

The moving projections in (L.3) also depend on `a`. Expanding them produces
mixed words containing interruptions by `R` and `Q=I-R`. At second order they
are the paired defects `-J*J` and `JJ*` from plan 035. At higher orders they
remain words with at least one Sonin boundary crossing.

Therefore the expansion separates as

```text
single-crossing words Q U^m R and their adjoints
  -> prime-power channel (L.6),

words containing R/Q interruptions
  -> fixed-support metric remainder.                     (L.7)
```

No claim is made that the interrupted words vanish. The remaining theorem is
that, after inserting the same compact test and applying `Q`, their total is
nonpositive or has only finitely many bad directions that the route
vanishing/conditioning removes.

## 4. Multi-Prime Additivity

For finite `S`, the transfer factors commute because every `U_p` is a function
of the same scaling generator:

```text
T_S=product_(p in S_f)(I-p^-1/2 U_p).                    (L.8)
```

The logarithmic derivative in any one prime parameter has the form (L.2), so
the single-crossing generator channels are additive over primes. Mixed-prime
words acquire additional projection-boundary crossings and belong to the
remainder side of (L.7). This names the exact cancellation obligation: the
Weil functional has no mixed-prime atoms, so all mixed interrupted words must
cancel or be controlled without being read as arithmetic main terms.

## 5. Next Rejection Test

For `S={infinity,2}`, compute the trace of the full second variation against
one convolution square:

```text
Tr(C(g) P_2 C(g)*).                                      (L.9)
```

Split (L.9) into:

```text
Q U^2 R single-crossing       -> required p^2 atom,
paired J*J/JJ* channel        -> central defect remainder,
second-order off-diagonal     -> boundary remainder.
```

If the latter two channels reproduce a positive noncompact translation block
after `Q`, the metric route is rejected. If they are trace class with only a
finite bad spectrum, the old fixed-S obstruction has been converted into the
kind of conditioning CC20 can handle.

## 6. Verdict

```text
all p^m translations: present in the logarithmic generator.
endpoint coefficient: wrong from p^2 onward after moving-projector terms.
raw central p^-1 identity: canceled by metric normalization.
moving-projector direct channel: supplies the fatal extra p^2 copy.
multi-prime direct additivity: exact.
metric Sonin route: rejected.
RH: unproved.
```

The operator-ideal estimates for genuine multi-crossing words remain useful,
but the excess `p^2` word is a single crossing and is not in that ideal. See
`docs/proofs/042_metric_sonin_second_prime_power_rejection.md`.
