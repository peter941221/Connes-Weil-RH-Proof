# Proof 214: global lower certificate for the CC20 positive multiplier

Date: 2026-07-13

Status: accepted computer-assisted archimedean theorem.  For every real `t`,

```text
ell_CC20(t):=2 theta'(t)+delta_hat(t) > 1/50.            (C.1)
```

The proof combines analytic tail and derivative bounds with 1251 Arb-certified
Taylor intervals on `[0,50]`.  It is independent of RH and of every finite
prime.  Proof 217 withdraws the earlier claim that this theorem, combined with
Proof 213, passes the same-object `p=2` gate: the Q-root and source root were
mixed.  The multiplier theorem itself is unaffected.  RH remains unproved.

## 1. Source function

CC20 proves

```text
ell_CC20(t)=2 theta'(t)+delta_hat(t) >= 0,

2 theta'(t)
  = -log(pi)+Re digamma(1/4+it/2),

delta_hat(t)
  = 2 integral_0^infinity d(x)cos(tx)dx,

d(x)=delta(exp(x)).                                     (C.2)
```

It gives

```text
delta(rho)
 = 2sqrt(rho)[Si(2pi(1+rho))/(2pi(1+rho))
              +Si(2pi(rho-1))/(2pi(rho-1))].           (C.3)
```

Source: `weil-compo.tex:586-604` and `631-661`,
https://arxiv.org/abs/2006.13771.

The source proves only nonnegativity.  The strict uniform constant in (C.1) is
new project evidence.

## 2. Explicit tail remainder

For positive `z`, one integration by parts gives

```text
|Si(z)-pi/2| <= 2/z.                                   (C.4)
```

Insert (C.4) into (C.3).  The leading `pi/2` terms sum to

```text
rho^(3/2)/(rho^2-1).
```

For `rho>=2`, direct comparison with `rho^(-1/2)` gives

```text
|delta(rho)-rho^(-1/2)| <= 2rho^(-3/2).                (C.5)
```

With `X=8`, (C.5) implies

```text
|2 integral_X^infinity
    [d(x)-exp(-x/2)]cos(tx)dx|
 <= (8/3)exp(-3X/2),                                   (C.6)

|d/dt 2 integral_X^infinity
    [d(x)-exp(-x/2)]cos(tx)dx|
 <= 4exp(-3X/2)[X/(3/2)+1/(3/2)^2].                    (C.7)
```

The certificate integrates the leading `exp(-x/2)` tail exactly and charges
(C.6)-(C.7) explicitly.  At `X=8`, the two charges are

```text
value error:       1.6384566275542e-5,
derivative error:  1.4199957438803e-4.                 (C.8)
```

## 3. Global second-derivative bound

The polygamma series at `z=1/4+it/2` gives

```text
|(d^2/dt^2) Re digamma(z)|
 <= (1/2)sum_(n>=0)(n+1/4)^(-3)
 < 33.                                                  (C.9)
```

For the cosine-transform term,

```text
|delta_hat''(t)| <= 2 integral_0^infinity x^2 d(x)dx.  (C.10)
```

The elementary source bounds `Si(z)/z<=1` and `Si(z)<=2` give

```text
d(x)<8,                       0<=x<=1,
d(x)<(8/5)exp(-x/2),          x>=1.                    (C.11)
```

Using

```text
integral_1^infinity x^2 exp(-x/2)dx=26exp(-1/2),
exp(-1/2)<2/3,
```

equations (C.10)-(C.11) give

```text
|delta_hat''(t)| < 61.                                 (C.12)
```

Combining (C.9) and (C.12), the certificate uses the safe global bound

```text
|ell_CC20''(t)| < 100.                                 (C.13)
```

## 4. Compact interval certificate

At each grid center

```text
t_j=j/25,  0<=j<=1250,
```

Arb evaluates in one complex integral both

```text
2 integral_0^8 d(x)cos(t_j x)dx
```

and its `t` derivative.  The removable singularity in `Si(z)/z` is evaluated
as the entire hypergeometric function

```text
1F2(1/2;3/2,3/2;-z^2/4).                              (C.14)
```

For every `t` with `|t-t_j|<=1/50`, Taylor's theorem, (C.7), and (C.13) give
the certified lower enclosure

```text
ell_CC20(t)
 >= ell_ball(t_j)
      - valueTailError
      - (|ell'_ball(t_j)|+derivativeTailError)/50
      - 100/(2*50^2).                                  (C.15)
```

Every one of the 1251 comparisons in (C.15) is strictly above `1/50`.
The smallest lower endpoint occurs at `t_0=0`:

```text
minimum compact lower = 0.029051430687854... > 0.02.   (C.16)
```

The comparison uses Arb balls directly.  Floating-point conversion is used
only to print the location and the human-readable minimum.

## 5. Large-frequency certificate

Differentiate the first term in (C.2).  The trigamma series shows that

```text
t -> 2 theta'(t)
```

is increasing for `t>0`: every summand has strictly negative imaginary part
before multiplication by `-1/2`.

For the second term, write

```text
q(z)=Si(z)/z=integral_0^1 sinc(zs)ds.
```

On `[0,1]`, `|q|<=1` and `|q'|<=1/4`, which gives `|d'|<42`.  For `x>=1`,
the bounds `Si<=2` and `|q'|<=3/z^2` give

```text
|d'(x)|<6exp(-x/2).
```

Hence

```text
integral_0^infinity |d'(x)|dx < 50.                    (C.17)
```

One integration by parts now yields

```text
|delta_hat(t)| < 100/t.                                (C.18)
```

At `t=50`, Arb proves

```text
2 theta'(50)
 = 2.07412927118522110406788...,

2 theta'(50)-100/50
 = 0.07412927118522110406788... > 1/50.                (C.19)
```

Monotonicity and (C.18) extend (C.19) to every `t>=50`.  Evenness of both
terms in (C.2) covers negative `t`.  Together with Section 4, this proves
(C.1) on the whole real line.

## 6. Reproduction

The certificate requires `python-flint`:

```text
python3 -B docs/proofs/214_cc20_multiplier_lower_certificate.py
```

Accepted output:

```text
grid_count=1251
compact_interval=[0,50]
minimum_compact_lower=0.029051430687854
minimum_compact_location=0.000000000000
large_t_lower=[0.07412927118522110406788 +/- 8.18e-24]
certificate=ell_CC20(t) > 1/50 for every real t
```

The accepted run used Arb precision 80 bits.  The code aborts at the first
grid interval whose lower ball does not exceed `1/50`.

## 7. Consequence and scope

Combining (C.1) with Plancherel gives the unconditional form estimate

```text
L(Q_+(g*g^*))
 > (1/50)(||g'||_2^2+(1/4)||g||_2^2)                  (C.20)
```

for every nonzero form-core root `g`.  The former inference to Proof 213,

```text
L(Q_+(g*g^*))+2||g||_2^2-<g,K_(p=2,c=256)g> >= 0,
```

does not represent the same CC20 Q-root square.  In the genuine identity, the
finite-prime term acts on `L g`, where `L=d/dx+1/2`.  Proof 217 gives the exact
correction.

```text
CC20 multiplier nonnegative:             source theorem
strict uniform lower bound 1/50:         accepted Arb certificate
p=2 eight-cell relative gate:            withdrawn by Proof 217
all finite primes simultaneously:        open
ordinary CC20 compact remainder:         not reinserted
Lean theorem:                             not yet formalized
RH:                                       unproved
```

The next mathematical step must retain `ell_CC20(t)` itself in the source-root
form.  Its global minimum cannot be spent as an extra derivative budget on the
pre-root.
