# Proof 333: Q-annihilated half-power tail

Date: 2026-07-17

Status: source-backed far-tail refinement after Proofs 276, 302, and 331. The
CC20 static archimedean and prolate coefficients have a leading
`rho^(-1/2)` boundary mode. When the logarithmic root differential

```text
Q=-(rho partial_rho)^2+1/4
```

is transferred distributionally onto a compact cross-correlation, that mode
is annihilated exactly. The remaining translated pairing has the next
half-density decay. This is a genuine far-prime mechanism, not the complete
moving Toeplitz covariance or Gate 3U.

## 1. Result

```text
+------------------------------------------------+----------------------------+
| layer                                          | judgment                   |
+------------------------------------------------+----------------------------+
| CC20 delta leading rho^(-1/2) mode            | explicit                   |
| delta remainder O(rho^(-3/2))                 | proved from Si expansion   |
| CC20 epsilon prolate leading mode             | exact convergent series    |
| epsilon remainder O(rho^(-3/2))               | oscillatory-integral lemma |
| Q transfer to compact root                    | exact                       |
| leading half-power after Q pairing            | zero                        |
| far translated static pairing                 | next half-density decay    |
| compressed Sonin Toeplitz product             | not controlled here        |
| near-prime complete-product stopping          | open                       |
| Gate 3U                                       | open                       |
+------------------------------------------------+----------------------------+
```

The new mechanism is

```text
d(z)=c exp(-z/2)+r(z),   r(z)=O(exp(-3z/2))
                 |
                 | <Qd,F_z>=<d,QF_z>
                 v
leading term =c exp(-z/2) integral exp(u/2)QF(u)du=0.
                                                               (BQ.1)
```

Proof 276 used only an absolute `O(exp(-z/2)(1+z))` bound and therefore could
not see `(BQ.1)`.

## 2. Explicit CC20 delta expansion

CC20 equation `sch18intro` is

```text
delta(rho)
 =2 sqrt(rho)[
   Si(2 pi(1+rho))/(2 pi(1+rho))
  +Si(2 pi(rho-1))/(2 pi(rho-1))].                  (BQ.2)
```

The standard integration-by-parts expansion

```text
Si(x)=pi/2-cos(x)/x+O(x^(-2))                       (BQ.3)
```

gives, uniformly for `rho>=2`,

```text
delta(rho)=rho^(-1/2)+O(rho^(-3/2)).                (BQ.4)
```

Indeed, the two `pi/2` terms equal

```text
sqrt(rho)/2[1/(rho+1)+1/(rho-1)]
 =rho^(-1/2)+O(rho^(-5/2)),                         (BQ.5)
```

while the cosine terms in `(BQ.3)` are
`O(sqrt(rho) rho^(-2))=O(rho^(-3/2))`.

For integral `rho`, where both cosines equal one, the first correction tends
to `-1/pi^2`. The numerical readback is

```text
+-------+------------------+---------------------------+
| rho   | sqrt(rho) delta  | rho^(3/2)(delta-rho^-1/2)|
+-------+------------------+---------------------------+
|   100 | 0.9990864993     | -0.0913501                |
|  1000 | 0.9998996785     | -0.1003215                |
| 10000 | 0.9999898779     | -0.1012212                |
+-------+------------------+---------------------------+
```

Since `1/pi^2=0.101321...`, this also checks the sign and scale of the first
oscillatory correction.

## 3. CC20 prolate expansion has the same leading mode

The original CC20 TeX gives

```text
epsilon(rho)
 =sum_n lambda_n^2/(1-lambda_n^2)
   rho^(1/2) integral_(1/rho)^1
     xi_n^an(x) xi_n^an(rho x) dx.                  (BQ.6)
```

Equivalently, using `eta_n=lambda_n xi_n^an` outside the support interval,

```text
epsilon_n(rho)
 =lambda_n/(1-lambda_n^2) rho^(-1/2)
   integral_1^rho xi_n(y/rho) eta_n(y) dy.           (BQ.7)
```

Here `eta_n` is the cosine transform of the compactly supported smooth prolate
vector `xi_n`. Repeated integration by parts gives a convergent primitive and

```text
A_n(Y):=integral_1^Y eta_n(y)dy
       =L_n+O(poly(n)/Y).                            (BQ.8)
```

The source bounds `Rokh`, `boundWang`, and the displayed `D_u xi_n` bound make
the constant in `(BQ.8)` polynomial in `n`. Integrate `(BQ.7)` by parts against
`A_n`. Since `xi_n` is even, `xi_n'(0)=0`; one obtains

```text
integral_1^rho xi_n(y/rho)eta_n(y)dy
 =xi_n(0)L_n+O(poly(n)/rho).                         (BQ.9)
```

Consequently

```text
epsilon(rho)=c_epsilon rho^(-1/2)
              +O(rho^(-3/2)),                       (BQ.10)

c_epsilon
 =sum_n lambda_n xi_n(0)L_n/(1-lambda_n^2).          (BQ.11)
```

Both series converge absolutely: CC20's `rapid-decay` estimate makes
`lambda_n` super-exponentially small against every polynomial, and every fixed
low-mode denominator is nonzero.

Primary source:

```text
Connes--Consani, Weil positivity and Trace formula,
arXiv:2006.13771.
https://arxiv.org/abs/2006.13771

Original source labels:
spectral, rapid-decay, sonine0, sonineQbis, Rokh, boundWang.
```

## 4. Distributional Q cancellation

Write `rho=exp(z)` and let

```text
d(z)=c exp(-z/2)+r(z),
|r(z)|<=A exp(-3z/2),   z>=z_0.                      (BQ.12)
```

For `F in C_c^2(R)` and a translate `F_z`, distributional self-adjointness is

```text
<Qd,F_z>=<d,QF_z>,
Q=-partial_u^2+1/4.                                  (BQ.13)
```

The leading mode contributes

```text
c exp(-z/2) integral_R exp(u/2)
  (-F''(u)+F(u)/4)du=0.                              (BQ.14)
```

Equation `(BQ.14)` follows by two integrations by parts; compact support
deletes both boundary terms and `Q exp(u/2)=0`. Therefore only `r` remains.
For `supp(F) subset [-B,B]` and `z>=z_0+B`,

```text
|<Qd,F_z>|
 <=A exp(-3z/2)
   integral_(-B)^B exp(3u/2)|QF(u)|du.               (BQ.15)
```

This proves a far-displacement gain. The weighted integral in `(BQ.15)` is not
yet the polynomial support-width bound required by Gate 3U.

## 5. Near/far split required for Gate 3U

The exponential support factor in `(BQ.15)` must not be bounded globally. Use
two regions:

```text
far modes:  z>c B_root
  -> (BQ.15) is absolutely summable after the extra decay;

near modes: z<=c B_root
  -> keep the complete normalized Euler product;
  -> use compact stopping and a square-function / graded-coboundary estimate;
  -> do not count Boolean histories by total variation.           (BQ.16)
```

The far region is now reduced to a source-backed asymptotic theorem. The near
region remains the same-object finite-`S` bottom.

## 6. Reproduction

Run in WSL2 without a Lean build:

```text
python3 -B docs/proofs/333_q_annihilated_half_power_tail_probe.py
```

The probe uses only the explicit CC20 `delta` formula. With
`F(u)=(1-(u/B)^2)^3` on `[-B,B]`, `B=1.3`, it reports

```text
integral exp(u/2)QF(u)du =7.04e-13,

z=5:  exp(z/2)<delta,QF_z>  =-5.65e-4,
z=8:  exp(z/2)<delta,QF_z>  =-2.71e-6,
z=10: exp(z/2)<delta,QF_z>  = 3.29e-8.               (BQ.17)
```

Thus the half-power-scaled translated pairing tends to zero after the exact
annihilation. The probe verifies the explicit branch, not the prolate series or
the moving covariance.

## 7. Route judgment

Proof 333 strengthens the usable source tail:

```text
pre-Q static coefficient:
  half-power leading mode plus next-order remainder;

post-Q compact pairing:
  half-power leading mode deleted exactly;

far prime-power modes:
  gain sufficient for absolute summation;

near complete finite-S modes:
  still require graded stopped-product control.                   (BQ.18)
```

Do not turn `(BQ.15)` into a global `exp(B_root)` estimate, and do not identify
the static coefficient with the compressed Sonin Toeplitz covariance. Gate 3U,
the finite-S sign, Burnol's identity, and RH remain open.
