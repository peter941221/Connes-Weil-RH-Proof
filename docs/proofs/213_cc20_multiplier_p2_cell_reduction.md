# Proof 213: CC20 multiplier reduction for the p=2 eight-cell gate

Date: 2026-07-13

Status: superseded and rejected as a same-object route gate by Proof 217.  The
calculation below bounds the prime translation on `g` while applying the CC20
Q-image coercivity as though the same `g` were the pre-root.  In the genuine
identity the prime term is `<L xi,K_2 L xi>` and the M4 remainder acts on
`xi`, with `L=d/dx+1/2`.  The global explicit archimedean bound

```text
2 theta'(t)+delta_hat(t) >= 1/50                         (M.1)
```

is independently valid by Proof 214, and the cell algebra below is valid for
the displayed wrong-object form.  It does not prove domination of the complete
same-object `p=2` channel.  The corrected screen is about `-2.026` at grid size
1000.  RH remains unproved.

## 1. Source multiplier

CC20 proves that the positive angle functional has Fourier representation

```text
L(f)
 = integral f_hat(t) ell_CC20(t) dt/(2 pi),

ell_CC20(t)=2 theta'(t)+delta_hat(t) >= 0.               (M.2)
```

Source: `weil-compo.tex:586-604`, Corollary `corlittlesq`, and
`weil-compo.tex:631-661` for the explicit cosine transform of `delta`:

```text
https://arxiv.org/abs/2006.13771
```

For a root `g` and

```text
Q_+=-partial_x^2+1/4,
```

Plancherel gives

```text
L(Q_+(g*g^*))
 = integral (t^2+1/4)|g_hat(t)|^2 ell_CC20(t) dt/(2 pi).
                                                               (M.3)
```

Consequently (M.1) would imply the common-domain coercive estimate

```text
L(Q_+(g*g^*))
 >= (1/50)(||g'||_2^2+(1/4)||g||_2^2).                 (M.4)
```

Unlike a new Weil-sign premise, (M.1) concerns one explicit archimedean
function already known to be nonnegative by a positive operator trace.

## 2. Eight-cell decomposition

Use the notation of proof 212:

```text
L=log(2),
I=[0,8L),
I_j=[jL,(j+1)L).
```

For `g` in the form core, write on each cell

```text
g(jL+t)=v_j+r_j(t),
v_j=(1/L) integral_0^L g(jL+t)dt,
integral_0^L r_j(t)dt=0.                               (M.5)
```

The `p=2` translation operator is fiberwise in `t`:

```text
K_2(t)=K_8,
(K_8)_(ij)=L 2^(-|i-j|/2) for i!=j,
(K_8)_(ii)=0.                                          (M.6)
```

Because every `r_j` has zero cell average, the average/residual cross term
vanishes exactly:

```text
<g,K_2 g>
 = L <v,K_8 v>
   + integral_0^L <r(t),K_8 r(t)>dt.                   (M.7)
```

Likewise

```text
||g||_2^2=L||v||^2+sum_j||r_j||_2^2.                  (M.8)
```

This is the key benefit of using cells aligned with the prime translation.

## 3. Average block

The route condition `g_hat(0)=0` gives

```text
sum_j v_j=0.                                           (M.9)
```

Let `w_m=L 2^(-m/2)` and let `d_i=sum_(j!=i)w_|i-j|` be the weighted cell
degree.  The graph identity is

```text
<v,K_8v>
 = sum_i d_i|v_i|^2
   -sum_(i<j)w_|i-j||v_i-v_j|^2.                       (M.10)
```

On (M.9),

```text
sum_(i<j)|v_i-v_j|^2=8||v||^2.                         (M.11)
```

The maximum degree is

```text
d_max=2(w_1+w_2+w_3)+w_4,
```

and every edge weight is at least `w_7`.  Hence

```text
<v,K_8v> <= (d_max-8w_7)||v||^2.                       (M.12)
```

The elementary bounds

```text
log(2)<7/10,
log(2)>693/1000,
707/1000<1/sqrt(2)<708/1000
```

give by exact rational arithmetic

```text
2-(d_max-8w_7) > 0.1237988432.                         (M.13)
```

Thus the scalar `2 Id` already dominates the average block.  Neither pole row
is needed for this estimate.

## 4. Cell-residual block

Schur's row-sum bound and (M.6) give

```text
<r(t),K_8r(t)> <= d_max ||r(t)||^2.                    (M.14)
```

The mean-zero Poincare inequality on each cell gives

```text
sum_j||r_j||_2^2
 <= (L/pi)^2 ||g'||_2^2.                               (M.15)
```

Assuming (M.1), combine (M.4), (M.14), and (M.15):

```text
L(Q_+(g*g^*))+2 sum_j||r_j||^2
  -integral_0^L<r(t),K_8r(t)>dt

 >= [2-d_max+(pi/L)^2/50] sum_j||r_j||^2.              (M.16)
```

Using only

```text
pi>3,
L<7/10,
1/sqrt(2)<708/1000,
```

the bracket in (M.16) has the exact rational lower bound

```text
3136274837/1914062500000
  > 0.0016385435.                                      (M.17)
```

The actual numerical margin is much larger.  Equation (M.17) is deliberately
crude so the conditional implication does not depend on numerical linear
algebra.

## 5. Superseded p=2 claim

Equations (M.7)-(M.17), together with Proof 214, prove only the displayed
raw-vector inequality:

```text
Every form-core g supported in an interval of length 8log(2) with
g_hat(0)=0 satisfies

L(Q_+(g*g^*))+2||g||_2^2-<g,K_2g> >= 0.                (M.18)
```

The two pole vanishings can be imposed simultaneously because (M.18) already
holds on the larger zero-mean domain.

This is not the CC20 Q-root relative form.  For the same Q-image, the finite
prime term must also receive the `L=d/dx+1/2` multiplier.  Proof 217 gives the
exact ownership diagram and the corrected numerical death test.

## 6. Discharge of the multiplier lemma

The source formulas used by the probe are

```text
2 theta'(t)
  = -log(pi)+Re digamma(1/4+it/2),

delta_hat(t)
  = 2 integral_0^infinity delta(exp(x))cos(tx)dx,

delta(rho)
  = 2sqrt(rho)[Si(2pi(1+rho))/(2pi(1+rho))
                +Si(2pi(rho-1))/(2pi(rho-1))].         (M.19)
```

Scanning `[0,50]`, with a refined grid on `[0,0.5]`, gives approximately

```text
minimum sampled ell_CC20:  0.0490
target lower bound:         0.0200
observed spare margin:      0.0290
```

Proof 214 replaces this screen with a valid producer:

```text
compact interval:
  1251 Arb Taylor enclosures on [0,50];

large |t| tail:
  monotonicity of 2 theta', an explicit variation bound for delta, and
  an Arb endpoint check at t=50.
```

The certified lower endpoints are `0.0290514...` on the compact interval and
`0.0741292...` on the large-frequency tail, both strictly above `1/50`.

## 7. Reproduction

The reconnaissance script requires SciPy:

```text
python3 -B docs/proofs/213_cc20_multiplier_p2_cell_probe.py \
  --t-max 50 --step 0.1 --refine-max 0.5 --refine-step 0.005
```

It also prints the exact rational margins (M.13) and (M.17).  Do not promote
its sampled multiplier minimum to a theorem.

## 8. Route judgment

```text
same-object p=2 translation owner:       exists, but acts on L xi
eight-cell average/residual split:       exact
average block below scalar 2:            exact
residual block under (M.1):              exact
global ell_CC20>=1/50:                   passed independently by Proof 214
claimed p=2 domination:                  rejected by Proof 217
CC20 compact remainder:                  not yet reinserted
new Lean owner:                           defer until the all-prime form exists
RH:                                       unproved
```

The next useful action is to retain the full `ell_CC20` multiplier on the
source root and compare it with the prime translation sum before reinserting
the named compact CC20 window operator.
