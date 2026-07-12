# Plan 021 Divisor-Gradient Flow Rejection

Date: 2026-07-11

Verdict: **rejected.** Exact cancellation of every residual gradient in one
dyadic block increases the global weighted Hilbert energy at every tested
scale. Reprojecting the correction away from the old span does not repair the
unit step. Optimally damping the correction turns it into another single
direction with an oscillatory correlation lower bound, so it does not remove
Plan 020's inverse-projection bottom.

This experiment was derived directly from the project model. It does not use a
published theorem or claim that the construction is historically novel.

## 1. Exact Local Construction

For `gamma_k(n)={n/k}` and `Delta h(n)=h(n)-h(n-1)`, direct residue arithmetic
gives

```text
Delta gamma_k(n) = 1/k - 1_(k divides n).
```

For a block correction

```text
b_N = sum_(N<k<=2N) a_k gamma_k,
A_N = sum_(N<k<=2N) a_k/k,
```

the only block index dividing `n` when `N<n<=2N` is `k=n`. Hence

```text
Delta b_N(n) = A_N-a_n.
```

Let `r_N` be the old optimal residual and set

```text
H_N = sum_(N<n<=2N) 1/n,
A_N = -sum_(N<n<=2N) Delta r_N(n)/n / (1-H_N),
a_n = A_N-Delta r_N(n).
```

Since `H_N<log 2<1`, the coefficients are well-defined and satisfy

```text
Delta(r_N-b_N)(n)=0,  N<n<=2N.
```

The CUDA experiment confirms this identity to approximately `1e-16` or better.

## 2. Global Energy Test

The tested energy is the project criterion's weighted norm

```text
E(h) = sum_(n>=1) |h(n)|^2/(n*(n+1)).
```

`raw ratio` is `E(r_N-b_N)/E(r_N)`. `reprojected ratio` first replaces `b_N`
by `(I-P_N)b_N`, allowing the old coefficients to readjust. Cutoff was
`250000`, and the conjugate-gradient relative tolerance was `1e-11`.

```text
+------+-----------+-------------------+---------------------------+
| N    | raw ratio | reprojected ratio | best scalar cert * log(N) |
+------+-----------+-------------------+---------------------------+
| 32   | 15.7263   | 1.9108            | 0.2459                    |
| 64   | 1.3134    | 1.1667            | 0.3332                    |
| 128  | 3.3548    | 1.3145            | 0.2088                    |
| 256  | 10.1341   | 1.7789            | 0.0353                    |
| 512  | 2.9799    | 1.0870            | 0.2080                    |
| 1024 | 2.6049    | 1.1594            | 0.1630                    |
| 2048 | 4.7180    | 1.1831            | 0.2553                    |
+------+-----------+-------------------+---------------------------+
```

The local cancellation is exact, but the coefficients create divisor hits at
all later multiples. That tail propagation costs more energy than the flat
block saves. This directly rejects the proposed unit correction.

## 3. Why Damping Does Not Create A New Route

The best scalar step along `(I-P_N)b_N` always decreases energy in finite
precision when its correlation is nonzero. Proving a uniform dyadic decrement,
however, requires

```text
log(N) * |<r_N,(I-P_N)b_N>|^2
  / (||r_N||^2 * ||(I-P_N)b_N||^2) >= c > 0.
```

The measured quantity oscillates and reaches `0.0353` at `N=256`. More
importantly, it again depends on `r_N` and `P_N`, which contain the old finite
Gram inverse. No local divisor identity supplies the missing uniform angle.
Thus damping abandons the proposed gradient-flow mechanism and returns to the
same coupled inverse-projection non-cancellation bottom rejected in Plan 020.

## 4. Final Judgment

```text
exact block-gradient cancellation: passed
global energy contraction: false in every tested scale
old-space reprojection repair: false in every tested scale
optimally damped direction: no new lower producer
Plan 021 status: rejected
RH status: still conditional
Lean API: not created
```

Do not reopen this route by damping the same correction or enlarging the
floating-point cutoff. A genuinely different proposal must control future
divisor propagation before claiming that local cancellation lowers global
energy.
