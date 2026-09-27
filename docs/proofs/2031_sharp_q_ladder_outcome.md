# Record 2031 - Sharp weighted q-ladder: R-B1 pricing outcome

Date: 2026-09-27.

Status: OUTCOME OF A NUMERIC PROBE. No theorem, no interval certificate, no RH
claim. Everything here is a pricing result on the record-1980 owner; the seed
mass `W_k` is computed, not certified.

Third item of the "full assault" batch registered in
[2029](2029_coupling_scan_outcome.md) section 7 (P3), after
[2030](2030_determinant_certification_margin.md) (P2).

Instrument: `scripts/fourpoint_sharp_q_2031.py`. Artifact:
`results/2031_sharp_q_ladder.json`.

## 1. Bottom line

Result: GOOD for R-B1, and it comes with a crisp structural reason.

```text
1.  The raw first-order majorant of record 1982 is worse than useless: it is
    not even a UNIFORM bound in t.  The base is a sum of node products of
    degree 26 while the seed mass multiplies |a + i y|^{-k}; a k-fold
    integration by parts buys |t|^{-10k}, so every k with 10k <= 26 gives a
    majorant that GROWS without bound.  Only k >= 3 can bound the strip.

2.  At k = 3 the SHARP weighted mass closes the target with a 203x margin:
        max over sigma in [0,1], |t| >= 28   of the majorant  =  3.0016e-07
        q = 2^(-14) = 6.1035e-05             margin q/bound     =  203.34
    and the maximum is attained at (sigma, t) = (0, 28), after which the
    bound decays (1.57e-09 at t = 30, 1.45e-15 at t = 40, 2.0e-18 at t = 800).

3.  The weighted mass is what buys it.  Replacing W_k(a) by the crude
    e^{2|a|} * D_k leaves k = 3 with a 1.03x margin -- a hair's breadth.
    The sharp mass is ~2.1x below the crude one at |a| = 0.525, and the tenth
    power amplifies that into the 197x gap between the two final bounds.

4.  k = 4 and above fail on the other side: the mass W_k grows faster than
    |a+iy|^{-k} (W_4/W_3 = 16.1, W_5/W_4 = 27.3, W_6/W_5 = 39.8).  k = 3 is
    the UNIQUE surviving order.
```

## 2. The object

```text
base(s) = sum_z c_z * P(z,s) * L(s - z),      L(w) = S_seed(w/2)^10
c_z     = value(z) / (P(z,z) * seed0),        seed0 = laplaceAt poweredSeed 0
```

The owner has 27 nodes, so `P(z,.)` has degree 26; only three targets are
active (`rho` with value +1, `1 - conj rho` with -1, `rho + 0.5` with -1).

Exact seed facts used here, all three proved by the reflection
`T(1-u) = 1 - T(u)` of the transition function and confirmed numerically to
`>= 20` digits:

```text
integral_0^1 T(u) du        = 1/2                    (reflection, exact)
S_seed(0)                   = 1/2 + 2 + 1/2 = 3      (exact)
seed0 = S_seed(0)^10        = 3^10 = 59049           (exact; the committed
                              float 59048.99999985875 is quadrature error)
D_k = integral |f^(k)|      :  D_0 = 3, D_1 = 2, D_2 = 8 (exact)
                              D_3 = 78.7283384, D_4 = 1266.2228343,
                              D_5 = 34570.6001442, D_6 = 1377559.3231497,
                              D_7 = 83080389.5981560
```

`D_1 = 2` and `D_2 = 8` are exact: for `k >= 1` the derivative mass lives only
on the two transition windows, `f^(k) = (+-)T^(k)` there, so
`D_k = 2 * integral_0^1 |T^(k)|`, and `integral_0^{1/2} T'' = T'(1/2) - T'(0)
= 2 - 0`.

## 3. The sharp weighted mass

```text
W_k(a) = integral_{-2}^{2} e^{a x} |f^(k)(x)| dx
       = e^{-2a} A_k(a) + e^{2a} A_k(-a),     A_k(a) = integral_0^1 e^{a u}|T^(k)(u)|du
```

`W_k` is even in `a` and increasing in `|a|` (`W_k(a) = integral cosh(a x)
|f^(k)|`), which is what makes the sigma-sup exact from a table on `|a|`.

```text
 |a|      0.025        0.225        0.275        0.525
 W_1      2.006433     2.121711     2.180208     2.669273
 W_2      8.026494     8.496420     8.735183    10.738871
 W_3     78.982934    83.630285    85.992335   105.834383
 W_4   1270.349286  1345.953820  1384.409124  1708.168568
 W_5  34682.897383 36764.420335 37823.740463 46756.824474
 W_6     1.382046e6   1.465826e6   1.508491e6   1.868972e6
 crude e^{2|a|} D_k at |a| = 0.525:  k=3 -> 224.97   (weighted 105.83)
```

The binding `|a|` values are `0.275` (from `rho` and `1 - conj rho` at
`sigma in {0,1}`) and `0.525` (from `rho + 0.5`).

## 4. The bound, and why k = 3 is forced

```text
|S_seed(a + i y)| <= W_k(a) / |a + i y|^k            (k-fold integration by parts)
|base(s)|         <= sum_z |c_z| |P(z,s)| (W_k(a)/|a+iy|^k)^10
```

```text
 k   max bound over sigma in [0,1],   attained at        margin q/bound
     |t| >= 28 (t scanned to 200)
 1            8.387290e+07            (0.00, 200)        7.28e-13     FAIL
 2            1.862259e-06            (0.00, 200)        3.28e+01     not uniform
 3            3.001641e-07            (0.00,  28)        2.03e+02     PASS
 4            1.358449e-03            (0.00,  28)        4.49e-02     FAIL
 5            1.217941e+03            (0.00,  28)        5.01e-08     FAIL
 6            4.797588e+10            (0.00,  28)        1.27e-15     FAIL
```

`k = 1, 2` are flagged "not uniform" even where their printed maximum is below
`q`, because their maxima sit at the end of the scan and keep growing. The
`t`-tail check in the artifact:

```text
 k=2:  t = 28 -> 9.08e-09   t = 100 -> 2.53e-09   t = 200 -> 1.86e-06
       t = 400 -> 2.44e-04 (4.00 q)               t = 800 -> 2.06e-02 (337 q)
 k=3:  t = 28 -> 3.00e-07   t = 30 -> 1.57e-09    t = 40 -> 1.45e-15
       t = 100 -> 1.02e-15  t = 400 -> 2.92e-17   t = 800 -> 2.01e-18
```

Degree arithmetic for the tail: `|P(z,s)| ~ |t|^26` past the last node
ordinate, the seed factor contributes `|t|^{-10k}`, so the bound behaves like
`|t|^{26-10k}` and is uniform exactly for `10k > 26`, i.e. `k >= 3`. Near the
node ordinates `|P|` dips, which only lowers the bound, so the large-`t`
asymptotics is the binding constraint.

## 5. Why the crude majorant nearly failed, and what that teaches

Same scan with `W_k` replaced by record 1982's `e^{2|a|} D_k`:

```text
 k   crude bound        margin q/bound
 1   1.754160e+10       3.48e-15
 2   3.827686e-04       1.59e-01
 3   5.918919e-05       1.03e+00   <- 3% under q, i.e. it barely passes
 4   2.619494e-01       2.33e-04
```

Two corrections to record 1982's screening:

```text
(a) the crude bound must be used at k = 3, not k = 1; the un-powered k = 1
    majorant is numerically hopeless (8.4e+07) and is not a uniform bound;
(b) the |a| range is [-0.525, 0.525] (from rho + 0.5), not the [-3/4, 3/4]
    of record 1982, and the seed support weight is 3, not <= 4.
```

The lesson worth keeping: a majorant that is raised to the tenth power must be
pushed below 1 BEFORE the power, and the cheapest way to do that is not more
support width but the located mass `W_k(a)`.

## 6. What this record does not do

- No interval certificate. `W_k(a)` is a high-precision quadrature value;
  a Lean consumer needs `integral_0^1 e^{a u} |T^(k)(u)| du` evaluated or
  bracketed with the committed `T`-derivative machinery. That is a plausible
  target because the integrand is one-dimensional, explicit and has no
  cancellation (`|.|`), unlike the gate moments.
- The sigma-sup is a 0.01 grid on `[0,1]` and the `t`-scan a 0.5 grid on
  `[28,200]` plus point checks to `t = 800`; both factors are smooth on those
  scales (`|P|` dips only reduce the value, and the seed mass is monotone).
- The owner is still the known-zero under-approximation; nothing here is a
  statement about the formal `sourceNontrivialZerosInClosedBallFinset`.
- Nothing about COVER, TAIL, the gate signs, or RH.

## 7. Consequence for the route ledger

```text
R-B1 (all-strip q)   PRICING PASS -- a concrete, explicit majorant exists with
                     a 203x margin, and the required order (k = 3) is forced
                     by the degree of the node product.  Next step is an
                     interval version of W_3 on [0,1].
R-B2 (determinant)   cheap (record 2030) but unreachable on certified rows.
R-B3 (tail ratio)    blocked by 2029: no admissible n >= 1 gate row.
```

The binding route obstacle is therefore NOT the contraction premise. It is
that the seeded owner has no certified gate row at `n >= 1` (record 2029).
