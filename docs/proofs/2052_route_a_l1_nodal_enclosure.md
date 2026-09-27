# 2052 — Route A link L1: enclosed nodal values (committed-evaluation forward bound)

Verdict: **ENCLOSED-L1-L2-VIABLE** at the registered owner (one-copy
G8-H): the model part's nodal input — the last addend charged as zero (L1)
and the last measured addend (the record-2048 float slack) — is now a
PROVEN charge.  Total `5.938659e+17` (aggregate) + `1.884216e+13` (L1) +
`3.917065e+16` (arch) = **`6.330553e+17` = 0.0633 x budget**, with no
measured addend left in the verdict line.  Probe:
`scripts/routea_l1_nodal_enclosure_2052.py`, artifact
`results/2052_l1_nodal_enclosure.json`.

## 1. Readings

Ladder (owner one-copy G8-H, same constants as records 2048/2051):

```
+--------+---------+-----------+-----------+-------------+-------------+---------+
| h      | nodes   | Coef1     | e_g max   | charge_nodl | charge_L1   | x slack |
+--------+---------+-----------+-----------+-------------+-------------+---------+
| 0.01   |   8001  | 22864.209 | 5.13897e10| 1.8470444e13| 1.8471353e13|  333.7  |
| 0.005  |  16001  | 23211.184 | 5.13904e10| 1.8751087e13| 1.8752010e13|  338.7  |
| 0.002  |  40001  | 23309.192 | 5.14358e10| 1.8829898e13| 1.8830825e13|  340.2  |
| 0.001  |  80001  | 23323.213 | 5.14360e10| 1.8841231e13| 1.8842159e13|  340.4  |
+--------+---------+-----------+-----------+-------------+-------------+---------+
```

`charge_L1` = nodal charge + echo (echo = `9.08995e+08 / 9.22789e+08 /
9.27728e+08 / 9.28286e+08` across the ladder); `e_g` median `3.082e-19`
at every rung (the cancellation floors); "x slack" is against the
record-2048 measured slack `5.536e+10`.

Cross-reads: the Coef1 column reproduces record 2048's table
(`22864.209 / 23211.184 / 23309.192` vs
`22864.209046806463 / 23211.183506287853 / 23309.19237243094`; B2 rel
`1.60e-08` at h = 0.002) and the per-rung aggregate charges reproduce the
record-2051 artifact exactly (B6 `worst_rel = 0.0`).  Scale of the bound:
`e_g <= 1.357e-09 |C|_max` at every rung, `|C|_max = 3.7906e+19`.

Verdict line: `5.938659e+17 + 1.884216e+13 + 3.917065e+16 =
6.330553e+17 = 0.0633 x budget` (record 2051: `6.330366e+17`; the L1
charge moves the total by 0.003%).

Anchors (all pass):

```
+----+--------------------------------------------+--------------------------+
| id | what                                       | reading                  |
+----+--------------------------------------------+--------------------------+
| B1 | containment |C - g^O| <= e_g at 6 sampled  | 6/6, worst ratio 6.1e-05 |
|    | nodes (mpmath dps 40, stored floats exact) | (mass peak), 9.5e-11 at  |
|    |                                            | the xi = 0 core          |
| B2 | Coef1(h = 0.002) vs record 2048            | rel 3.4e-07              |
| B3 | ladder node vs nearest fine-grid node      | bitwise equal at all 6   |
|    | (diagnostic)                               | sampled nodes            |
| B4 | charges finite, >= 0; Coef1 = Sum_j        | rel <= 9e-16             |
|    | Coef1_j                                    |                          |
| B5 | forward-calculus selftest vs mpmath dps 50,| 0/200 violations, worst  |
|    | inflated input errors                      | ratio 0.952              |
| B6 | aggregate charges vs the 2051 artifact     | worst_rel 0.0            |
+----+--------------------------------------------+--------------------------+
```

## 2. What is bounded (scope)

The bound is on the committed float64 evaluation of `g` at the ladder
nodes, relative to the stored-floats-exact object `O` of the record-2051
scope.  The committed DAG at a node:

```
s   = 0.5 - 2 pi i xi                       (Re exact, one rounding in Im)
v_j = a_j * (exp(z_j X_j) @ (phi(X_j) W_j)) (committed family path)
lb  = base @ v,   cc = corr @ v
p   = Re(prod_m (cnt_m - s))                (real up to rounding)
g   = ((p*p) * |lb|^2) * |cc|^2
```

Stored floats (exact in scope): `a_j, theta_j, X_j, W_j, base, corr,
cnt`, the node coordinates, `pi`.  The exp-argument rounding is carried by
the SAME constant as the 2051 bundles,
`AMP_j = 8 U a_j^2 (0.5 + 2 pi XI_MAX + |theta_j|)`, through the
node-independent moment `M_0`:

```
e_v_j = (EPS_TERM + m U + AMP_j) M_0_j INS,   m = 2400 GL nodes.
```

The upstream ideal-vs-stored gaps (F construction, phi quadrature,
eigh/min-h1, sigma) remain LINK L5, registered, NOT touched.

## 3. The forward calculus, and the cancellation-floor defect (found by B1)

The calculus is a (value, error) chain in which every multiplication
`z = x y` carries

```
e_z = (|x| + e_x) e_y + (|y| + e_y) e_x + U (|x| + e_x)(|y| + e_y),
```

the matvecs carry `gamma_17 Sum|terms|` plus the propagated `Sum |w_j| e_j`,
and squares use `e_{x^2} = X_s^2 - x + U X_s^2` with the SAFE magnitude
`X_s = |x| + e_x`.  The first version of the rig used the float value
alone as the magnitude and FAILED B1 at the `xi = 0` cancellation core by
27x:

```
xi = 0:  |lb| ~ 1.0000000000006 (no cancellation)
         |cc| exact 5.900e-14, float 5.7e-15, |error| <= e_cc = 5.9e-09
         -> true |cc| <= |cc_float| + e_cc, NOT |cc_float| = 1.04e-20
         -> e_yc = 2 |cc| e_cc + e_cc^2: the e_cc^2 floor (3.8e-17) is the
            whole error; the unsafe form read 1.3e-28 and under-charged.
```

After the fix the same node reads ratio `9.5e-11`; B5 (which injects
input errors up to `10^6 U` relative, i.e. exactly this class) is tight at
worst ratio `0.952`.  This is the 2051 cancellation-blindness law applied
to the calculus itself: magnitudes multiply, so the magnitude bound must
be the ENCLOSURE, not the float.

B1 detail (sampled nodes; `abs_diff = |C - g^O|`):

```
+----------+-------------+-------------+------------+
| xi       | abs_diff    | e_g         | ratio      |
+----------+-------------+-------------+------------+
| 0.0      | 2.736e-14   | 2.883e-04   | 9.49e-11   |
| 0.493    | 6.896e-09   | 5.361e-04   | 1.29e-05   |
| -6.68    | 1.854e-03   | 3.018e+01   | 6.14e-05   |
| 20.0     | 1.412e-32   | 5.456e-21   | 2.59e-12   |
| 34.97    | 7.322e+05   | 1.346e+10   | 5.44e-05   |
| 39.747   | 7.752e+05   | 1.444e+10   | 5.37e-05   |
+----------+-------------+-------------+------------+
```

The measured discrepancy is at the float floor everywhere; the proven
bound exceeds it by 10^4-10^10 depending on the cancellation depth of the
node — the price of a magnitude-based forward bound with the AMP smear.

## 4. The charge

Node j enters the model part with total weight `Coef1_j =
Sum_k c_k |W_j(k)|` (tent weights; `W_0 = BC_0 - BL_0/h`,
`W_j = BL_{j-1}/h + BC_j - BL_j/h`, `W_last = BL/h`), so

```
charge_L1(h) = Sum_j Coef1_j e_g_j
             + Coef1(h) ECHO_REL max_j |C_j| INS,   ECHO_REL = 1e-15
```

the second term being the model part's own echo (BC/BL evaluation and
assembly) carried at the record-2048 `dg_reference` rate — the rate whose
h = 0.002 charge is `8.836e+08` — a DISCLOSED proxy, not a proof; impact
`~9.3e+08`, i.e. 5e-9 of the total.

Structural readings:

- the per-node charge is 64x below the flat charge `Coef1(h) e_g_max
  = 1.200e+15` (h = 0.001): the e_g distribution is dominated by a few
  mass nodes, so the per-node coefficient array is what makes L1 cheap;
- the proven L1 charge is 340x ABOVE the record-2048 measured slack
  (`1.884e+13` vs `5.536e+10`): that slack was a magnitude-budgeted
  MEASUREMENT, not a bound, and this is the price of turning it into one.
  It costs 0.003% of the total;
- nodal allowance against the aggregate charge,
  `dg* = (budget - charge_agg - arch)/Coef1`: `3.093e+14` at h = 0.002,
  `4.016e+14` at h = 0.001 (positive only at the two operating rungs,
  as in 2048); the charged number `1.88e+13` sits `5.0e+05`x below the
  available headroom (`budget - charge_agg - arch = 9.367e+18` at
  h = 0.001), so precision is nowhere near binding.

## 5. Incident chain (both defects caught before any verdict)

1. **The selftest's exact chain had an extra square** (`(LR^2+LI^2)^2`
   instead of `(LR^2+LI^2)`), so B5 failed 200/200 with ratios up to
   8.8e+33 on the first build.  The failing side was the INSTRUMENT, not
   the bound (fifth instance of the 2048/2050 gate-at-the-design's-floor
   law); fixed in the selftest, not by touching the calculus.
2. **The cancellation-floor defect** of section 3, caught by B1 at
   `xi = 0` (26.85x) and fixed by the safe-magnitude form, re-validated
   by B5 at worst ratio 0.952.

B3 also resolved a puzzle from the 2051 arc: the ladder nodes and the
nearest fine-grid nodes are BITWISE equal at all six sampled nodes (numpy
`linspace` at h = 0.001 and 0.002 lands on fine-grid points exactly), so
the 2051 A1 residual (`1.47e+05`) was the model-vs-committed evaluation
difference, not a node-representation effect.

## 6. What it moves, and non-claims

- The L2 link's verdict line has no zero-charged and no measured addend
  left: `charge_agg` (2051, enclosed) + `charge_L1` (this record, proven)
  + `arch` (2048, interval) = `6.330553e+17 = 0.0633 x budget`.
- Remaining on the link: L4 (full-line tail, separate) and L5 (the
  upstream ideal-vs-stored construction, registered); the echo term is a
  disclosed proxy at the 2048 rate.
- The enclosure is of the committed evaluation at the ladder nodes; the
  bound is magnitude-based and deliberately cancellation-blind, so the
  charge is conservative exactly where the pipeline's own cancellation
  floors live.
- Not a producer theorem; not RH.