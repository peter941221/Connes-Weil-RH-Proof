# 2249 — Certified downward enclosure of the finite-window functional (L1)

Date: 2026-09-30

Consumer: the 2246 item-5 statement, brick L1: the anchor
`1675397327895.099` is a single binary64 sample of the direct
construction without an error bar.

Verdict: **L1 landed**. The finite-window functional on the 4001-point
grid is enclosed by a first-order forward-error shadow:

```text
q                = -1675397327923.575          (instrumented evaluation)
E_total          =  1281535.3012791811         (7.649142564095338e-07 of |q|)
q_lo             = -1675398609458.8762
q_hi             = -1675396046388.2737
margin_lo (|Q|)  =  1675396046388.2737         (= -q_hi, certified lower)
margin_hi (|Q|)  =  1675398609458.8762         (= -q_lo, certified upper)
```

The strict signed margin now holds at the certified margin: with the 2245
count ratios and the 2248 tail,

```text
total charge, unconditional              2126963424.526075
reading (charge / margin_lo)             0.0012695287356749262
slack                                    0.9987304712643251
eps0                                     1673269082963.7476
total charge, imported                   1732278444.8676655
reading                                  0.0010339516131735035
slack                                    0.9989660483868265
eps0                                     1673663767943.406
```

(compare the 2246 readings against the sampled margin:
`0.0012695277646158757 / 0.0010339508223067488`; the certified readings
move by about `1e-9` because the certified margin is `1281535.3` smaller
than the sample).

## What is enclosed

Convention A (record 2230): the stored binary64 operands are exact, and
the enclosed object is the formula of the 2103 pipeline evaluated in exact
real arithmetic on those operands. Every elementary double operation is
charged `U = 2^-52` (two machine epsilons, covering one ulp including
libm error); pairwise reductions carry `64 * 2^-53 * sum |terms|`; a final
`1 + 1e-6` inflation covers the model's own float bookkeeping. Summing the
pointwise charges then gives `q_true in [q_lo, q_hi]` for the
exact-real evaluation, hence `|Q| in [margin_lo, margin_hi]`.

Deliberately NOT charged (registered ideal-to-discrete gaps): the GL phi
quadrature choice (the m = 6400 Gauss-Legendre panels), the numerical
owner list, the `[-40, 40]` window versus the full integral, and the
float solve versus the exact solve of the stored matrix (the stored
floats define the object).

## Cross-checks

```text
plain 2103 pipeline on the same grid   q = -1675397327885.4666
rel discrepancy at the g peak          3.0620944708905883e-13
max |g| difference                     988.25   (|g| up to 9.4543131425951609e14)
kernel max |difference|                3.552713678800501e-15
p (quartic product)                    bitwise equal (rel 0.0)
lb (base dot) rel difference           2.93e-15 at the mid point
eg/g on live points (|g| > 1e-9 max)   2.82e-05 ; 651 live points of 4001
gl identity vs r59.phi_weights         bitwise (gl_identity_ok)
base/corr md5 pins                     d461872e14212dcba8efe1874de6f652
                                       c37e16a9dfeb4383c7bab1d23aa59566
```

The corr-dot relative diagnostic (`rel_lc_diff_mid = 1.96`) is a
near-cancellation artifact, not a disagreement: the instrumented and
plain paths at the mid point land on a corr value of order `1e-22`
(`abs_hc_min = 5.668725323812063e-23` over the grid). An mpmath
50-digit reference at the worst family confirms both float paths are
limited by cancellation there (`rel_v_mine_vs_ref = 3.76e-05`,
`rel_v_plain_vs_ref = 2.98e-04` at `|v| = 3.93e-26`); the error model
charges absolute errors, so near-zero channels are covered by
construction.

## Instrument finding (fixed)

The first smoked run showed a kernel drift of `6.1e-07` against the
plain pipeline. Root cause: the complex power update `pw = pw * zz2`
inside the instrumented sigma recursion reused the already-updated real
part (`old_re * z2re * z2im` instead of `old_re * z2im`), corrupting the
asymptotic-series correction. After the fix the kernel agrees to
`3.55e-15`. The lesson is registered in the module docstring: shadow
implementations must be op-by-op copies, and the cross-check against the
plain pipeline is the guard.

## What this closes and what it does not

Closed: L1 of the 2246 statement, at the full pipeline and with all
cross-checks; L3 now holds against a certified margin with positive slack
`~1.667e12` (the arithmetic side is formalized in the 2252 Lean brick).

Not closed: the ideal-to-discrete gaps listed above; the per-node charge
uniformity half of L2 (the 2250 count brick closes the count half per
node); the numeric certification is first-order-shadow based, not
Lean-formalized interval arithmetic; no producer GO, no gate sign change,
no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_l1_enclosure_2249.py`
  (recon: `scripts/routea_weighted_zero_l1_recon_2249.py`);
- artifact: `results/2249_l1_enclosure.json`;
- runtime: 190.2 s single core in WSL for the 30 families x 4001 grid
  plus the plain cross-check; the legendre nodes are built once and
  copied bitwise (guarded by `gl_identity_ok`).