# 2287: MPFR-directed finite GL node preflight

Date: 2026-09-30

Decision: node arithmetic is controlled; the finite GL quadrature remainder is now the binding unresolved layer.

## Method

Record 2286 supplies directed complex intervals for fixed owner atoms. Record 2287 propagates those intervals through finite composite Gauss-Legendre node sums using 256-bit MPFR RNDD/RNDU arithmetic. The tested configurations are:

```text
xi       panels/order
40       8/8, 8/16, 16/8, 16/16
120      8/8, 8/16, 16/8, 16/16
200      8/8, 8/16, 16/8, 16/16
```

The corrected owner and support-derived 41136 prime-power guard are unchanged.

## Result

The arithmetic enclosure radii remain small:

```text
quantity              maximum radius
base node sum         1.7604848135e-11
corr node sum         2.6934635855e-8
```

But the rule midpoint moves substantially across order and partition:

```text
quantity              maximum relative movement
base                   4.5953271785x
corr                  10.3752568650x
```

Therefore the remaining error is not MPFR atom arithmetic. It is the unbounded quadrature remainder from replacing the continuous oscillatory panel integral with a finite GL node sum.

## Decision

Do not attach this result as `hgap`. The next admissible step must add a separately proved panel remainder, such as an oscillatory Filon remainder with a certified derivative/analytic bound. Increasing GL order alone remains frozen.

## Nonclaims

- The GL quadrature remainder is not enclosed.
- The finite xi sample is not the infinite tail.
- No hgap supplier, producer GO, selected-detector readback, or RH conclusion follows.

## Reproduction

```text
wsl.exe bash -lc "python3 /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/routea_mpfr_gl_node_preflight_2287.py"
python -m unittest discover -s scripts -p 'routea_mpfr_gl_node_selftest_2287.py' -v
```
