# 989 - complete finite-vanishing Weil probe (SUPERSEDED sign report corrected)

Date: 2026-08-12. Status: floating-point convergence evidence. RH NOT claimed.
Companion: `docs/proofs/989_m2_double_sided_psi_probe.py`.

## Result first

The previous positive/negative sign split is superseded. After matching all
three coordinate-sensitive components to `C1SameOwnerWeil`, every tested
window is positive. In particular, the earlier negative values for widths
`3`, `3.5`, and `4.5` disappear when all visible prime powers are included.

## Correct evaluator contract

```text
F               = g^* * g                         (autocorrelation)
F(0)            = ||g||_2^2
pole(F)         = L_F(+1/2) + L_F(-1/2)
                = 2 * L_g(+1/2) * L_g(-1/2)       (real sampled tests)
prime_n(F)      = Lambda(n)/sqrt(n) * (F(log n) + F(-log n))
QW(g)           = pole(F) - arch(F) - sum_(all visible prime powers) prime_n(F)
```

Every run aborts unless `F(0)=||g||_2^2`, the pole product identity, and the
three sampled vanishings hold to `1e-8`.

## Convergence

```text
+--------------+-------+--------------+--------------+--------------+
| window       | N     | QW           | arch         | prime sum    |
+--------------+-------+--------------+--------------+--------------+
| [-0.5,+1.5] | 10001 | +0.018893669 | +0.000605332 | -0.019499001 |
| [-0.5,+1.5] | 20001 | +0.018894924 | +0.000603881 | -0.019498804 |
| [-0.5,+1.5] | 40001 | +0.018895284 | +0.000603518 | -0.019498802 |
+--------------+-------+--------------+--------------+--------------+
| [-1.5,+1.5] | 10001 | +0.003105435 | +0.415240087 | -0.418345522 |
| [-1.5,+1.5] | 20001 | +0.003105627 | +0.415239453 | -0.418345080 |
| [-1.5,+1.5] | 40001 | +0.003105849 | +0.415239295 | -0.418345144 |
+--------------+-------+--------------+--------------+--------------+
| [-2.0,+2.5] | 10001 | +0.000092040 | +0.844483372 | -0.844575412 |
| [-2.0,+2.5] | 20001 | +0.000093091 | +0.844483102 | -0.844576193 |
| [-2.0,+2.5] | 40001 | +0.000093282 | +0.844483034 | -0.844576316 |
+--------------+-------+--------------+--------------+--------------+
```

The pole is numerically zero because the constructed test nearly vanishes at
`+1/2`; the reported pole-product identity is independently asserted.

## Why the verdict changed

The historical sequence fixed several different bugs. Only their combined
correction gives the current numbers:

1. use autocorrelation `spectrum * conj(spectrum)` with zero lag at index zero;
2. use the real Laplace points `+1/2` and `-1/2`, not `i/2`;
3. sample prime terms at `+/-log(n)`, not at `n` and `1/n` or other raw values;
4. include every visible prime power, not only `n=2`.

## Interpretation

These tests numerically support `QW(g) >= 0` on one normalized parametric
family. They do not prove it for every compact-log test, and their SVD-derived
coefficients are not exact Lean witnesses. The old negative-family and sign
boundary conclusions are retracted. RH NOT claimed.
