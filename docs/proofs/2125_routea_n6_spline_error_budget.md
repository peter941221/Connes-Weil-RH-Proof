# 2125 — Route-A n=6 spline error budget

Date: 2026-09-28.

Status: SPLINE-ONLY-ERROR-BUDGET-CANDIDATE. This is not yet a prime-channel
certificate, producer theorem, or RH claim.

The n=6 candidate from records 2123/2124 uses a full prime book of 595877
entries. Increasing the Fourier window from `[-25,25]` to `[-75,75]` keeps the
same owner, seed, gate, and prime book while reducing the dual-frequency mesh
from `0.02` to `0.006666...`.

The cubic-spline interpolation estimate used for this screening budget is:

```text
|error(F_f)| <= (Delta_omega^4 / 384) * (2*pi)^4
                * integral |xi|^4 |f(xi)| dxi
```

Multiplying by the absolute prime weight sum
`2 * sum Lambda(q) / sqrt(q) = 11918.679927555173` gives:

```text
moment       integral |xi|^4 |f|       prime error bound
C            2.919859020367e8          2.790058136898e4
b            1.602060046677e12         1.530841262298e8
D            9.331484748484e15         8.916658225703e11
```

The Route-A full-gate centre at `|xi| <= 75` is:

```text
C = 1.1704752817252602e6
b = 1.2168693836911371e10
D = 8.288323049417873e13
det = -5.106433713351128e19
```

Propagating the three one-sided moment errors through
`det = C*D - b^2`, including quadratic error terms, gives a determinant
uncertainty `7.130143592708958e18`, giving a `7.16x` determinant margin. The
spline-only budget therefore preserves
`C > 0`, `b > 0`, and `det < 0`.

This is the first quantitative Route-A error budget that is smaller than the
n=6 gate margin. It is still incomplete because it does not yet charge:

- DFT/trapezoid sampling error;
- finite-window tail outside `|xi| = 75`;
- forward error in the cardinal transforms and prime accumulation;
- promotion from the 40-node known-zero owner to the formal source owner.

Next certificate target:

```text
spline bound + DFT/trapezoid bound + window-tail bound
    -> interval enclosure for C, b, D
    -> determinant sign certificate
```
