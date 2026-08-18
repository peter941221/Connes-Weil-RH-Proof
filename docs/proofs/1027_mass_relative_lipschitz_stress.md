# 1027 - Mass-relative Lipschitz stress screen

Date: 2026-08-18.

## Question

The formal Gamma_R origin estimate uses a Lipschitz constant for the compact-
log test.  The 1026 bridge can express its tail in square-mass units only
after a bound of the form `L <= C * mass` is supplied.  This screen checks
whether a frequency-independent `C` is plausible for the constructive D3
triple-vanishing family.

## Method

For a smooth compactly supported bell `h_k(t) = h(t) cos(k t)`, form

```text
g_k = (d/dt)(d/dt + 1/2)(d/dt + 1) h_k.
```

The differential identity gives exact formal Laplace zeros at `0`, `1/2`,
and `1`.  Each numerical root is normalized to convolution-square mass one.
The probe measures an interior-grid lower bound for the derivative of
`g_k^* * g_k`; this lower bound is already enough to show growth of the
Lipschitz constant if it grows with `k`.

## Reproduction

WSL2 command:

```text
python docs/proofs/1027_mass_relative_lipschitz_stress.py
```

The output is a finite floating-point screen.  It is not imported into Lean.

Representative output from the verified probe run:

```text
+-----------+------------+------------------+----------------------+------------------+
| frequency | mass       | Lipschitz lower  | head constant lower  | Laplace residual |
+-----------+------------+------------------+----------------------+------------------+
|       0   | 1.00000000 | 7.268133e+01     | 1.463627e+02         | 3.87e-12         |
|      32   | 1.00000000 | 3.268103e+01     | 6.636207e+01         | 1.50e-13         |
|      64   | 1.00000000 | 6.571541e+01     | 1.324308e+02         | 5.37e-14         |
|     128   | 1.00000000 | 1.290041e+02     | 2.590083e+02         | 3.79e-15         |
|     192   | 1.00000000 | 1.926769e+02     | 3.863538e+02         | 3.45e-15         |
|     256   | 1.00000000 | 2.565044e+02     | 5.140088e+02         | 1.97e-15         |
+-----------+------------+------------------+----------------------+------------------+
```

The measured derivative is only an interior-grid lower bound, so the listed
head coefficient is also a lower bound for the `2 * Lip + ||F(0)||` constant
used by the formal majorant.  The high-frequency rows are therefore evidence
against assuming a small frequency-independent mass coefficient, not a proof
that no finite coefficient exists.

## Route Decision

The constructive next owner should not assume a small frequency-independent
mass-only `C`.  The viable formal choices are:

1. restrict the proof to a finite-dimensional or frequency-bounded owner and
   prove its derivative energy bound; or
2. retain the derivative/energy factor and prove a coupled quadratic tail
   estimate instead of an absolute mass budget.

The 1026 conditional bridge remains useful for either choice.  Prime-inclusive
Lane R, global spectral nonnegativity, and RH remain open.
