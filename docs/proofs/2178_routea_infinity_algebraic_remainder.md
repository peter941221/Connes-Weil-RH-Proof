# 2178 — Route A algebraic infinity remainder

Date: 2026-09-29.

## Consumer, owner, assumptions, failure criterion

The consumer is the same selected healthy `CompactLog` owner's signed C3'
tail, followed by the existing `SourceRH` consumer.  The calculation keeps
the one-copy G8-H numerical owner used by records 2058 and 2137; it does not
replace it by the complete closed-ball source-zero owner.

The input assumptions are the record-2135 order-48 variation upper candidate,
the stored coefficient/Gram path of record 2058, the support-derived prime
book, and the committed shifted-Stirling expression for the Archimedean
kernel.  Failure is any sign not covered, a nonpositive denominator constant,
or an infinity remainder that cannot be bounded by an explicit convergent
integral.

## Bound

For `|x| >= X0 = 10^6`, with `theta_max = 48.005150881...`,

```text
|theta - 2*pi*x| >= eta |x|,
eta = 2*pi - theta_max/X0 = 6.283137302...
```

The order-48 rung gives each family value at most `D_i |x|^-48`.  For the
four centered polynomial factors,

```text
|P(x)|^2 <= beta^8 |x|^8,
beta = 2*pi + max_j |z_j|/X0 = 6.283226226...
```

The shifted Stirling expansion gives the intentionally broad elementary
envelope `|sigma_arch(2*pi*x)| <= log |x| + 10` on this tail.  Adding the
finite prime book and the fixed slack gives `C0 + log |x|`, with
`C0 = 470.047586...`.  Hence the two-sided tail is bounded by twice

```text
beta^8 B_base^2 B_correction^2
 * X0^-183 * ((C0 + log X0)/183 + 1/183^2),
```

because the net power is `x^(8 - 4*48) = x^-184`.

## Result

The WSL resource-aware run
`results/20260929_routea_inf_2178.log` completed successfully and produced:

```text
one-sided bound          = 3.4512795416489271e-974
two-sided bound          = 6.9025590832978542e-974
two-sided / |Q1600|     = 2.0265584307153261e-986
two-sided / L2 charge    = 1.5644201827966582e-984
```

The script evaluates both signs and performs the closed-form integral in
high-precision arithmetic; no endpoint value is allowed to underflow to zero.

Evidence:

- `scripts/routea_infinity_algebraic_remainder_2178.py`
- `results/2178_routea_infinity_algebraic_remainder.json`
- `results/20260929_routea_inf_2178.log`

## Boundary

This is a strictly smaller tail obligation, not a producer theorem.  The
order-48 variation still needs an independent Arb or Lean enclosure, the
coefficient path and Gram construction are stored-float measurements, the
shifted-Stirling envelope is not formalized in Lean, and the one-copy owner has
not been transferred to the complete closed-ball owner.  The finite-window
signed C3' margin and detector compatibility remain open.

Classification: **ALGEBRAIC-INFINITY-REMAINDER-BOUND-CANDIDATE**.
