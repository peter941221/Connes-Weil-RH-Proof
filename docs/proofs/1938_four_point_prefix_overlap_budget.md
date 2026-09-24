# Record 1938: four-point prefix plus actual-owner overlap budget

Date: 2026-09-24.

The owner-preserving prefix reduction is now combined with the committed
support-overlap estimate for the physical kernel. For every actual
`OrbitG8Geometry`, Lean proves

```text
finitePrimeSum(g.square)
  <= finitePrimeTerm(g.square, 2)
     + sum over the actual finite cutoff with n=2 erased of
       2 * exp(rawFactorSupportRadius) * rawFactorSeminorm^2
         * (vonMangoldt(n) / n)
```

The proof uses the exact range split at `n=2` and the existing signed-owner
physical-kernel overlap bound. It does not assume that `2` is visible and it
does not replace the selected owner.

Together with record 1937, the live sufficient inequality is now an explicit
scalar budget:

```text
archimedeanTerm + n2PhysicalTerm + overlapRemainder <= 0.
```

The overlap remainder is a majorant, so the remaining work is to prove that
the actual n=2 physical sample supplies enough strict negative margin, or to
sharpen the overlap estimate until it does. The determinant sign itself is
still open; this record is a strict quantitative reduction, not an RH claim.

Focused build `20260924_prime_prefix_reduction20` completed successfully
(3801 jobs). The paired audit prints only `[propext, Classical.choice,
Quot.sound]`; no `sorryAx` occurs.

Classification: FORMAL quantitative reduction.

## Prefix sharpening

The overlap majorant originally included the `n = 2` range contribution even
though that node is retained exactly. Record 1938's final theorem removes this
double payment:

```text
finitePrimeSum
  <= n2PhysicalTerm + orbitSupportOverlapBound
     - 2 * exp(rawFactorSupportRadius) * rawFactorSeminorm^2
         * (vonMangoldt(2) / 2).
```

The subtraction is formal and uses only that every OrbitG8 cutoff contains
`2`; it does not assume that the selected owner makes the n=2 term nonzero.
