# 2322 — Fourier-side omitted-book cancellation is the viable interface

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

The 2321 diagnostic was extended by integrating the owner weight against each
omitted prime-power cosine first:

```text
I_n = integral W(xi) * cos(2*pi*log(n)*xi) dxi
D = Sum_{n > 167} 2*Lambda(n)/sqrt(n) * I_n
```

On the same 4001-point diagnostic grid:

```text
+--------------------------------+----------------------+
| quantity                       | value                |
+--------------------------------+----------------------+
| signed omitted contribution    | 1.554582535574e8      |
| sum abs of Fourier terms       | 6.216173118934e8      |
| frequency groups, width 0.5    | 5.792690481574e8      |
| frequency groups, width 1.0    | 2.634544878446e8      |
| frequency groups, width 2.0    | 1.554964793996e8      |
| existing margin                | 1.675396046388e12     |
+--------------------------------+----------------------+
```

This is the first diagnostic that keeps the relevant cancellation in the
right variable. The pointwise product bound was `2.2256e16`; integrating the
owner weight against each Fourier mode first reduces the absolute term sum to
`6.216e8`, already below the margin by about 2695x. Frequency grouping is even
closer to the signed result.

This remains a sampled diagnostic, not a certificate. The next proof object
must enclose each Fourier coefficient `I_n` (or certified frequency groups),
including the finite-window and quadrature remainder, and then sum the
coefficient radii. Do not infer a theorem from the sampled cancellation.

Evidence: `scripts/routea_omitted_prime_book_diagnostic_2321.py` and
`results/2321_omitted_prime_book_diagnostic.json`.
