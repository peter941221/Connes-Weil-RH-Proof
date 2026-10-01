# 2321 — Omitted prime-book diagnostic

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

Record 2321 evaluates the omitted prime-power interval on the same 30-family
owner, 4001-point grid, and transform/annihilator weight used by record 2249.
It is a diagnostic, not a certified enclosure.

```text
+----------------------------+----------------------+
| quantity                   | value                |
+----------------------------+----------------------+
| short prime book           | 52 terms <= 167      |
| full prime book            | 41136 terms <= 492475|
| short functional           | -1.675397327895e12   |
| full functional            | -1.675241869640e12   |
| signed omitted delta       | +1.554582542873e8     |
| absolute omitted charge   | 2.225576909988e16     |
| abs charge / abs full      | 1.3285e4              |
+----------------------------+----------------------+
```

The signed omitted contribution is small relative to the existing margin, but
its pointwise absolute-value charge is enormous because the omitted prime book
carries strong cancellation. A termwise triangle bound is therefore a named
no-go for this lane: it cannot fit the producer margin. The next certificate
must group the prime-power terms before taking norms, or use a directly
certified oscillatory quadrature/envelope that preserves the cancellation.

This result does not certify the full selected physical kernel and does not
transfer the 2249 margin. It does establish the correct numerical target for
the next proof attempt: bound the signed omitted contribution near
`1.55e8`, not its `2.23e16` pointwise absolute envelope.

Evidence:

- script: `scripts/routea_omitted_prime_book_diagnostic_2321.py`
- artifact: `results/2321_omitted_prime_book_diagnostic.json`
- scope predecessor: `docs/proofs/2320_kernel_owner_scope_mismatch.md`
A second diagnostic groups the same signed integrand in xi panels before
applying absolute values. The absolute sum falls from `2.2256e16` at pointwise
resolution to `1.5049e13` with width-2.0 panels, but this is still about nine
times the `1.6754e12` 2249 margin. Fixed-width panel grouping alone is not a
producer certificate; the next attempt must align panels with the oscillatory
scale and charge the quadrature remainder, or use a higher-order oscillatory
quadrature.

```text
+-------------+----------------------+
| panel width | sum of abs panels    |
+-------------+----------------------+
| 0.1         | 3.487650791596e15    |
| 0.2         | 1.422194499884e15    |
| 0.5         | 7.516380666734e14    |
| 1.0         | 2.767546173622e14    |
| 2.0         | 1.504929461135e13    |
+-------------+----------------------+
```
