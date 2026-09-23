# 075 — C3' carrier transport and phase-owner reduction

Status: active formal reduction for the same-owner signed C3' lane. The
readbacks are closed; the selected-detector signed estimate is open.

## Formal reduction

`C1C3CarrierTransport.lean` places a carrier-modulated two-span test on one
owner and proves exact readbacks for:

- the two diagonal gates and directed cross gate;
- Archimedean, mixed Archimedean/prime, and prime determinant channels;
- finite visible-prime phase cells and their credit/deficit expansions;
- the optimal two-span coefficient and determinant criterion;
- support-preserving inverse modulation and carrier reparameterization of the
  actual `OrbitG8Geometry` detector;
- the support-derived finite cutoff and owner-cardinality adapters.

For a positive pivot, the optimal q-form is nonpositive exactly when the full
same-owner gate determinant is nonpositive. The determinant must be treated as
one aggregate. Splitting it into three channelwise sign obligations is only a
sufficient condition and can impose a false cross-sign constraint.

The later algebraic correction is binding:

```text
det = ICgate(u) * ICgate(v) - ICgate(u,v)^2.
```

If `ICgate(u) <= 0` and `ICgate(v) >= 0`, then `det <= 0` without any sign
assumption on the cross term. This is consumed by [091].

## Physical and Gamma-side interfaces

The same carrier owner has exact Fourier/Laplace shifts and a full
Archimedean readback through the centered GammaR integrand. The sigma profile
has a convergent reciprocal-difference series, evenness, monotonicity on the
nonnegative half-line, and an existential negative tail. These facts identify
the Archimedean mechanism but do not compare it with the detector's exact
finite prime sum at the required height.

Absolute-value cutoff bounds such as
`N * 2 * log(N) * seminorm` are valid diagnostics. `OrbitG8Geometry` does not
export the envelope seminorm needed to close them, and channelwise absolute
values destroy the cancellation sought by C3'. They are not the live
producer.

## Current consumer

The live downstream owner is [080], with the finite physical-node and
aggregate-kernel interfaces [079] and [081]. The exact target remains:

```text
archimedean determinant
  + mixed discrepancy
  + prime determinant
<= 0
```

or a stronger one-span/physical-kernel inequality that implies the same
`orbitWindowSemiLocalGate` on the actual selected detector.

## Guard

Do not demodulate and then reason about a different test: carrier modulation
and inverse modulation cancel exactly, so the envelope depends on the chosen
frequency while the physical detector stays fixed. Do not freeze the prime
set independently of support. Do not replace the full determinant by three
unnecessary channel signs.

Evidence classification: carrier/readback/cutoff statements are `FORMAL` and
paired-audited; sigma asymptotics not represented by named Lean theorems remain
`PAPER`; the selected signed budget is `OPEN`.
