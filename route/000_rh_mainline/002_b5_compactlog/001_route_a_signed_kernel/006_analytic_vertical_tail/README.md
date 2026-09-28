# Route A.006 — Analytic vertical-decay tail

Status: ACTIVE INFRASTRUCTURE. This is a required tail component, not a
producer theorem and not an RH claim.

## Why this subroute exists

Record 2134 closes the current `m=6400` sampled-tail extrapolation. On the
same owner used by records 2059-2062, the measured ratios are small on
`40..160`, `160..240`, and `240..400`, but the evaluator reaches an alias
cliff in `500..550`. A low-range sampled value therefore cannot certify the
full-line tail.

Evidence:

```text
docs/proofs/2134_routea_evaluator_horizon_no_go.md
results/2132_routea_tail_horizon_extension.json
results/2133_routea_tail_horizon_400.json
results/2134_routea_tail_horizon_600.json
```

## Healthy-detector consumer

The consumer is the actual selected healthy `CompactLog` owner:

```text
selected detector has qw < 0
    -> bound the same-owner spectral/physical tail
    -> retain the signed finite visible-prime aggregate
    -> prove qw >= 0 for that owner
    -> SourceRH
```

The tail bound must not replace the selected owner with a fixed-prime,
known-zero, or sampled under-approximation.

## Current formal assets

The four-point spectral infrastructure already exposes the ingredients:

```text
C1SpectralWeil.exists_uniform_centered_laplaceAt_vertical_quartic_decay
C1SpectralWeil.exists_uniform_centered_laplaceAt_vertical_quadratic_decay
C1FourPointHighShellTail.selectedOwner_fullOrbit_span_fourthOrderSpectralTail
```

These establish decay interfaces and a parameterized shell-tail implication.
They do not yet prove the actual Route-A selected-owner signed C3' gate.

## Next bounded task

1. Instantiate the decay constants for the actual owner and preserve its
   support, visible-prime set, and quantifier order.

2. Derive an explicit shell/tail budget with a named margin, not only an
   existence statement.

3. Connect that budget to the signed aggregate gate. If the connection fails,
   record the exact owner, inequality, and failed margin as a scoped no-go.

## Reopen rule

Do not return to sampled-tail extrapolation unless the evaluator changes and
its trust horizon is independently proved. Do not spend more high-resolution
brute-force scans on the closed `m=6400` mechanism.
