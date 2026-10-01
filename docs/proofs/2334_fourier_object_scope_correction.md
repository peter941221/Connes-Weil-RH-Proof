# 2334 — Fourier object-scope correction

## Finding

Records 2321–2333 were described as diagnostics for the selected owner, but
their numerical input is the auxiliary P-only construction from record 2249:

```text
2249 build()
  -> r80.counterpart_nodes(rho)
  -> r59.P_from_nodes(...)^2
  -> Fourier / local-Taylor diagnostics
```

This is not the actual selected detector. The selected owner is defined in
`ConnesWeilRH/Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean` by

```text
selectedOwner base correction n
  = ofCompactLogTest
      (halfDensityShift
        ((convolutionIterate base n).convolution correction))
```

and its physical kernel is the convolution square of that shifted test. The
formal readback is exposed by
`selectedOwner_convolutionSquare` and
`selectedOwner_laplaceAt_convolutionSquare_centered`.

## Scope decision

The numerical readings in 2321–2333 are retained only as P-only auxiliary
cancellation and quadrature diagnostics. They do not establish any of the
following:

```text
actual selectedOwner Fourier coefficient
actual selectedOwner prime book
actual selectedOwner physical-kernel remainder
actual selectedOwner producer margin
```

In particular, record 2319 already gives a direct scoped no-go: the P-only
four-point annihilator reads zero on the marked centered pair, while the real
selected square reads -1. Therefore a P-only tail or margin cannot be used as
the selected detector's negative-prefix proof.

## Correct object chain

```text
actual selectedOwner
    -> selectedOwner.sourceTest
    -> selectedOwner.convolutionSquare
    -> actual bilateralProfile
    -> actual globalPrimeIndexSet
    -> finitePrimeSum
    -> actual physical-kernel integral
    -> ICgate / qw
```

The next numerical gate is not a tighter bound. It is an object-identity
gate: instantiate the actual selected owner, read back its transform and
support-derived prime set, and only then port the Fourier/local-Taylor
machinery. Until that gate passes, no 2321–2333 number may be placed in the
producer margin ledger.

## Evidence

- `ConnesWeilRH/Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean`
- `ConnesWeilRH/Dev/C1SameOwnerWeil.lean`
- `ConnesWeilRH/Dev/C1P2BilateralProfile.lean`
- `ConnesWeilRH/Dev/C1RouteAProducerReadback.lean`
- `docs/proofs/2319_routea_producer_readback_no_go.md`
- `scripts/routea_fourier_owner_error_budget_2324.py`
- `scripts/routea_forward_tail_budget_2333.py`

