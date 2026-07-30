# Proof 605: Exact Old-Carrier Coframe Gap Response

## Result

The old-carrier coframe gap now has an exact response readback.  Define

```text
L_(p,S) = rho_p * R_(p::S)
           - T_(p,S) * R_S * reverseT_(p,S)
```

where `R_S` is the complete raw quadratic response, `T_(p,S)` is the forward
Euler transition, and `rho_p` is the one-prime Schur--Markov scalar.  The new
Lean definition is
`suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse` in
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponse.lean`.

The exact source-facing identities are:

```text
G_(p,S) = rawPhysicalFourTermRow_(p,S)

L_(p,S) * T_(p,S)
  = -rho_p * G_(p,S)^dagger

G_(p,S)^dagger
  = -rho_p^(-1) * L_(p,S) * T_(p,S).
```

The first response is the safer form because it does not divide by the scalar.
The inverse form uses `primeSchurMarkovScalar_pos` to establish nonzeroness.
The proof reuses the existing local cofactor theorem and preserves the right
composition order; it does not identify the transition with its adjoint.

## Lean owner and audit

The source owner is:

```text
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponse.lean
```

The import-facing audit is:

```text
ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseAudit.lean
```

The audited declarations use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or user axiom was added.

## Verification evidence

Ubuntu-24.04 WSL2 ext4 verification mirror (temporary local copy):

The focused source build, import-facing audit, aggregate, and full repository
build all passed:

```text
focused source module: 3369 jobs, PASS
focused axiom audit:   3370 jobs, PASS
CCM25Concrete:         3873 jobs, PASS
full repository:       3954 jobs, PASS
```

## Boundary

This proof closes an exact algebraic response/readout identity only.  It does
not construct the family-uniform source readout, prove the Bone 1 Douglas
bound, control the complete signed gap in Gate 3U, prove the finite-`S` sign,
prove Burnol's identity, or prove `_root_.RiemannHypothesis`.
