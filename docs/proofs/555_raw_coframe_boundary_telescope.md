# Proof 555: raw coframe boundary telescope

Result: the new boundary moment is exactly the adjoint of the existing
completed raw quadratic response. This closes an object-alignment and trace
ledger gap, but it does not prove the Gate 3U Douglas estimate.

## Source

The Lean source is
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope.lean`.
The focused audit is
`ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescopeAudit.lean`.

Let `J` be the source inclusion, `R_0 = J J†`, `C_0 = I - R_0`, and `W` the
selected self-adjoint detector. For an off-Sonin forward coframe `F` and a
biorthogonal endpoint coframe `E`, the module defines

```text
Z(F,E) = E† C_0 W J + J† W F.
```

The source commutator corners are

```text
K J = -C_0 W J,
J† K F = J† W F       when R_0 F = 0.
```

Because `K† = -K`, the existing physical response identity gives

```text
Z(F_S,E_S)
  = (suffixActualBandRawQuadraticCycledResponse owner lambda S)†.
```

Thus the complete raw four-term row has the exact adjacent form

```text
RawRow(p,S)
  = RawResponse(S)† T_(p,S)†
    - T_(p,S)† RawResponse(p::S)†.
```

The row remains signed and adjacent. No termwise residual estimate is used.

## Arithmetic readback

For a `FinitePrimePowerFamily`, the exact visible-prime specialization is

```text
Z(F_family,E_family)
  = (sourceActualBandFiniteEulerRemainderResponse owner lambda family)†.
```

The generic trace bridge is also proved. If the existing raw response is
`IsTraceClassAlong` a named Hilbert basis, then its adjoint boundary moment is
`IsTraceClassAlong` the same basis. Its ordinary trace is the complex conjugate
of the raw response trace.

These are trace-legality and carrier-alignment statements only. They do not
construct a readout through the actual ambient-loss plus moving-boundary Julia
analysis column.

## Verification

Commands run in the Ubuntu-24.04 WSL2 verification mirror:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
Build completed successfully (3333 jobs).

lake build ConnesWeilRH.Dev.CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescopeAudit
Build completed successfully (3334 jobs).
```

The audit reports exactly
`[propext, Classical.choice, Quot.sound]` for every new principal
declaration. The new source, audit, and proof document contain no `sorry`,
`admit`, or user axiom declaration. The WSL localhost-proxy warning is
environmental noise.

## Boundary

Proof 554 still rules out estimating the physical transport residual alone
through the ambient antiresonant loss. Proof 555 identifies the complete raw
row with the already-owned raw response, but supplies no family-uniform
Douglas factor through the actual left Julia co-defect. Gate 3U, the finite-S
sign, Burnol's identity, and `_root_.RiemannHypothesis` remain open.
