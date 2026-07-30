# Proof 594: old-carrier leakage expansion

## Result

Bone 1's signed old-carrier telescope is now expanded into its exact two
physical channels.  For the boundary moment `Z_S`, the module defines

```text
Z_S
  = (endpointCoframe_S - sourceInclusion)^dagger
      * detector * sourceInclusion
    + sourceInclusion^dagger * detector * forwardCoframe_S.
```

The first term is the endpoint/ambient leakage channel.  The second term is
the forward-coframe channel.  Applying the adjacent signed telescope keeps
both channels synchronized:

```text
R0(p,S)
  = ambientLeakage_S * transition(p,S)^dagger * oldFrame(p,S)^dagger
      - transition(p,S)^dagger * ambientLeakage_(p::S)
          * oldFrame(p,S)^dagger
    + forwardLeakage_S * transition(p,S)^dagger * oldFrame(p,S)^dagger
      - transition(p,S)^dagger * forwardLeakage_(p::S)
          * oldFrame(p,S)^dagger.
```

The Lean theorem `suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_leakage_telescopes`
proves this equality without estimating either adjacent moment separately.

## Handoff contract

The module introduces `SuffixRawOldCarrierTwoChannelFactorData`.  A genuine
source producer must provide bounded rows `ambientRow` and `boundaryRow` such
that the *same signed telescope* factors as

```text
R0(p,S)
  = ambientRow * primeEulerAmbientLossFactor(p)^dagger
    + boundaryRow
        * (I - newFrame * newFrame^dagger) * transport^dagger.
```

The row bounds are combined by the existing ambient-boundary readout:

```text
 +----------------------+       +-------------------------+
 | ambientRow           | ----> | prime Euler loss^dagger |
 +----------------------+       +-------------------------+
           \                         /
            \                       /
 +----------------------+          /
 | boundaryRow          | --------/
+----------------------+
           |
           v
 +----------------------------------------------+
 | one old-carrier readout of the signed row    |
 +----------------------------------------------+
```

If the two row norms are bounded by `A` and `B`, the handoff proves old-carrier
domination with bound `A + B`, and the uniform family adapter is available.

## Boundary

This proof does not construct the source-specific rows or prove their
family-uniform bounds.  The residual modules currently provide operator-norm
bounds and obstruction results, but those facts do not produce the required
two-channel factorization of the single signed telescope.  Therefore Bone 1
remains open at the source-specific producer:

```text
uniform ambientRow/boundaryRow factorization
  -> old-carrier domination
  -> Gate 3U.
```

No spectral-gap assumption, separate adjacent-moment estimate, Gate 3U sign,
Burnol identity, or RH theorem is added here.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansionAudit.lean
```
