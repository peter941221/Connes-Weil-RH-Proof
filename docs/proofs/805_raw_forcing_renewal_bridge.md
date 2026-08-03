# Proof 805: Raw forcing renewal bridge

Date: 2026-08-04

Status: axiom-clean exact readback. The support-polynomial Gate 3U estimate
remains open.

## Result

For a finite prime-power family `T`, define the complete physical renewal
response on the actual source Sonin carrier by

```text
R_T = c_T^(-2) * sum_forward sum_renewal PhysicalResponseAtom(T, forward, renewal),
```

where `c_T = finiteEulerLowerFactor(T.visiblePrimes)`. Lean proves the
operator identity

```text
R_T = sourceBandGramResponse_T.
```

Under the existing completed Hardy--prolate pair-data hypotheses, `R_T` is
trace class on the named source basis. For one literal raw forcing step from
`oldFamily` to `newFamily`, Lean then proves

```text
raw forcing(p, S; newFamily, oldFamily)
  = Re Tr(R_oldFamily - R_newFamily).
```

Equivalently,

```text
raw forcing
  = Re Tr(R_oldFamily) - Re Tr(R_newFamily).
```

The subtraction is represented by one signed trace-class operator before the
real part is taken.

## Why It Matters

This corrects the overly broad claim that the causal renewal expansion had no
bridge to the raw Gate object. The existing renewal expansion already owns the
full source-band response; Proof 805 combines it with the raw completed
physical endpoint ledger.

```text
complete physical renewal response
             |
             v
source-band endpoint for each family
             |
             v
signed old-minus-new trace
             |
             v
literal raw Markov/remainder forcing
```

Consequently the unresolved analytical object is now exact:

```text
abs Re Tr(R_oldFamily - R_newFamily)
```

with compact root support applied before any absolute value. A merely uniform
absolute bound for individual raw steps is not enough: the number of steps
grows with the finite family. A valid producer must instead prove a direct
support-polynomial bound for `abs Re Tr(R_canonical)`, or a signed cumulative
estimate for the compatible deletion tower that preserves cancellation. At the
canonical endpoint, the Gate is precisely the bound for
`abs Re Tr(R_canonical)`.

## Boundary

The factor `c_T^(-2)` remains inside each complete endpoint response. This
proof does not divide the scaled estimate of Proof 795 by `c_T^2`, does not
bound the Markov coboundary and completed remainder separately, and does not
take absolute values of physical renewal branches.

Therefore Proof 805 does not prove the support-polynomial Gate 3U estimate,
the finite-S sign, Burnol's identity, or `_root_.RiemannHypothesis`.

## Lean Owner

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovRawRenewalBridge.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovRawRenewalBridgeAudit.lean
```

Key declarations:

```text
inverseLowerFactorPhysicalRenewalResponse_eq_sourceBandGramResponse
rawCompletePhysicalForcing_eq_rawPhysicalRenewalForcingTrace_re
canonicalRealGate3UAt_iff_abs_inverseLowerFactorPhysicalRenewalTrace_le
```
