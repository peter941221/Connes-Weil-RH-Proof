# Proof 799: Raw Gate 3U readout

Date: 2026-08-03

Status: axiom-clean Lean alignment of the canonical real Gate with the raw
completed physical trace. It makes the raw forcing route feed the actual
Gate directly. It does not prove the required support-polynomial bound.

## Result

For the canonical finite prime-power family of the selected Weil square,
Lean proves:

```text
canonicalRealGate3UAt(owner, lambda, sourceBasis, bound)
  <->
abs(rawCompletePhysicalHermitianTrace(canonicalFamily(owner))) <= bound.
```

Together with Proof 798, a future compatible family-chain producer has the
following exact route:

```text
signed cumulative raw forcing bound
        |
        v
raw completed physical trace bound
        |
        v
canonical real Gate 3U.
```

No lower Euler factor is introduced in this readout.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovRawGateReadout.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovRawGateReadoutAudit.lean
```

Key declarations:

```text
canonicalRealGate3UAt_iff_abs_rawCompletePhysicalHermitianTrace_le
canonicalRealGate3UAt_of_abs_rawCompletePhysicalHermitianTrace_le
```

## CC20 Scope Audit

The tempting static cancellation is not yet a theorem about this moving
finite-S owner. CC20 defines

```text
Q = -(rho d/drho)^2 + 1/4
```

on compactly supported source test functions. Its Theorem 3.6 represents the
static functional `D o Q` on a fixed `L2(sqrt(I), d*rho/rho)` space by
`-2 I + K_I`; the `Q epsilon` formula separately retains a bulk term, two
boundary terms, and a prolate series tail.

Primary source:

```text
Connes and Consani, Weil positivity and Trace formula, the archimedean place
https://arxiv.org/abs/2006.13771

Source anchors: weil-compo.tex lines 710-719, 789-806, 1218-1346.
```

The current Gate owner instead contains the moving inverse-metric coframe:

```text
finiteEulerMetricCoframe
  = finiteEulerAmbientGram o sourceInclusion o finiteEulerGramInv.
```

No source or Lean theorem presently identifies this moving Gram-corrected
coframe with the fixed CC20 `D o Q` kernel, or proves a `Q` intertwining for
it. Therefore the static `Q` half-power cancellation from Proof 333 cannot
legally be imported into the current raw cumulative forcing.

## Verification

The focused Ubuntu-24.04 WSL2 ext4 verification passed:

```text
lake build \
  ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawGateReadout \
  ConnesWeilRH.Dev.CCM24FiniteSCausalMarkovRawGateReadoutAudit
```

The source and audit use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Scope

Proof 799 does not bound the raw trace, establish a compatible canonical
family chain, prove the finite-S sign, prove Burnol's identity, or prove
`_root_.RiemannHypothesis`.
