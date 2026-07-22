# Proof 491: Corrected physical pair alignment

Date: 2026-07-22

## Result

The result is good as an ownership audit and bad for the proposed shortcut.
The previously unused `sourceCorrectedPhysicalSourcePairData` is not the full
actual-band remainder.  Lean now identifies exactly what it owns and exactly
which two terms are still required.

With

```text
E =radialSupportProjection,
T =cc20ThreeBranchCommutator,
H_S=finiteEulerAmbientGram,
J =sourceInclusion,
G_S^-1=finiteEulerGramInv,
```

the identity-transport corrected bracket collapses to

```text
correctedPhysicalBracket(E,...,I)=E T E.
```

Its source response is therefore

```text
C_S=J^dagger T E H_S J G_S^-1.
```

The omitted outer-complement response is

```text
O_S=J^dagger T(I-E)H_S J G_S^-1.
```

Lean proves the exact recombination

```text
C_S+O_S=-sourceBandGramResponse(S),
```

and hence

```text
sourceActualBandFiniteEulerRemainderResponse(S)
  =actualBandFirstJetCycledResponse(S)+C_S+O_S.
```

## What changed

The source file and audit are:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCorrectedPhysicalPairAlignment.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCorrectedPhysicalPairAlignmentAudit.lean
```

The module first proves a carrier-independent ring lemma.  If the fixed
physical commutator has the compressed form

```text
fixed=-(E T E),
```

then idempotence of `E` makes the identity-corrected bracket exactly `E T E`.
The actual CCM24 projections and the existing three-branch theorem instantiate
that lemma.

The source inclusion adjoint then absorbs the redundant left support:

```text
J^dagger E=J^dagger.
```

This leaves the right `E` visible.  Splitting the identity as

```text
I=E+(I-E)
```

produces `C_S+O_S`; no physical branch is split and no absolute value is taken.

## Why the shortcut fails

The old pair owns only `C_S`.  Treating it as the completed remainder would
delete both

```text
actualBandFirstJetCycledResponse(S)
```

and

```text
O_S=J^dagger T(I-E)H_S J G_S^-1.
```

The second term is especially important: `H_S J` need not remain in the outer
support after the adjoint half of the causal transport.  Causality of the
forward frame does not authorize replacing `E H_S J` by `H_S J`.

The correct trace-compatible pair theorem is now explicit:

```text
sourceCorrectedPhysicalSourcePairData.traceProduct=C_S.
```

It may be used only inside the displayed three-term assembly, or after a new
theorem proves a legal same-object cancellation with the other terms.

## Axioms and verification

The generic ring lemma uses exactly `[propext]`.  The eight actual-carrier
declarations use exactly

```text
[propext, Classical.choice, Quot.sound].
```

The shared final verification batch is:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 490/491 focused audits         |  3275 | PASS   |
| CCM25Concrete aggregate              |  3765 | PASS   |
| full repository                      |  3846 | PASS   |
+--------------------------------------+-------+--------+
```

The new files contain no `sorry`, `admit`, or new axiom declaration and emit
no new linter warning.

## Boundary

Proof 491 is an exact alignment theorem, not a uniform estimate.  The active
Gate 3U bottom is a signed compact-support estimate for Proof 490's complete
lower-factor-gauged owner.  Equivalently, any use of the corrected physical
pair must retain the first jet and outer-complement response through the first
absolute value.  The finite-S sign, negative-owner integration, Burnol's
identity, and RH remain open.
