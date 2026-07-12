# Proof 187: CC20 source-to-log Schwartz selected-formula bridge

## Result

Every existing `PositiveIntervalCompactTest p` now owns one exact chain

```text
p.test
  -> cc20LogPullback p
  -> cc20LogPullbackSchwartz p
  -> compactLogTestOfPositiveIntervalCompactTest p
  -> selectedWeilFormulaOfPositiveIntervalCompactTest p.
```

There is no second test witness in this chain.  The log-coordinate Schwartz
map is definitionally the function

```text
t |-> normalizedCC20ConcreteTestAlgebra.legacy.encode p.test (exp t).
```

## Lean evidence

`GlobalLogHaar.lean` proves:

```text
contDiff_cc20LogPullback
cc20LogPullbackSchwartz
cc20LogPullbackSchwartz_coe
cc20LogPullbackSchwartz_support_subset
```

The smoothness proof composes the source Schwartz map's `smooth` theorem with
`Real.contDiff_exp`.  Compact support is the already proved transport of
`p.support_subset` to
`[log p.lower, log p.upper]`.  `HasCompactSupport.toSchwartzMap` therefore
constructs the log test without an analytic premise.

`SelectedYoshidaBridge.lean` then proves and constructs:

```text
compactLogTestOfPositiveIntervalCompactTest
compactLogTestOfPositiveIntervalCompactTest_apply
compactLogTestOfPositiveIntervalCompactTest_support_subset
selectedWeilFormulaOfPositiveIntervalCompactTest
selectedWeilFormulaOfPositiveIntervalCompactTest_sourceTest_apply
cc20LogPullbackLp_ae_eq_selectedWeilFormula_sourceTest
```

The selected formula owner consequently uses the genuine additive
convolution square of this same log pullback.  The last theorem identifies the
global `L2` input `cc20LogPullbackLp p` almost everywhere with that formula
owner's `square.sourceTest.test`, so the operator and formula carriers no
longer require an informal function-level identification.

## Verification

The retained-cache WSL builds passed:

```text
lake build ConnesWeilRH.Source.CC20Concrete              3504/3504
lake build ConnesWeilRH.Source.CCM25Concrete             2965/2965
```

The import audits print the public types and report only:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx` and no new theorem premise beyond the source test `p`.

## Route judgment

This closes the carrier mismatch between an existing CC20 positive compact
source test and the selected CCM25 log-coordinate formula owner.  It does not
identify the finite-window regular-kernel positive trace with that selected
Weil formula.  In particular, it does not supply the required finite-S
single-crossing coefficients, compact post-Q remainder, same-test trace
read-off, or RH.
