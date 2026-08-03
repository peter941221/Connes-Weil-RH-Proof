# Proof 795: Scaled completed forcing support bound

## Result

For the exact complete forcing from Proof 794,

```text
F_(p,S) = -Re Tr(C_(p,S)) + Re Tr(R_(p::S) - R_S),
```

and `c_T = finiteEulerLowerFactor(T)`, Lean now proves

```text
|c_(p::S)^2 F_(p,S)|
  <= (1 + (1 - p^(-1/2))^2) E_root.                  (795.1)
```

Here `E_root` is the same compact-root support energy already used for the
normalized complete endpoint.  No outer, reflected, second-support, prolate,
Markov, or remainder branch is bounded separately.

```text
complete forcing
      |
      v
c_(p::S)^2 F_(p,S)
      |
      +-- exact recurrence --> N_(p::S) - (1-p^(-1/2))^2 N_S
      |
      +-- completed endpoint support bounds --> (795.1)
```

## Why It Matters

This is the first direct support-first bound on the exact forcing scalar in
the physical one-prime recurrence.  The root support is consumed by the
existing completed Hardy--prolate endpoint theorem before the absolute value
in `(795.1)` is taken.

## Limitation

Equation `(795.1)` is still scaled by `c_(p::S)^2`.  It does not bound the
raw forcing `F_(p,S)`, does not supply the required lower-factor-square decay,
and does not prove Gate 3U, the finite-S sign, Burnol's identity, or RH.

## Lean Owner

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovCompletedForcingSupportBound.lean
```

Key declarations:

```text
normalizedCompletePhysicalHermitianTrace_eq_neg_normalizedSourceBandGramTrace_re
abs_normalizedCompletePhysicalHermitianTrace_le_supportEnergy
lowerFactorSq_completePhysicalForcing_abs_le_supportEnergy
```
