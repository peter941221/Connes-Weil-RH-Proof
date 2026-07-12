# CC20 Parameterized Haar Measure

Date: 2026-07-12

Status: source measure family accepted; parameterized kernel operator and
exhaustion trace remain open.

## Result

For every `lambda > 1`, Lean now defines the exact source measure

```text
d rho / rho on [1/lambda, lambda].
```

The main declarations are:

```text
cc20WindowBaseMeasure
cc20WindowHaarDensity
cc20WindowHaarMeasure
cc20WindowHaarMeasure_univ_lt_top
integral_cc20WindowHaarMeasure_eq_smul
```

The base interval has measure

```text
lambda - 1/lambda,
```

the density is bounded by `lambda`, and the resulting Haar measure is finite.
The integral bridge expands the same object exactly as

```text
integral f d(mu_lambda)
  = integral ((1/rho) * f(rho)) d(base_lambda).
```

Source module:

```text
ConnesWeilRH/Source/CC20Concrete/ParameterizedHaarMeasure.lean
```

## Route Meaning

Together with proof 165, the carrier chain is now concrete:

```text
positive compact source test
  -> support inside [1/lambda,lambda] for some lambda
  -> finite source Haar measure d rho/rho on that same interval
```

No change-of-window invariance or trace limit is asserted. The next owner must
put the ordinary CC20 regular kernel on `Lp C 2` for this same parameterized
measure and prove compatibility when `lambda` increases.

## Verification

Using the existing WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/ParameterizedHaarMeasureAudit.lean
```

Both passed. The focused declarations print only:

```text
propext
Classical.choice
Quot.sound
```

No RH premise, Weil-positivity premise, or `sorryAx` occurs.

## Route Judgment

```text
parameterized source carrier: accepted
parameterized source Haar measure: accepted
parameterized regular-kernel L2 operator: open
lambda-exhaustion trace/read-off: open
RH: unproved
```
