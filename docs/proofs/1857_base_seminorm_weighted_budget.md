# 1857 - Finite-window base seminorm budget

Date: 2026-09-23.

Status: Formally verified in Lean; quantitative interface reduction.

The new leaf `C1P2BaseSeminormBound.lean` proves three facts for the existing
finite-window construction:

1. The zero-order seminorm of `compactLogTestOfWindow g` is bounded by the
   zero-order seminorm of the positive-variable source test `g`.
2. The source seminorm of a finite windowed combination is bounded by the
   coefficient-weighted sum of the basis seminorms.
3. A coefficient-weighted budget at most `1/2` gives the strict contraction
   required by the convolution route:

```text
2 * seminorm(base) < 1.
```

This does not yet prove the budget for the right-inverse coefficients. It
replaces the missing unstructured seminorm field with an explicit finite
quantity that can be certified separately. The quadratic tail constant `C`
is not used as a seminorm substitute.

Verification: WSL focused build
`base-seminorm-1857i.log`; 3476 jobs completed successfully, zero `error:`
lines, zero `sorryAx`, and all four audited declarations depend only on
`[propext, Classical.choice, Quot.sound]`.
