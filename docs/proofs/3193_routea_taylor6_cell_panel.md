# 3193 Route A Taylor-6 Cell Panel

Status: the exact cell-integration algebra is formalized; the pointwise
Taylor remainder remains a separate premise.

`intervalIntegral_symmetricTaylor6_upper3193` accepts a pointwise upper bound
of the form

```text
f(x) <= f(m) + f2(m) * (x-m)^2 / 2
             + f4(m) * (x-m)^4 / 24
             + M6 * (x-m)^6 / 720
```

and proves the integrated coefficients

```text
h * f(m) + h^3 * f2(m) / 24
  + h^5 * f4(m) / 1920 + h^7 * M6 / 322560
```

where `h = right - left` and `m = (left + right) / 2`. The theorem does not
claim the pointwise inequality or the nonnegativity of `M6`; those must later
come from a Lean Taylor remainder theorem and the sixth-order derivative
budget.
