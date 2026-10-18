# 2900 Route B composed cosh zero exclusion

For `|t| <= R = 1/20`, the composed argument

`a(t) = 2t/(1-t^2)`

satisfies the elementary bound

```text
|a(t)| <= (2R)/(1-R^2) = 40/399 < 3/2 < pi/2.
```

The zeros of complex `cosh` are `i*pi*(k+1/2)`, whose moduli are at least
`pi/2`. Therefore the composed `cosh(a(t))` denominator cannot vanish inside
the selected Cauchy disk. The remaining formal task is to encode the complex
norm inequality and the standard zero classification in Lean.
