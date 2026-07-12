# 087 Compact Log Mellin Normalization Survives

Date: 2026-07-12

## Source theorem

`ConnesWeilRH/Source/CC20YoshidaConvolution.lean` proves
`laplaceAt_compactLogTestOfWindow_eq_mellin`. For a positive-variable test
`g` supported in `(a,b)`, its raw log pullback

```text
f(u) = g(exp u)
```

has bilateral Laplace transform equal to the project's Mellin transform:

```text
laplaceAt(f,s) = mellin(g,s).
```

The proof performs the change of variables `t = exp u` and is already
source-backed; it is not the rejected additive toy model.

## Centered coordinate

Set `u = s - 1/2`. Then the centered transform is simply

```text
Laplace_centered(f,u) := laplaceAt(f,u + 1/2).
```

The functional-equation involution `s -> 1 - conjugate(s)` becomes
`u -> -conjugate(u)`. No extra pointwise half-density factor is needed in this
coordinate, because the Jacobian in the displayed Mellin change of variables
has already produced the exponent `s` in `g(exp u)`.

## Gate verdict

```text
log convolution -> Mellin normalization: survives
centered orbit involution: survives by parameter shift
compact source owner integration: still open
```

The prior concern about the raw pullback is therefore narrowed: the required
repair is a centered parameter owner, not a new multiplicative factor in the
test function.

