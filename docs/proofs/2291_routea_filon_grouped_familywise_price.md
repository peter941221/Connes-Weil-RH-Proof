# 2291: grouped versus familywise fifth-derivative price

Date: 2026-09-30

Decision: any strict enclosure for the 24:4 Filon candidate must preserve the complete complex family sum; familywise absolute values are structurally too expensive.

## Method

At 33 interior points per panel, the fifth derivative is priced in two ways:

```text
G^(5)(y) = fifth derivative of the complete owner sum
familywise = sum_j |(family_j)^(5)(y)|
```

Both are inserted into the same 24-panel degree-4 Lagrange residual shape. This is a comparison screen, not a uniform enclosure.

## Result

```text
channel       familywise / grouped price ratio
base                         4.0692x
corr                      3572.8966x
```

The correction channel is the binding warning: taking absolute values before summing destroys approximately four orders of magnitude of cancellation. A familywise MPFR interval implementation would therefore reject the otherwise viable 24:4 candidate even before kernel-weighted functional propagation.

## Decision

The next certified derivative enclosure must operate on the complete complex owner amplitude, with real and imaginary interval channels summed before modulus. Per-family positive majorants are not admissible for this candidate.

This is compatible with the project owner guard: preserve the actual corrected width-a^2 owner, the stored coefficient vectors, and the support-derived 41136 prime-power set.

## Nonclaims

- Sampled maxima are not uniform derivative bounds.
- The ratio is a feasibility comparison, not a certificate.
- No hgap supplier, producer GO, selected-detector readback, or RH conclusion follows.

## Reproduction

```text
python scripts/routea_filon_grouped_familywise_price_2291.py
python -m unittest discover -s scripts -p 'routea_filon_grouped_familywise_selftest_2291.py' -v
```
