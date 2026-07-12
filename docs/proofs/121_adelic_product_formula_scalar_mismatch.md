# 121 Adelic Product Formula Scalar Mismatch

Date: 2026-07-12

## Source Fact

Burnol explains that the global additive characters preserving the principal
adeles as their own annihilator form a torsor under `Q^*`.  Replacing the
character by `q` changes local Weil terms by

```text
log(|q|_v) g(1),
```

and the sum over all places vanishes by the product formula.

## Required Versus Available Coefficients

The positive prime-multiplier completion from Plan 037 requires at finite `p`

```text
2 log(p)/(sqrt(p)+1).
```

To remove this with a principal-idele shift would require

```text
v_p(q)=2/(sqrt(p)+1)
```

for every visible prime.  The left side is an integer; the right side is not,
and it varies with `p`.  No rational `q` supplies these shifts.

Choosing independent real local scales is not a harmless renormalization: it
breaks the principal-idele annihilator condition and changes the global
explicit formula.  It cannot be used as a same-object cancellation theorem.

## Verdict

```text
product-formula cancellation of Plan 037 compensation: impossible
adelic character freedom: retained only as normalization evidence
RH: unproved
```

