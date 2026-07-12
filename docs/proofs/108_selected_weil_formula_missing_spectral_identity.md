# 108 Selected Weil Formula Missing the Spectral Identity

Date: 2026-07-12

## Audit result

The selected local owner is complete on the arithmetic side:

```text
SelectedWeilFormulaOwner.weilValue
  = poleTerm - archimedeanTerm - globalFinitePrimeTerm.
```

It has exact finite prime support and unconditional archimedean integrability.
However, the repository contains no theorem identifying this value with the
sum over source nontrivial zeros for the same compact test. The zero-index
module still describes that statement as a future spectral-side explicit
formula.

## Missing theorem

For the same selected square, Plan 028 needs a theorem of the shape

```text
owner.weilValue.re
  = sourceZeroSum(owner.square.sourceTest)
```

with absolute/symmetric convergence and the exact centered Mellin convention.
Without it, the Xi quotient's negative zero pattern and the explicit
pole/archimedean/prime formula remain two unrelated numerical objects.

## Consequence

The broad package can no longer be blamed for this gap. The selected owner
already bypasses it. The missing spectral explicit formula is an actual
analytic theorem and is the next source root for Plans 025/028/030.

## Verdict

```text
same-square arithmetic owner: pass
prime support/integrability: pass
same-square spectral zero-sum identity: absent
route status: open but source-analytic
```

