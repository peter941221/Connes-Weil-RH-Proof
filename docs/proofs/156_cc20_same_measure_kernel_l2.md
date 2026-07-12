# CC20 same-measure kernel L2 gate

The compact regular kernel is now proved to belong to `L2` on the exact
product measure used by `cc20CompactL2Operator`:

```text
MemLp cc20CompactRegularKernel 2
  (cc20CompactMeasure.prod cc20CompactMeasure).
```

Consequently its squared norm is Bochner integrable on that product measure.
Fubini identifies the product integral with the iterated section integral:

```text
integral x, integral y, |K(x,y)|^2
  = integral p, |K(p)|^2.
```

This removes the previous mismatch between the real-coordinate rectangle
integral and the subtype measure used by the completed `L2` operator. The
remaining Hilbert--Schmidt step is Parseval: identify this finite double
integral with `sum_i ||T e_i||^2` for a Hilbert basis.
