# 2896 Route B centered Q series

The removable center variable is

`Q(t) = (1 + tanh(2t/(1-t^2))) / 2`.

Its exact rational expansion through degree 21 is:

```text
Q(t) = 1/2 + t - t^3/3 - 13 t^5/15 + 67 t^7/315
       + 3083 t^9/2835 + 41617 t^11/155925 - ...
```

The complete coefficients are stored in the JSON artifact. This is the correct
centered object for the Cauchy proof; convergence radius and Lean analytic
extension remain open.
