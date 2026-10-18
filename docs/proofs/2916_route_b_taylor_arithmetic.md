# 2916 Route B Taylor arithmetic replay

The Lean module `C1RouteBTrigTaylor2916.lean` defines the order-20 Taylor
polynomials for sine and cosine and proves their rational interval at the
left endpoint representative.  This is only the polynomial arithmetic layer;
the analytic Taylor remainder connecting these polynomials to `Real.sin` and
`Real.cos` remains open.

