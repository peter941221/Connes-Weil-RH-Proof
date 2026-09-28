# Route A.003 — Panel-local L2 model

Status: ACTIVE INFRASTRUCTURE. Numerically viable; not a producer theorem.

This branch changes the enclosure object rather than tightening the dead
uniform-panel or IBP bounds:

```text
panel-local Taylor model
    + derivative / moment enclosure
    + aggregate charge
    + L5 ideal-vs-stored pricing
    -> L2 model budget
```

Current evidence:

```text
2051  L3 aggregate enclosure
2052  L1 nodal enclosure
2053  L4 horizon / tail audit
2054  reduced-evaluator repricing
2055  third-order sigma model + finer ladder
2056  ideal-vs-stored L5 pricing
2057  split-rule bridge
2058  direct-difference solve pricing
```

Latest reading: `4.412216e10 = 0.1295x` the 10% bar, with `7.72x` margin and
`29/29` controls green in record 2058.

This branch still carries nonclaims: `COVER` is open, the Gram rule and
`a_mat` idealisation gap remain registered, some grid quantities are controls
rather than enclosures, and the result is not yet the selected detector's
same-owner signed inequality.

Authoritative evidence:

- `docs/map/README.md:253`
- `docs/map/README.md:526`
- `docs/map/README.md:655`
- `docs/proofs/2051*` through `docs/proofs/2058*`

Next use: close the model-to-real interface. Do not make another L5 pricing
round unless it removes one of the named nonclaims above.
