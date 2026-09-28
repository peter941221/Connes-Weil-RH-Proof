# Route A.002 — Quadrature-by-parts architecture

Status: CLOSED. Scoped no-go; do not treat it as an unfinished optimization.

Record 2046 measured `IBP-L2-FAIL`:

```text
2 * TV2 * B2 = 1.83e22
required budget = 1.38e19
ratio = 1826x
```

The derivative-order trade was also measured: one integration by parts was
only `1.28x` better than two, while the direct enclosure was `5.2x` tighter.
This closes the IBP architecture at the registered owner; it does not close
all possible Route A mechanisms.

Authoritative evidence:

- `docs/map/README.md:151`
- `docs/proofs/2046*`

Reopen condition: a changed owner, changed support theorem, or a genuinely
different signed object. Merely increasing derivative order is not sufficient.
