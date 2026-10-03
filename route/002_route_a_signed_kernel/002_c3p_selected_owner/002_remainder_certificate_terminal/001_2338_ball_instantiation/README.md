# 001 — 2338 exact-ball instantiation

Status: `COMPLETED SUPPORT / NOT A PRODUCER GO`. Records 2460-2466
instantiate the generic 2459 quadrature attachment with the coefficient balls
from record 2338 and lift it through the three panel geometries.

The owner decision is binding:

```text
2338 exact interpolation balls  -> production strip certificate
2275 capture vectors             -> mechanism validation only
```

Record 2456 rules out using the 2275 capture vectors for the production strip
path because record 2337 found nonzero interpolation residuals. Record 2338
instead encloses the unique solution of the analytic system `A x = y` in the
same 30-family basis. The import must preserve those balls as intervals; it
must not cast their midpoints into new exact coefficients.

## Completed chain

```text
1. Freeze the 2338 artifact and source hashes.
2. Import the 30 base/correction coefficient rectangles.
3. Instantiate the 2459 panel hull on positive, negative, and cross-zero panels.
4. Expose the universal indexed panel dispatcher.
```

The completed acceptance gates are:

```text
artifact/source hash check                  PASS
all 30 coefficient balls imported           PASS
panel containment for every branch          PASS
node-sum upper below the frozen pin          DEFERRED to subtask 002
standard axiom audit                        [propext, Classical.choice, Quot.sound]
capture-vector substitution                FAIL (must remain rejected)
```

The completed panel chain still does not prove exact-owner invertibility, the
node-sum pin, the complete signed C3' margin, producer GO, `SourceRH`, or RH.

The next executable work is recorded in
`../002_640_node_sum_certificate/README.md`.

Primary evidence:

- `docs/proofs/2338_exact_interpolation_repair.md`
- `docs/proofs/2456_ownership_target_ruling.md`
- `docs/proofs/2459_quadrature_attachment_wc.md`
- `results/2338_exact_interpolation_repair.json`
- `ConnesWeilRH/Dev/C1RouteAQuadratureAttachment2459.lean`
