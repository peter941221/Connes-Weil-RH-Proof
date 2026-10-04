Record 2573: production-grid price of the 2562 correction-second construction

Verdict: OVER BUDGET at the committed correction pair and 10240-cell grid.
The external enclosure price is about 7.7 times the pin at both signs.
The 2566 constant-per-cell second-channel production plan is stopped at
these inputs. The local certificates in records 2570-2572 remain valid.
This result is a failure of this bound construction, not a global
impossibility theorem or evidence against RH.

Object and scope

The owner is the 2338 ideal_correction_coefficient row, with the same
centers as 2570 and uniform coefficient-distance allowance 1e-28.
A coefficient-distance allowance means the unknown actual coefficient
must be within that distance of the stored center. This is still a
premise: the actual exact interpolation solution has not been proved
to meet it in Lean.

Let c be the correction physical function and W(x) = exp(sigma*x)*c(x).
The 2562 decomposition bounds the integral of exp(sigma*x)*norm(c''(x))
by the integrals of norm(W''), 2*abs(sigma)*norm(W'), and sigma^2*norm(W).
A prime means a derivative with respect to x. The signed sum retains
complex phase cancellation at point evaluations; the variation bound
sums absolute values of the individual families.

The mesh has cells = 10240, radius R = 6.5536001, and h = 2*R/cells.
The pin, the accepted total budget, is 41654536587/62500 = 666472.585392.
Every reported total below comes from exact Fraction accumulation of
outward Arb enclosures, not from multiplying two local-cell prices by
the grid size. A numerical enclosure contains the exact mathematical
value; it does not make the resulting table a Lean numerical certificate.

Production-grid result

Command in a configured Linux workspace:
  python scripts/price_decomposed_correction_grid_2573.py --cells 10240

The JSON stores exact rational values; this table rounds for readability.

```text
+-----------------+--------------------+--------------------+
| channel         | sigma = -1/2       | sigma = +1/2       |
+-----------------+--------------------+--------------------+
| second integral | 5130776.73136131   | 5105691.92425523   |
| first integral  |    6503.31119667   |    5827.50058613   |
| value integral  |      22.87210110   |      18.21780732   |
| total           | 5137302.91465908   | 5111537.64264868   |
| pin             |  666472.585392     |  666472.585392     |
+-----------------+--------------------+--------------------+
```

Cause of the excess

The second-integral bound expands into
  h*sum(second midpoint bounds)
  + h^2/2*sum(unsigned third endpoint terms)
  + h^3/4*sum(whole-cell fourth envelopes).

A whole-cell envelope bounds the derivative at every position in a cell,
including where a family crosses its compact-support boundary.

```text
+-----------------------+---------------+---------------+
| second-channel charge | minus         | plus          |
+-----------------------+---------------+---------------+
| signed midpoint       |  125428.90    |  100344.10    |
| unsigned third        | 4849971.55    | 4849971.55    |
| fourth inflation      |  155376.27    |  155376.27    |
+-----------------------+---------------+---------------+
```

The unsigned third term dominates. Taking absolute values before adding
families removes their cancellation: +100 and -99 cost 199 instead of 1.
The pointwise three-term identity itself is not the dominant loss.
Record 2574 changes the second-integral method while preserving the owner,
coefficient allowance, grid, and first/value channels.

Validation and disposition

scripts/validate_decomposed_correction_grid_2573.py checks exact totals,
profiles, both signs, source hashes, unchanged local anchors 2570-2572,
and the same-run direct 2561 baseline. The direct 2561 node, remainder,
total and margin fields reproduce the predecessor exactly.

Independent mpmath controls include 90 derivative evaluations, 18
reconstruction checks, and 90 sampled fourth-envelope checks. The samples
are controls, not a proof of a full-cell integral bound. Four corrupted
artifacts are rejected: zero total, missing sign, wrong coefficient owner,
and an unproved membership claim.

No Lean numerical-table certificate, table-rounding price, exact
coefficient membership, producer GO, or RH claim is supplied here.

Evidence

  scripts/price_decomposed_correction_grid_2573.py
  scripts/validate_decomposed_correction_grid_2573.py
  results/2573_decomposed_grid_256.json
  results/2573_decomposed_grid_10240.json
  results/2573_decomposed_controls_10240.json
  docs/proofs/2574_same_owner_second_chord.md
