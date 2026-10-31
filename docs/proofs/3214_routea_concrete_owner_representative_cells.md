3214 Route-A Concrete-Owner Representative Cell Replay
=======================================================

Status
------

PASS_REPRESENTATIVE_CELL_REPLAY_ONLY

Purpose
-------

This record isolates the first, middle, and last cells of the 40960-cell
Taylor-6 diagnostic for the concrete record2680 owner. It verifies the exact
cell geometry, the Taylor aggregation formula, and upward rounding for every
row before retaining only the three representative rows.

Reproduction
------------

    python scripts/routea_concrete_owner_probe_3214.py

Output
------

    results/3214_routea_concrete_owner_representative_cells.json

Observed result
---------------

The probe validates all 40960 rows and selects indices 0, 17168, and 40959.
The two outer diagnostic-boundary cells have zero value, second-derivative,
and fourth-derivative uppers; their cell charge is entirely the sixth-order
remainder. The selected middle cell is the most negative cell in the full grid,
with an upper of approximately -38.0161. Across the full grid, 18695 cells
are negative and 22265 are positive; the final negative margin comes from their
signed aggregate cancellation.

This is useful for proof design, but it is not a Lean certificate. The probe
does not prove the Arb intervals, derivative identities, or the full-line
tail. It also does not set producer_go.

Next proof boundary
-------------------

Formalize one outer cell and one interior cell with the same owner hash and
exact rational bounds. If the outer cell closes using the existing support
lemmas while the interior cell does not, use a split proof architecture:
support-zero boundary blocks plus an aggregate interior derivative envelope.
End of record 3214.
