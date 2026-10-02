# Record 2497 — uniform exponential bound is not a route to hcell

The first candidate for proving the 2496 per-cell premise was to replace all
local bump factors by the global rational bound

`Real.exp (-30) <= 10^-13`.

The bound itself is Lean-checkable with `Real.exp_bound'` and `norm_num`, but
it is far too coarse for the corrected 2496 table.  The MPFR routing probe
`scripts/diag_owner_hcell_exp_bound_2497.py` evaluates the same owner inputs
and grid while replacing the local exponent by that uniform bound.  Against
the corrected 2495/2496 cell payloads it reports, for each sigma sign:

- `421` of `640` cells above the table;
- worst ratio `1147018264624721.5`;
- worst cell `0` for sigma `-1/2` and cell `639` for sigma `+1/2`.

This is a scoped no-go for the uniform-exponent proof strategy, not a
statement about the hybrid construction.  The failure is expected at cells
where the true `exp(-30/(1-a^2))` decay is essential.  The next admissible
step is a partitioned endpoint-ratio enclosure, with each exponential
bounded by a rational Taylor enclosure and with the resulting slack priced
before any Lean data is regenerated.  The probe is diagnostic external data;
it is not a numerical certificate, producer GO, or RH claim.
