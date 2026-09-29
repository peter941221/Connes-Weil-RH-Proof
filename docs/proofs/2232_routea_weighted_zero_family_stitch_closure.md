# 2232 — Family-stitch closure of the 2229 node envelope

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Record 2229 reported each node total by stitching the 30 per-family rows in
binary64: `total = nextafter-up(total + gl + sim)`. This record closes that
stitch with a two-part argument and a directed re-accumulation experiment,
turning the 2229 nonclaim ("family totals are combined in binary64 with
upward inflation") into a lemma-backed statement.

## Lemma

For `g, s >= 0` that are already outward-rounded binary64 values of the exact
family charges,

```text
c2 = fl(fl(T + g) + s)
nextafter-up(c2) >= T + g + s
```

Proof mechanism: each round-to-nearest step loses at most half a spacing of
its result downward, so `fl(fl(T + g) + s) >= T + g + s - spacing(c2)` (the
second result's spacing dominates the first's half-spacing for these
magnitudes); one `nextafter` step upward adds exactly one spacing. The
stitch is outward, non-strict. The lemma is stated on paper here; Lean
formalization is not claimed.

## Directed verification

The committed per-family rows are re-accumulated with 256-bit MPFR RNDU
(`gl` and `simpson` fed through `mpfr_add` with RNDU into a single
accumulator, 60 additions per node):

```text
nodes verified                     30 / 30
rows per node                      30
worst node                         2
MPFR-RNDU re-accumulation          8.792971355816368e-09   (node 2)
reported 2229 total                8.792971355816406e-09   (node 2)
reported - recomputed              3.8050308177439273e-23
relative slack, node 2             4.327354956327679e-15
relative slack, node 1             4.656045912096321e-15
relative slack range (all nodes)   [2.536371840662237e-15, 4.656045912096321e-15]
deficits (reported < recomputed)   none
```

Every reported 2229 node total lies strictly above the directed
re-accumulation of its own rows, with the deficit channel empty at all 30
nodes. The observed slacks (2.5e-15 to 4.7e-15 relative) sit at the
expected binary64 stitch scale: two nearest roundings plus one spacing.

## What this closes and what it does not

Closed: the accumulation step of ladder item 2 ("binary64 operand
construction + finite-sum accumulation enclosure"): the per-term chain is
MPFR RNDU (2229), the family stitch is outward (this record), and the
reported node totals are upper bounds under the discrete-defined operand
convention (2230).

Not closed by this record:

- the operand construction ledger itself (coefficient solve, quadrature
  generation, x-node generation), priced separately in 2233;
- the Lean formalization of the stitch lemma;
- owner transfer and the signed producer margin (ladder items 4 and 5).

## Provenance

- script: `scripts/routea_weighted_zero_family_stitch_2232.py`
- input: `results/2229_q_mpfr_node*.json` (30 node artifacts, committed)
- output: `results/2232_family_stitch_closure.json`
- MPFR backend: `scripts/routea_weighted_zero_mpfr_exp_binding_2223.py`
  (libmpfr.so.6, 256-bit, RNDU)
- no producer or RH claim