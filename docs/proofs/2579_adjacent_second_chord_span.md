# Record 2579: adjacent correction second-chord span

Verdict: the cell-2703 correction second-chord certificate closes at both
signs, and the adjacent two-cell span [2702, 2704] closes by adding the two
certified cell integrals. This is a local continuity control, not full-grid
coverage.

## Construction

Record 2577 supplies fresh order-two endpoint owners at nodes 2702, 2703, and
2704. Record 2578 already closes cell 2702. Record 2579 generates the fresh
node-2704 owner, the order-two derivative leaves, and the cell-specific fourth
envelopes for cell 2703. The span theorem uses interval-integral additivity.

```text
node2702 ---- cell2702 ---- node2703 ---- cell2703 ---- node2704
     |             |              |             |             |
   order-2       2578           shared        2579         order-2
   endpoint      cell           endpoint      cell         endpoint
```

The second-chord consumer needs order-two endpoints. The generator therefore
does not create an order-three owner for node 2704. The validator also checks
that the legacy default interface still verifies orders two and three.

## Results

```text
+--------+----------------------+----------------------+----------------------+
| sigma  | fourth upper         | cell-2703 upper      | span-2702..2704      |
+--------+----------------------+----------------------+----------------------+
| -1/2   | 91404.73420393883    | 0.032143775029258005 | 0.06401665241347980  |
| +1/2   |  4146.137710915317   | 0.001471088119751863 | 0.002927923114013575 |
+--------+----------------------+----------------------+----------------------+
```

The exact rational values are stored in
`results/2579_second_chord_validation.json`; displayed values are rounded
only for readability. The span upper is the exact sum of the committed 2578
cell upper and the new 2579 cell upper.

## Verification

- Lean audit build: 3947 jobs, zero errors.
- Axiom audit: 262 declarations, each with exactly
  [propext, Classical.choice, Quot.sound].
- Independent validator: 4 fresh endpoint replays and 24 rejection controls.
- Rejection controls cover zero factors, wrong derivative order, opposite
  owner, wrong position, zero fourth envelope, opposite sign, zero cell total,
  and invalid order selections.
- Regeneration is deterministic and leaves all generated source bytes unchanged.
- Source/config mirror closure: 238 files.
- Record-2271 Linux integration: 22 tests passed.

## Scope boundary

The certificate assumes the correction coefficient distance premise from the
2338 repair data. It does not prove coefficient membership, full-grid coverage,
the base norm, producer GO, or RH. The span is useful because it tests the
adjacent-cell assembly mechanism before mass generation; it is not a license
to multiply one local bound across the grid.

Evidence:

- `scripts/generate_second_chord_span_2579.py`
- `scripts/validate_second_chord_span_2579.py`
- `scripts/build_second_chord_span_2579.py`
- `ConnesWeilRH/Dev/C1RouteACorrectionSecondChordSpan2702_2579.lean`
- `results/2579_second_chord_validation.json`
