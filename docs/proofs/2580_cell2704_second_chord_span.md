# Record 2580: cell 2704 second-chord span

Record 2580 extends the correction second-chord certificate to cell 2704 and
the adjacent span 2703..2705. The fresh endpoint owner is node 2705; the
consumer-required derivative order is two. The generated order-three leaves
remain a compatibility control and are not needed by the second-chord
consumer.

The exact rational assembly gives these cell upper bounds:

```text
sign       cell 2704 upper
minus      0.032416714960059885
plus       0.001485468770406976
```

The span combines the committed 2579 cell-2703 bound with the new cell-2704
bound. The Lean audit build completed 3943 jobs with zero errors and zero
`sorryAx` occurrences. The audited declarations use only
`[propext, Classical.choice, Quot.sound]`.

This is a local two-cell certificate, not full-grid coverage. The
coefficient-distance premise from record 2338 remains an assumption here;
exact coefficient membership, producer GO, and an RH claim remain false.

Evidence:

- `results/2580_second_chord_generation.json`
- `ConnesWeilRH/Dev/C1RouteACorrectionSecondChordSpan2703_2580Audit.lean`
- Linux build log `2580_span_ext4.log`
