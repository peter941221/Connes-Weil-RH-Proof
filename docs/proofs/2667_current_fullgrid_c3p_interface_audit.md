# Record 2667 - captured-owner full-grid interface audit

**Verdict: CAPTURED-OWNER-INTERFACE-PASS; repair-owner transfer remains open.**

Erratum to the initial 2667 description: artifacts 2422/2424 use the 2275
captured coefficient vectors. The 2359 worker calls `2303.load_owner()`, and
that loader reads the 2275 capture. It does not inject the 2338 repaired
coefficients. Record 2665 confirms this distinction: its control MD5s match
2275, while its treatment MD5s are different. Thus the full-grid number below
is for the captured owner; it is not a repaired-owner C3' budget.

The audit checks the committed 2422/2424 source hashes, the 776,611-node
partition, the 39-span readback, and the four same-expression directed
controls. It does not promote numerical output into a mathematical enclosure.

## Readback

```text
+-----------------------------------------------+------------------+
| quantity                                      | value            |
+-----------------------------------------------+------------------+
| nodes                                         | 776611           |
| span size                                     | 20001            |
| spans                                         | 39               |
| same-expression controls                     | PASS             |
| assembled base_M0 + base_D2                  | 8619.145941699   |
| assembled corr_M0 + corr_D2                  | 138085.480163030 |
| captured-owner channel sum                    | 146704.626104729 |
| knownError2109 comparison reference           | 74601530.30234718 |
| captured-owner sum / reference                | 0.0019665096     |
+-----------------------------------------------+------------------+
```

The ratio is descriptive only: because these coefficients are the captured
owner, it is not a bound on the repaired owner's mathematical `chargeRest`.
The producer theorem still requires a mathematical enclosure for the actual
owner, not merely a sum of floating-point evaluator outputs.

## Open obligations

1. Replay the full grid after injecting the 2338 coefficient repair; record
   2668 supplies that missing owner-specific numerical input.
2. Prove pointwise mathematical-term dominance for the repaired owner.
3. Import the directed span witnesses and accumulation theorem into Lean.
4. Assemble the signed full-line C3' budget, including the infinite-xi tail.
5. Prove the actual-owner identity and coefficient-box membership before using
   the resulting bound in `hcharge`.

The signed FFT tail screen is not a certificate: the committed record-2278
artifact marks that route `FFT-TAIL-UNTRUSTED`. Therefore this record does not
establish `producer_go`, `SourceRH`, or RH.

## Evidence

- `scripts/routea_current_fullgrid_audit_2426.py`
- `results/2422_repaired_shared_geometry_776611.json`
- `results/2424_repaired_span_composite_bridge.json`
- `results/2667_current_fullgrid_audit.json`
- `results/2275_gap_owner_audit.json`
- `results/2665_l1_margin_repair.json`
- `results/2278_signed_kernel_tail_screen.json`
