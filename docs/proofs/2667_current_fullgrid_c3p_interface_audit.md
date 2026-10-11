# Record 2667 - repaired-owner full-grid C3' interface audit

**Verdict: INTERFACE-AUDIT-PASS; C3' producer gate remains open.**

This record replays the current repaired-owner full-grid interface from the
committed 2422 and 2424 artifacts. It checks source hashes, the 776,611-node
partition, the 39 span readback, and the four same-expression directed
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
| all four assembled channels                   | 146704.626104729 |
| knownError2109                                | 74601530.30234718 |
| current window / knownError2109               | 0.0019665096     |
+-----------------------------------------------+------------------+
```

The channel sum is a numerical interface reading only. The producer theorem
still requires a bound on the mathematical `chargeRest`, not merely a sum of
floating-point evaluator outputs.

## Open obligations

1. Prove pointwise mathematical-term dominance for the repaired owner.
2. Import the directed span witnesses and accumulation theorem into Lean.
3. Assemble the signed full-line C3' budget, including the infinite-xi tail.
4. Prove the actual-owner identity and coefficient-box membership before using
   the resulting bound in `hcharge`.

The signed FFT tail screen is not a certificate: the committed record-2278
artifact marks that route `FFT-TAIL-UNTRUSTED`. Therefore this record does not
establish `producer_go`, `SourceRH`, or RH.

## Evidence

- `scripts/routea_current_fullgrid_audit_2426.py`
- `results/2422_repaired_shared_geometry_776611.json`
- `results/2424_repaired_span_composite_bridge.json`
- `results/2667_current_fullgrid_audit.json`
- `results/2278_signed_kernel_tail_screen.json`
