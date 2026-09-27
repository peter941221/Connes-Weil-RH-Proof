# 002.002 — Route B: same-owner four-point SPAN

Status: DEAD_ON_CURRENT_FAMILY. RH is not claimed.

Decision (2026-09-27): freeze this Route-B family. The committed gate rows
occur at n = 2, 3, while the same-index tail first becomes closable at n = 4;
the two obligations have no common index. This is a scoped family no-go, not a
global impossibility result for every future four-point construction.

Reopen only after a cheap, named-hypothesis probe produces either:

```text
1. a complete-owner gate row at the tail-closure index or later; or
2. an all-strip q bound strong enough for the actual gate row and lambda.
```

Until then, do not spend Lean or interval-certification work on the current
n = 2, 3 rows.

This route keeps one actual owner and tries to produce one detector with both
sign conditions:

```text
same owner g_n
    |
    +-- determinant gate: det_n < 0
    |       -> gate(h_n.square) < 0
    |
    +-- joint tail: beta_s * L_n < multiplicity_rho * lambda_n^2
            -> qw(h_n) < 0

same detector h_n also needs:
    qw(h_n) >= 0
```

Minimum joint target:

```text
C_n > 0
b_n > 0
det_n = C_n * D_n - b_n^2 < 0
beta_s * L_n < multiplicity_rho * lambda_n^2
```

The determinant and tail must use exactly the same:

```text
rho, owner, base, correction, n, lambda_n, support, visible-prime set
```

Current candidate:

```text
T = 28
q = 2^(-14)
n = 2, 3     <- the admissible gate rows found by record 2032, on the changed
                named hypotheses (height gamma and owner cardinality N).
                The old n = 4 candidate is WITHDRAWN (2026-09-27): that gate
                row was a dxi = 0.05 resolution artifact (records 2028/2029).
                n = 1 and n >= 4 carry no gate row on this family.
```

Live screen state after the 2026-09-27 batch:

```text
R-B0 owner            known-zero under-approximation, complete owner OPEN
R-B1 q (Cut 1 tail)   PRICED VIABLE AND MASS-CERTIFIED: the k = 3 weighted
                      mass has a genuine interval bracket (20000 panels,
                      19728 sign-certified, 272 enveloped) and the strip bound
                      recomputed with the bracket UPPER end is 3.001847e-07
                      against q = 2^-14, margin 203.33x (records 2031/2033 P6)
R-B2 determinant      CHEAP: detUpper < 0 needs only eps < 3.8e-3 .. 9.0e-2
                      (0.4142 vertex-centred), and the sign pair C > 0, b > 0
                      now EXISTS on 9 admissible n >= 1 rows (record 2032)
R-B3 tail ratio       THE BINDING WALL, obstruction changed shape:
                      PAIR-MISMATCH. On every gate row (n = 2, 3) the
                      same-index tail budget is already above 1 at the
                      lambda -> infinity limit (tau_inf = 2.1e10 .. 9.7e12);
                      the tail first closes one step later at n = 4, where the
                      gate pattern is gone. The gate index and the tail index
                      are DISJOINT on this family. Record 2029's "no
                      admissible n >= 1 gate row" is retired (record 2033)
R-B4 coverage         OPEN, and now doubly gated: RADIUS-FRAGILE (only 1 of 15
                      rows keeps the pattern at delta = +1 and +2, record
                      2034) plus the R-B0 prerequisite
```

Current evidence is only an under-approximation and grid/proxy evidence. It is
not an interval proof and not a complete-owner result.

Fast survival decision:

```text
R-B0  complete owner and exact visible-prime source
R-B1  corrected-base all-strip q screen
R-B2  same-owner signed determinant margin
R-B3  same-index tail ratio
R-B4  all-rho quantifier coverage and Lean consumer assembly
```

R-B0/R-B1 survival does not imply RH survival. R-B2 and R-B3 are independent
kill points; R-B4 is the final universal-coverage gate.

Authoritative records:

- `docs/map/106_centered_signed_moments_joint_tail_execution.md`
- `docs/map/103_four_point_same_span_three_cut_campaign.md`
- `docs/proofs/1982_powered_contraction_candidate.md` (gate row withdrawn)
- `docs/proofs/2029_coupling_scan_outcome.md`
- `docs/proofs/2030_determinant_certification_margin.md`
- `docs/proofs/2031_sharp_q_ladder_outcome.md`
- `docs/proofs/2035_route_b_full_block_outcome.md` (the 2032-2034 batch outcome:
  gate rows, radius robustness, gate/tail pairing, interval mass)
- `scripts/fourpoint_powered_contraction_1982.py`

See `001_survival_screen.md` for the pre-Lean triage protocol.
