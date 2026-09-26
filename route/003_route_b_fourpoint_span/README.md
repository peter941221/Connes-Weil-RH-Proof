# 003 — Route B: same-owner four-point SPAN

Status: PROJECT CANDIDATE. RH is not claimed.

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
n = 4
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
- `docs/proofs/1982_powered_contraction_candidate.md`
- `scripts/fourpoint_powered_contraction_1982.py`

See `001_survival_screen.md` for the pre-Lean triage protocol.