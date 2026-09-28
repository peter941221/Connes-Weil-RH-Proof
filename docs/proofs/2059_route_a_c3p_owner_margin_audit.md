# 2059 - Route A C3' selected-owner margin audit

Date: 2026-09-28.

Status: OWNER-ALIGNED-L2-MARGIN-AUDIT. This is a bounded core audit, not a
producer theorem and not an RH claim.

Consumer:

```text
C1P2DirectSemiLocalGate
    -> orbitWindowSemiLocalGate
    -> same-owner qw(g) >= 0
    -> SourceRH
```

Owner contract:

```text
owner       = one-copy G8-H
rho         = 0.6 + 40.9187190121475i
scale       = 0.88
support     = 9.504
visible book= 1647 prime powers
basis       = 17, rank 17, nullity 0
```

The audit cross-reads the owner metadata in record 2058 against the two
one-copy rows of record 2037. All owner guards pass: owner label, support,
visible-prime book size, basis size/rank, and absence of an affine nullspace.

The inherited signed readings are:

```text
Q400  = -1.1111757839943652e20
Q1600 = -3.406049871881275e12
L2 charge = 4.412215566637855e10
```

Therefore the L2 charge is below the sampled negative magnitude at the
registered reduced-evaluator owner:

```text
L2 / |Q1600| = 0.012954054498916812
sampled margin = 3.361927716214886e12
```

Decision: `L2-BUDGET-BELOW-SAMPLED-NEGATIVE-MARGIN`.

This is useful because the owner is no longer the immediate blocker: if the
signed value and every transfer error were enclosed on the same object, the
current L2 budget would fit inside the observed negative margin by a wide
factor. The next blocker is the certificate interface, not another generic L5
price.

Nonclaims:

- `Q400` and `Q1600` are inherited sampled/refinement readings, not full-line
  interval enclosures.
- The L2 charge is not yet a model-to-real enclosure for the selected detector.
- The Gram rule, `a_mat` idealisation gap, and `COVER` remain open.
- No producer theorem or RH claim follows from this audit.

Reproducibility:

```text
python scripts/routea_c3p_owner_margin_2059.py
```

Artifact: `results/2059_route_a_c3p_owner_margin.json`.

Source records:

- `results/2037_route_a_g8h_basis_comparison.json`
- `results/2058_l5_solve.json`
- `docs/map/080_c3p_signed_certificate_owner.md`
- `docs/map/082_direct_semilocal_gate_assault.md`
