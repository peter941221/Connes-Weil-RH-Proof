3176 Route-A Same-Owner Budget Audit
===================================

Status
------

STOP_MISSING_PRODUCER_PREMISE

This record is a fail-closed evidence gate for the selected same-owner
Route-A producer. It does not prove a no-go theorem for Route A, SourceRH, or
the Riemann Hypothesis (RH).

Audited checks
--------------

The current legacy payload preserves same-owner identity, but it does not
close the producer premises required by the Lean route:

- both signed frequency contributions;
- exact visible-prime support and owner transfer;
- source-transform and signed physical-kernel enclosures;
- coefficient and finite-window quadrature enclosures;
- a full-line tail bound;
- a certified negative aggregate margin imported into Lean.

The machine-readable result is
`results/3176_routea_same_owner_budget_audit.json`.

Why this matters
----------------

The Route-A gate needs a lower bound for the same physical object that is
used by the selected owner. A modulus-majorant or scalar acceptance row can
be numerically favorable while still failing to bound the signed aggregate
used by the theorem. Therefore the audit stops before any producer assembly.

Reproduction
------------

```text
python scripts/routea_same_owner_budget_audit_3176.py
```

Expected status:

```text
STOP_MISSING_PRODUCER_PREMISE
```

Nonclaims
---------

- no numerical producer certificate;
- no Lean `SourceRH` certificate;
- no `SourceRH` claim;
- no RH claim.
