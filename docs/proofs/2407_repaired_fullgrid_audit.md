# 2407 — repaired full-grid same-expression audit

Date: 2026-10-02.

After the 2398 evaluator repair, the 776611-point replay was regenerated as
`results/2406_repaired_shared_geometry_776611.json`. The directed control now
uses the exact public binary64 operands (`hypot`, `exp`, cell weight) lifted
into MPFR before RNDU multiplication and accumulation.

The independent readback passed source-hash checks, the 39-span contiguous
partition, same-expression span dominance in all four channels, same-expression
integral dominance in all four channels, and term-roundup dominance. The
interval minimum product is positive (`337039.476950803`).

The older 2386 bridge is intentionally not reused: its node totals belong to
the superseded evaluator revision. A fresh interface-only bridge was generated
as record 2408, and its node readback and arithmetic assembly also pass. This
record remains diagnostic; Lean numeric import, the analytic remainder
theorem, producer closure, and RH remain open.

Evidence: `scripts/routea_repaired_fullgrid_audit_2407.py`,
`results/2406_repaired_shared_geometry_776611.json`,
`results/2407_repaired_fullgrid_audit.json`, and
`results/2408_repaired_composite_charge_bridge.json`.
