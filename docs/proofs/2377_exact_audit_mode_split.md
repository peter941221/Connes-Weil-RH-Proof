# 2377 — exact-audit mode split

Date: 2026-10-02.

The nodal replay now has an explicit `--skip-exact-audit` mode.  It removes
the per-term `Fraction` construction while retaining the directed MPFR term
and accumulation path.  On the 1001-node control, the interval integrals,
directed integrals, and interval minimum product are identical to the full
exact-audit run.  The skip mode therefore changes only the auxiliary audit,
not the evaluator values.

The 776611-node replay still exceeded the bounded 180-second run even with
the exact audit disabled and produced no artifact.  This record is a runtime
diagnostic, not a numerical certificate; exact-audit dominance, nodewise
Lean import, and the full-grid replay remain open.
