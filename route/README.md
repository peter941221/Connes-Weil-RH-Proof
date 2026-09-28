# Route topology

This directory is a navigation layer for proof routes. It does not replace the
authoritative records in `docs/map/`, and it does not promote a candidate to a
producer theorem.

Authority order:

```text
route/README.md
    |
    +-- navigation and current status only
    |
    v
docs/map/README.md
    |
    +-- binding route decisions and active obligations
    |
    v
Lean source + paired audits + proof records
```

Current topology:

```text
000_rh_mainline/
    001_shared_contracts/
        SourceRH consumer, owner rules, quantifier rules, audit gates
    002_b5_compactlog/
        Healthy CompactLog B5-shaped producer mainline
        001_route_a_signed_kernel/
            Same-owner signed physical-kernel / C3' campaign
                001_uniform_panel_interval/  CLOSED - L2 width no-go
                002_ibp_quadrature/          CLOSED - IBP L2 no-go
                003_panel_local_l2_model/    ACTIVE infrastructure only
                004_selector_family/         CLOSED / PARKED by selector
                005_c3p_selected_owner/      ACTIVE core producer target
                099_frozen_or_audit_only/    Frozen evidence
        002_route_b_fourpoint_span/
            Same-owner four-point SPAN / determinant + joint-tail campaign
        099_frozen_or_audit_only/
            Frozen descendants of the B5 campaign
```

The single RH core obligation is:

```text
hypothetical off-line zero
    -> selected healthy CompactLog detector g with qw(g) < 0
    -> prove qw(g) >= 0 for that same owner
    -> SourceRH
    -> Mathlib RiemannHypothesis
```

A route is not considered alive merely because it has Lean interfaces or a
numerical candidate. It must preserve the same owner, support, visible-prime
set, detector, and quantifiers through the final consumer.

Route A execution rule:

```text
dead architecture -> keep its no-go and reopen only after a named hypothesis changes
viable L2 model  -> use as infrastructure, not as a producer theorem
next core strike  -> price the signed C3' margin on the actual selected owner
```

Read next:

1. `000_rh_mainline/README.md`
2. `000_rh_mainline/002_b5_compactlog/README.md`
3. `000_rh_mainline/001_shared_contracts/README.md`
3. `000_rh_mainline/003_route_c_trace_formula/README.md`
4. `000_rh_mainline/004_common_bottleneck_audit/README.md`
5. `000_rh_mainline/001_shared_contracts/README.md`
6. `docs/map/README.md` for binding decisions
