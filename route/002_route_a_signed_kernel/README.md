# 002 — Route A: signed physical kernel / C3′

Status: ACTIVE CORE CAMPAIGN. The route is not a producer theorem and RH is
not claimed.

This directory is a navigation layer only. Binding decisions remain in
`docs/map/README.md`, `docs/map/080_c3p_signed_certificate_owner.md`, and
`docs/map/104_route_a_four_round_campaign.md`.

## Fixed consumer and owner

```text
actual selected healthy CompactLog detector g
  -> prove qw(g) >= 0 for that same owner
  -> SourceRH
  -> Mathlib RH
```

The owner is the exact selected detector, with its actual support, support-
derived finite visible-prime set, triple vanishing, and full-line tail. ROOT
models, fixed-prime models, sampled auxiliary spans, and truncated owners are
not substitutes.

## Subroutes

```text
001_panel_local_l2_model/       ACTIVE SUPPORT ONLY
002_c3p_selected_owner/         ACTIVE CORE TARGET; full RH GO OPEN
003_analytic_vertical_tail/     SUPPORT ONLY; required for full line
004_weighted_zero_measure_c3p/  GO-CANDIDATE / UNPRICED
099_frozen_or_audit_only/       CLOSED OR AUDIT-ONLY EVIDENCE
```

The only newly registered candidate is `004_weighted_zero_measure_c3p/`,
corresponding to `A.005.1` in proof record 2177. It must derive a fixed,
nonnegative weight from the same physical-kernel/correction formula and prove
```text
Arch + C3'_aggregate <= -epsilon(rho,N) + B_zm(rho,N)
B_zm(rho,N) < epsilon(rho,N).
```

This is not yet `GO`: the exact-owner weight has not been priced. A valid GO
requires an owner-preserving, independently controlled enclosure with a
strict margin. A numerical sign, a finite known-zero prefix, or a tail-only
bound is insufficient.

## Acceptance ladder

1. Fix the weight formula before evaluating it.
2. Run a fixed-`rho`, fixed-`N` exact-owner enclosure with independent
   interval/rounding control.
3. Pass `B_zm < epsilon` with full signed cancellation retained.
4. Transfer the bound uniformly over the actual off-line-zero owner and then
   connect it to the existing C3′ consumer.

Failure is an owner change, non-finite/unbounded weight sum, loss of signed
cancellation, or `B_zm >= epsilon`. Such a result is a scoped no-go, not a
global impossibility theorem.
