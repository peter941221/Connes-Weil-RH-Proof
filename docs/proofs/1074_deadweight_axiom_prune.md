# 1074 - Deadweight frontier-axiom inventory and prune (hygiene, no semantics)

Date: 2026-08-31. Scope: every `axiom` declaration on the frontier tree.
RH NOT claimed; this record changes no proof semantics - the RH-output
axiom residual is byte-identical before and after.

## Inventory method

Exact declaration enumeration, not line greps: `^axiom\s+NAME\s*:` across
all of `ConnesWeilRH/` (the naive `grep -c '^axiom'` count of 40 on
`UnconditionalSkeleton.lean` includes one prose line at :146; the true
declaration count was 39, all in that one file). Each name then got a
repo-wide identifier-reference count.

## Census (39 real axiom decls, all in Dev/UnconditionalSkeleton.lean)

| tier | count | meaning | action |
|------|-------|---------|--------|
| LEDGER | 5 | on the transitive closure of `rhDefinitionBridgeToMathlibFromTheorems`; printed by the audit | keep |
| WRAPPED | 8 | each has a live wrapper `def ...FromTheorems := <root>`, and those wrappers are consumed by larger structure instances in the same file | KEEP (see verdict) |
| DEADWEIGHT | 26 | zero identifier references anywhere: dangling sockets from retired interpretations | PRUNED (this record) |

The WRAPPED eight:
`normalizedSourceObjectBridgeReadOffRowsInputRoot`,
`normalizedSourceObjectScalarRemainderRowsProviderRoot`,
`normalizedSelectedFinitePrimeIndexDifferenceInputRoot`,
`normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsRoot`,
`normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot`,
`normalizedSelectedFinalRouteConcreteCanonicalRoutePackageCoverageRoot`,
`normalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageRoot`,
`normalizedSelectedFinalRouteCertificateCarrierRoot`.

## Prune

Wave 1: 26 axiom declaration units plus their attached doc comments,
55 lines, `UnconditionalSkeleton.lean` 8088 -> 8033 lines. By construction
nothing referenced them, so the build needed no repair.

## Guarded acceptance

1. `lake build ConnesWeilRH.Dev.RhOutputAxiomLedger` after the prune:
   zero `^error:` lines, footer `Build completed successfully (3775 jobs)`
   (warm-cache no-op total-graph footer).
2. `#print axioms` on the RH output: byte-identical 8-axiom residual -
   three Lean foundations plus exactly the five ledger roots.
3. Post-prune `^axiom` decl count in the skeleton: 13 real + 1 prose =
   14 lines (5 LEDGER + 8 WRAPPED).

## Rejected method (negative result, kept as a landmine note)

A first attempt pruned all 34 non-ledger roots and let compiler
"unknown identifier" errors drive the transitive consumer deletion.
On this 8k-line file the unit-boundary parse mis-sliced multi-field
structure instances: one wave removed 2,282 lines and then reported
unknown identifiers inside the LIVE bridge region (e.g. field providers
of `normalizedSourceObjectPackageFromTheorems`, and
`normalizedSourceObjectRHExitObjectFromTheorems.rhDefinitionBridge` at
:1428). That was over-deletion of live wiring - fully reverted by
`git checkout`. Lesson: consumer-closure pruning in this file needs
Lean-side per-declaration axiom checks, not text cascade; the WRAPPED
eight therefore stay until a real rewiring round retires them.

## Why the deadweight was safe to remove but the wrapped is not

The 26 were sockets welded to nothing: declared, never plugged. Removing
a declared-but-unused axiom cannot change any theorem statement. The 8
wrapped roots ARE plugged - through their `FromTheorems` wrappers into
alternate interpretation instances - so removing them forces those
instances to be rebuilt without the field or deleted; that is a design
change about which interpretations we keep, not hygiene, and is left to
a future rewiring record.
