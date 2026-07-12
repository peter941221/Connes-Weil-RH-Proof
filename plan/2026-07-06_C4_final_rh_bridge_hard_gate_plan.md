# C4 Final RH Bridge Hard Gate Plan

## 1. Hard Completion Gate

C4 is solved only when the public no-argument theorem proves
`_root_.RiemannHypothesis` through the visible route/source bridge chain.  It
does not close if `final_connes_weil_rh` or any downstream theorem returns a
stored `mathlibRH` field.

```text
old weak path:
  RouteFinalExitPackage.mathlibRH
    -> mathlib_rh_of_route_final_exit_package
    -> final_connes_weil_rh
    -> unconditional_rh_skeleton

  NormalizedNoArgumentRouteCertificatePackage.mathlibRH
    -> mathlib_rh_of_normalized_no_argument_route_certificate_package
    -> unconditional_rh_contract_skeleton

new semantic owner/API:
  RouteCertificate built from C1-C3 semantic owners
  cc20_source_rh_of_route_certificate
  Source.RHDefinitionBridge.source_rh_to_mathlib_rh

real consumer rewired:
  final_connes_weil_rh
  unconditional_rh_skeleton
  unconditional_rh_contract_skeleton
  any public no-argument theorem exported by ConnesWeilRH.lean

same-object alias / wrapper rejection scan:
  rg -n "mathlibRH\\s*:|pkg\\.mathlibRH|\\.mathlibRH|mathlib_rh_of_route_final_exit_package|mathlib_rh_of_normalized_no_argument_route_certificate_package|_root_\\.RiemannHypothesis\\s*:=\\s*by\\s*exact\\s+.*\\.mathlibRH|\\bTrue\\b|Set\\.univ|sorry|admit|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Route.RouteTheorem
  lake env lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean
  lake build ConnesWeilRH

focused axiom audit targets:
  ConnesWeilRH.Route.cc20_source_rh_of_route_certificate
  ConnesWeilRH.Route.final_connes_weil_rh
  ConnesWeilRH.Route.route_final_exit_mathlib_rh_uses_source_bridge
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton
  ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_contract_skeleton

semantic sufficiency for final RH step:
  The final theorem has no arguments.  Its proof path exposes the CC20 source
  criterion and the Mathlib bridge.  No input structure may store
  `_root_.RiemannHypothesis` as the active proof source.
```


## 2. Result First

Result:
  Planning only. No Lean proof progress.

Plan source:
  This plan follows `plan/README.md`.

Parent map:
  `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lists C4 under
  `[C] route / ledger / final bridge`:

```text
C4. final RH bridge
  -> source-backed route theorem
  -> restricted-to-full theorem
  -> sign-defect theorem
  -> no-argument _root_.RiemannHypothesis
```

Evidence from current code:

```text
ConnesWeilRH/Route/RouteTheorem.lean:1493
  structure RouteFinalExitPackage

ConnesWeilRH/Route/RouteTheorem.lean:1510
  route_final_exit_package_of_certificate

ConnesWeilRH/Route/RouteTheorem.lean:1549
  mathlib_rh_of_route_final_exit_package

ConnesWeilRH/Route/RouteTheorem.lean:3267
  final_connes_weil_rh

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4611
  structure NormalizedNoArgumentRouteCertificatePackage

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4620
  mathlibRH : _root_.RiemannHypothesis

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4751
  theorem unconditional_rh_skeleton
```

Current status:
  The route layer can derive Mathlib RH from a `RouteCertificate`, but the
  final no-argument skeleton still has packaging surfaces that store
  `_root_.RiemannHypothesis` as a field.  C4 is solved only when the no-argument
  theorem is a proof term from lower route/source data, not a projection from a
  package that already contains RH.


## 3. What Counts As Solved

All items below must hold.

```text
1. old weak path:
     RouteFinalExitPackage.mathlibRH
       -> mathlib_rh_of_route_final_exit_package
       -> final_connes_weil_rh

   and

     NormalizedNoArgumentRouteCertificatePackage.mathlibRH
       -> mathlib_rh_of_normalized_no_argument_route_certificate_package
       -> unconditional_rh_contract_skeleton

   are deleted from the active final proof path or demoted to
   compatibility-only.

2. new semantic owner/API:
     a complete RouteCertificate whose bridge is built from:
       C1 RouteLedgerSemanticData,
       C2 RestrictedToFullQWBridgeContract,
       C3 source-backed route consumers,
       CC20 RHDefinitionBridge source criterion.

3. semantic theorem:
     `final_connes_weil_rh` and the final no-argument theorem prove:

       route certificate
       -> cc20_source_rh_of_route_certificate
       -> RHDefinitionBridge.source_rh_to_mathlib_rh
       -> _root_.RiemannHypothesis

   without using `mathlib_rh_of_route_final_exit_package` as the active exit.

4. consumer declarations:
     unconditional_rh_skeleton
     unconditional_rh_contract_skeleton
     any public final theorem in `ConnesWeilRH.lean`

   use the direct proof term from route certificate to Mathlib RH.

5. same-object alias / wrapper rejection scan passes.

6. WSL build passes:
     lake build ConnesWeilRH

7. focused axiom audit passes for the exact C4 targets listed below.

8. semantic sufficiency for final RH step:
     the final theorem has no arguments and its proof path bottoms in C1-C3
     semantic owners plus the CC20 source-to-Mathlib bridge, with no package
     field containing RH as an assumption.
```

Complete resolution means `final_connes_weil_rh`, `theorem
unconditional_rh_skeleton : _root_.RiemannHypothesis`, and the public root
theorem prove RH from the route certificate chain.  A package field named
`mathlibRH` can exist only as a compatibility readback whose value comes from
the same direct chain and does not feed an active final theorem.


## 4. What Does Not Count

Rejected as not solved:

```text
- returning `pkg.mathlibRH`;
- adding another no-argument package that stores `_root_.RiemannHypothesis`;
- proving final RH by projecting from `RouteFinalExitPackage.mathlibRH` while
  hiding the source RH bridge;
- leaving `final_connes_weil_rh` as
  `mathlib_rh_of_route_final_exit_package (route_final_exit_package_of_certificate cert)`;
- keeping final proof on a compatibility theorem family such as
  `final_rh_of_normalized_*` that takes unresolved source packages as inputs;
- making `RouteCertificate` contain `_root_.RiemannHypothesis`;
- using a project-local `RH` abbreviation as the final target;
- accepting a clean axiom audit for a theorem whose statement is a wrapper
  around an RH field.
```

Allowed compatibility:
  `RouteFinalExitPackage` may remain as a diagnostic object if
  no active theorem proves RH by projecting from it.  `final_connes_weil_rh`
  and the public no-argument theorem must expose the direct proof chain from
  `cc20_source_rh_of_route_certificate` to
  `Source.RHDefinitionBridge.source_rh_to_mathlib_rh`.


## 5. Current Evidence

Code facts:

```text
RouteFinalExitPackage stores:
  sourceRH : inputs.cc20.rhDefinitionBridge.SourceRH
  mathlibRH : _root_.RiemannHypothesis

Source:
  ConnesWeilRH/Route/RouteTheorem.lean:1493

route_final_exit_package_of_certificate constructs both fields from the
certificate:
  ConnesWeilRH/Route/RouteTheorem.lean:1510

mathlib_rh_of_route_final_exit_package returns the stored field:
  ConnesWeilRH/Route/RouteTheorem.lean:1549

final_connes_weil_rh uses a route certificate:
  ConnesWeilRH/Route/RouteTheorem.lean:3267

final_connes_weil_rh currently returns the package field through
mathlib_rh_of_route_final_exit_package:
  ConnesWeilRH/Route/RouteTheorem.lean:3272

NormalizedNoArgumentRouteCertificatePackage stores mathlibRH:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4611
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4620

unconditional_rh_skeleton currently calls final_connes_weil_rh:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4751
```

Interpretation:
  `final_connes_weil_rh` has the right argument shape, but its proof body still
  exits through `RouteFinalExitPackage.mathlibRH`.  C4 must rewrite that theorem
  first, then rewire the no-argument skeleton.


## 6. First-Principles Dependency Chain

The final theorem must expose this chain:

```text
C1 route ledger semantic data
  |
  v
C2 restricted-to-full bridge
  |
  v
C3 source-backed route consumers
  |
  v
RouteCertificate
  |
  v
CC20 Proposition C1 source criterion
  |
  v
RHDefinitionBridge.source_rh_to_mathlib_rh
  |
  v
_root_.RiemannHypothesis
```

The weak final chain stores the answer:

```text
NormalizedNoArgumentRouteCertificatePackage
  |
  v
mathlibRH : _root_.RiemannHypothesis
  |
  v
projection theorem
```

That shape can typecheck while hiding the final proof path.


## 7. Implementation Route

Step 1. Pin current local types.

```lean
#check ConnesWeilRH.Route.RouteCertificate
#check ConnesWeilRH.Route.RouteFinalExitPackage
#check ConnesWeilRH.Route.cc20_source_rh_of_route_certificate
#check ConnesWeilRH.Route.final_connes_weil_rh
#check ConnesWeilRH.Source.RHDefinitionBridge.source_rh_to_mathlib_rh
#check ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton
```

Step 2. Rewrite the route-level final proof first.

Preferred shape:

```lean
theorem final_connes_weil_rh
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    _root_.RiemannHypothesis := by
  exact Source.RHDefinitionBridge.source_rh_to_mathlib_rh
    inputs.cc20.rhDefinitionBridge
    (cc20_source_rh_of_route_certificate cert)
```

This theorem must not call `mathlib_rh_of_route_final_exit_package`.

Step 3. Define the direct no-argument final proof.

Preferred shape:

```lean
theorem unconditional_rh_skeleton : _root_.RiemannHypothesis := by
  exact ConnesWeilRH.Route.final_connes_weil_rh
    normalizedRouteCertificateFromTheorems
```

This is acceptable only after C1-C3 gates make
`normalizedRouteCertificateFromTheorems` semantically sufficient.

Step 4. Replace package-field exits.

Target declarations:

```text
NormalizedNoArgumentRouteCertificatePackage
normalizedNoArgumentRouteCertificatePackageFromTheorems
mathlib_rh_of_normalized_no_argument_route_certificate_package
unconditional_rh_contract_skeleton
```

Expected direction:

```text
normalizedRouteCertificateFromTheorems
  -> cc20_source_rh_of_route_certificate
  -> Source.RHDefinitionBridge.source_rh_to_mathlib_rh
  -> unconditional_rh_contract_skeleton
```

If a package remains, it must store route certificate and source RH bridge
evidence, not `_root_.RiemannHypothesis` as an input-like field.

Step 5. Expose the final proof path.

Add or keep a theorem that states:

```lean
theorem final_rh_uses_source_bridge :
    final_connes_weil_rh normalizedRouteCertificateFromTheorems =
      Source.RHDefinitionBridge.source_rh_to_mathlib_rh
        ... (cc20_source_rh_of_route_certificate
          normalizedRouteCertificateFromTheorems) := ...
```

Use the exact normalized names after C1-C3 settle.  The theorem must make the
source-to-Mathlib bridge visible to reviewers.

Step 6. Build root target.

The C4 gate is final-facing.  Run the full project build after smaller Route
and Dev checks pass.


## 8. Static Rejection Scans

Run these scans after implementation.

RH field and projection scan:

```text
rg -n "mathlibRH\\s*:|pkg\\.mathlibRH|\\.mathlibRH|mathlib_rh_of_route_final_exit_package|mathlib_rh_of_normalized_no_argument_route_certificate_package|NormalizedNoArgumentRouteCertificatePackage" ConnesWeilRH -g "*.lean"
```

Expected result:
  No active final theorem should prove RH by projecting a stored `mathlibRH`
  field.  Remaining hits must be compatibility or diagnostics with a visible
  direct proof source.

Final theorem family scan:

```text
rg -n "theorem final_rh_of_|theorem unconditional_rh|final_connes_weil_rh|cc20_source_rh_of_route_certificate|route_final_exit_package_of_certificate" ConnesWeilRH -g "*.lean"
```

Same-object alias / wrapper scan:

```text
rg -n "_root_\\.RiemannHypothesis\\s*:=\\s*by\\s*exact\\s+.*\\.mathlibRH|mathlib_rh.*:=.*mathlib_rh|\\bTrue\\b|Set\\.univ|sorry|admit|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH -g "*.lean"

rg -n -C 8 "theorem final_connes_weil_rh|mathlib_rh_of_route_final_exit_package" ConnesWeilRH/Route/RouteTheorem.lean
```

Root export scan:

```text
rg -n "RiemannHypothesis|unconditional_rh|final_connes_weil_rh|ConnesWeilRH" ConnesWeilRH.lean ConnesWeilRH -g "*.lean"
```


## 9. WSL Build Gate

Use the main WSL mirror.

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Route.RouteTheorem'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH'
```

The full build is mandatory for C4 because the public target is the root
project theorem, not a route-local helper.


## 10. Focused Axiom Audit

Create one scratch file in the WSL mirror with:

```lean
import ConnesWeilRH
import ConnesWeilRH.Route.RouteTheorem
import ConnesWeilRH.Dev.UnconditionalSkeleton

#check ConnesWeilRH.Route.cc20_source_rh_of_route_certificate
#print axioms ConnesWeilRH.Route.cc20_source_rh_of_route_certificate

#check ConnesWeilRH.Route.final_connes_weil_rh
#print axioms ConnesWeilRH.Route.final_connes_weil_rh

#check ConnesWeilRH.Route.route_final_exit_mathlib_rh_uses_source_bridge
#print axioms ConnesWeilRH.Route.route_final_exit_mathlib_rh_uses_source_bridge

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton

#check ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_contract_skeleton
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_contract_skeleton
```

If the public root theorem has a different name, add it to the same scratch
file.

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```

Rejected output:

```text
sorryAx
project-local axiom
constant
opaque
unsafe
stored `_root_.RiemannHypothesis` field used as proof source
project-local RH abbreviation used as final target
```


## 11. Final Acceptance Text

Use this exact shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  RouteFinalExitPackage.mathlibRH and
  NormalizedNoArgumentRouteCertificatePackage.mathlibRH no longer feed an
  active final theorem.

New semantic owner:
  normalizedRouteCertificateFromTheorems built from C1-C3 semantic owners.

Semantic theorem:
  final_connes_weil_rh, unconditional_rh_skeleton, and the public root theorem
  prove _root_.RiemannHypothesis through cc20_source_rh_of_route_certificate
  and RHDefinitionBridge.source_rh_to_mathlib_rh.

Consumer rewires:
  unconditional_rh_skeleton
  unconditional_rh_contract_skeleton
  public root theorem

Semantic sufficiency:
  The final theorem is no-argument and its proof path exposes the source RH
  criterion and Mathlib bridge.  It does not project a stored RH field.

Build:
  <exact WSL command and result>

Focused axiom audit:
  <target list and axiom output>

Remaining black box:
  <first C1-C3 semantic dependency still not drilled, if any>
```
