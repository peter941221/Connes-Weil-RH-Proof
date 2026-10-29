# Project Memory

Last compressed: 2026-10-29.

This file is a current-state handoff, not a chronological experiment ledger.
Detailed evidence and historical incidents remain in `docs/proofs/` and Git
history. The project does not claim `SourceRH` or RH.

## Current decision tree

```text
Route A healthy CompactLog owner
        |
        +--> selected detector has qw < 0
                 |
                 +--> prove qw >= 0 for that same owner
                          |
                          +--> SourceRH -> Mathlib RH
```

The binding producer bottleneck is the selected-owner signed physical-kernel /
C3' budget. Route B and row-B results are scoped results, not automatic
transfers to the Route A owner.

## Hard verification gate

Every non-trivial Lean build must use a Linux-native WSL2 ext4 workspace. The
repository `lean-toolchain` must be copied or synchronized before building and
must be checked with:

```text
cat lean-toolchain
lean --version
```

Required result: `leanprover/lean4:v4.30.0` and Lean `4.30.0`. If the file is
missing, the version differs, or the build runs on `/mnt/c`, verification stops
and no `.olean` result may be reported as valid. This rule was added after the
3130 build: the temporary WSL tree initially selected Lean 4.33.1 because it
lacked `lean-toolchain`; copying the file corrected the build.

Focused builds and audits must preserve logs, inspect the full error list, and
print exactly `[propext, Classical.choice, Quot.sound]`. Never treat a build
footer alone as proof.

## Mathematical red lines

- No `sorry`, `admit`, new axioms, fake data, or `True`/`Set.univ` shortcuts.
- Preserve owner identity, signed cancellation, support ownership, and the
  correct `2*pi` frequency normalization.
- A finite prime cutoff requires a same-test omitted-term proof or aggregate
  bound. A signed partial remainder is not a sign for the full remainder.
- Do not exchange infinite sums and integrals without proving integrability.
- Numerical experiments need a named decision target and reproducible exact or
  interval evidence.

## Completed records

- `2722F`: stored row-B capture compiled in the WSL dependency chain.
- `3110`, `3119`, `3120`: Route-B powered seed, signed prime cut, and Fourier
  readback dependencies compiled under Lean 4.30.0.
- `3128`: names the owner-specific prime-power residual and proves its exact
  additive decomposition; no residual sign or bound is proved.
- `3130`: defines the finite owner symbol and proves the exact pointwise and
  whole-line integral decomposition under explicit `Integrable` premises.
  Audit passed with the standard axiom trio. This is an interface, not a
  residual estimate or RH proof.
- `3160`-`3165`: indexed producer contracts and support prototypes were audited;
  `3163` proves the current concrete common-only producer construction is a
  no-go, and `3164` records the fixed-index versus test-indexed API boundary.
- `3170`: the selected-owner residual now has a conservative pointwise
  absolute allowance equal to the existing prime-part allowance plus the
  finite-owner kernel coefficient allowance. The focused WSL build and audit
  passed under Lean 4.30.0 with only the standard axiom trio.
- `3171`: combines the finite-owner and residual allowances into the explicit
  same-owner margin gate
  `finite allowance + residual allowance <= -c3Sigma xi -> routeAJointSymbol >= 0`.
  This is a parameterized diagnostic only; because the residual allowance
  already contains the finite allowance, the displayed condition counts it
  twice and is weaker than the direct 3080 lower bound. It is not the binding
  producer route.
- `3172`: defines the live same-owner physical-kernel envelope contract with
  signed centers and nonnegative errors, proves it yields an
  `OrbitPhysicalKernelNodeCertificate`, and bridges it to the existing
  semi-local gate. No numerical node producer has been supplied yet; WSL
  Lean 4.30.0 build and audit passed with the standard axiom trio.
- `3173`: defines the concrete same-owner lower/upper node interval contract,
  converts it to the 3172 center/error envelope, and bridges it to the physical
  kernel gate. Audit passed with the standard axiom trio. Record 2038 remains
  the binding warning that the old one-copy G8-H numerical interval payload is
  not closed.
- `3174`: audited the existing numerical payloads against the 3173 contract.
  The repository has no data-bearing same-owner interval producer: 2523 is a
  fixed midpoint model, 2530 is diagnostic, 2535 is an external whole-cell
  enclosure, 2539 leaves coefficient/numeric membership open, and 2038 leaves
  the one-copy full-line certificate unclosed. This closes the current
  payload-to-producer attempt, not Route A globally.
- `3175`: the same-owner interval certificate is now guarded by an audited
  contradiction theorem. Under a hypothetical right-hand off-line zero,
  `orbitWindowSemiLocalGate_of_owner_node_interval_certificate` gives
  `ICgate <= 0`, while healthy owner geometry gives `ICgate > 0`. The WSL2
  Lean 4.30.0 target and audit passed (3796/3797 jobs) with exactly the
  standard axiom trio. This is a producer-boundary guard; it constructs no
  numerical certificate and makes no RH claim.

## Open obligations

1. Construct an owner-specific `OrbitPhysicalKernelNodeCertificate` for the
   actual geometry, preserving signed cancellation and both frequency signs.
2. Prove its finite aggregate bound on `orbitVisiblePrimeRange geometry` with
   the same owner and support; absolute-value replacement is not sufficient.
3. Feed that certificate into `sourceRH_of_right_orbitGeometry_physicalKernel_certificate`.
4. Reassess the indexed producer only after obtaining a genuine arbitrary-
   convolution support theorem; common-only support is already blocked by the
   3163 concrete no-go.

The immediate producer checkpoint is now explicit: construct one fully closed
same-owner node family with exact lower/upper bounds, both frequency signs,
and a separately verified full-line/tail enclosure before adding any new Lean
producer assembly.

## Reproducibility lessons

- Build continuity is not mathematical progress; each experiment needs a named
  target and a stop condition.
- Native WSL source copies must include `lean-toolchain`; otherwise a different
  Lean version can silently invalidate cached `.olean` evidence.
- Keep the Windows source authoritative, use WSL ext4 for heavy builds, and
  copy logs/artifacts back in the same invocation.
- Avoid quoted `wsl.exe bash -lc` interpolation for `$?`, `$((...))`, and target
  lists. Use WSL-side scripts and explicit status files.
- For cancellation-sensitive enclosures, bind the gate to the same object or
  stencil being enclosed, carry `|value| + error`, and use independent-engine
  anchors.

## Evidence index

- `docs/proofs/3130_routea_owner_residual_margin_bridge.md`
- `docs/proofs/3163_indexed_producer_concrete_no_go.md`
- `docs/proofs/3164_fixed_vs_indexed_prime_support_boundary.md`
- `docs/proofs/3165_test_indexed_prime_support_prototype.md`
- `docs/proofs/3170_routea_residual_absolute_bound.md`
- `docs/proofs/3171_routea_owner_residual_margin_gate.md`
- `docs/proofs/3172_routea_owner_physical_kernel_certificate.md`
- `docs/proofs/3173_routea_owner_node_interval_certificate.md`
- `docs/proofs/3174_routea_owner_interval_producer_no_go.md`
- `docs/proofs/3175_routea_owner_interval_no_go.md`
- `build-logs/3175_wsl_build.log`
- `build-logs/3175_wsl_audit.log`
- `ConnesWeilRH/Dev/C1RouteAOwnerResidualMargin3130Audit.lean`
- `ConnesWeilRH/Dev/IndexedProducerApiAudit3161.lean`
- `ConnesWeilRH/Dev/IndexedProducerConcreteNoGo3163.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerResidualBound3170Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerResidualMargin3171Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerPhysicalKernelCertificate3172Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeIntervalCertificate3173Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeIntervalCertificate3175.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeIntervalCertificate3175Audit.lean`
