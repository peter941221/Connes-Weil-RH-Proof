Record 2661: P095 center normalization against the actual entry integrand
Date: 2026-10-10

Result

Positive.  Two green Lean modules land the first bridge between the ACTUAL
(0,3) entry integrand and the panel certificate lane of records 2655-2660.

1. `ConnesWeilRH/Dev/C1RouteAPanelCenterNormalization2661.lean` (generic
   core, no panel constants): the normalized entry integrand factors on any
   panel as center value times panel phase,

       F(center + position)
         = F(center) * exp(phase(position) - phase(0)),

   both pointwise (`normalizedMomentIntegrand_eq_centerFactor2661`) and as
   an integral identity (`panelCenterNormalization2661`).  The coefficient
   tie between the captured parameters and the panel table enters as the
   explicit hypothesis `hcoef`.

2. `ConnesWeilRH/Dev/C1RouteAPanelCenterNormalization2661P095.lean`
   (instance at the captured (0,3) parameters):

   - exact-rational coefficient tie `panelBetaTie2661P095`:
     `(node_0 + i*theta_3) * r_3^2 = beta + i*psi` of the record-2655
     panel table, by kernel `norm_num` on the literal rationals;
   - the two argument pins `ampArgPin2661P095` / `phaseArgPin2661P095`:
     `beta*c - 30/(1-c^2) = ampArg2657P095` and `psi*c = phaseArg2658P095`
     at `c = 1/200` exactly;
   - the identity `panelCenterNormalization2661P095`:
     `integral F = (ampCenterComplex2660 * rotTrue2660P095)
        * panelIntegralTrue2660P095`;
   - the composed ball `panelTrueBall2661P095`: the true panel integral of
     the ACTUAL normalized integrand lies in the L1 ball around
     `panelAssemblyCenter2659P095` of radius
     `panelAssemblyCharge2659P095 + panelResidualCharge2660P095`.

The build is green with zero errors, zero `sorry`, zero warnings on the new
modules, and all ten declarations auditing to exactly
`[propext, Classical.choice, Quot.sound]`.

Convention verification

The four parameter identities (coefficient tie, amplitude argument, phase
argument, phase spelling) were first verified independently in exact
rational arithmetic (Python `Fraction`, bitwise true on all four checks)
against the committed capture data, table literals and pin artifacts; the
Lean tie and pins re-prove them in the kernel.  The spelling choices were
made so that the final assembly is DEFEQ, not rewrite-based:
`panelPhase2661` at the P095 instantiations is definitionally
`complexPanelPhase2656P095`, and `panelCenterFactor2661` after the pins is
definitionally `ampCenterComplex2660 * rotTrue2660P095`.

Proof architecture

- pointwise: the exponent identity reduces to a ring identity after
  `push_cast` (the pinned Mathlib tags the `Complex.ofReal` family
  `norm_cast`, so all real casts push into sums, products, divisions and
  powers); the exponential split is
  `rw [Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp]`, which
  closes the goal outright -- an appended `rfl` errors "No goals to be
  solved" and must NOT be kept;
- integral: `rw [← intervalIntegral.integral_const_mul]` pulls the center
  factor out (the lemma is `*`-shaped and `@[simp]`), then
  `intervalIntegral.integral_congr` applies the pointwise identity on
  `uIcc (-h) h = Icc (-h) h` (`Set.uIcc_of_le`);
- instance: `rw [hgen]`, then the center-factor rewrite by the two pins,
  then a `rfl`-proved `hInt` transporting the phase-integral spelling to
  `panelIntegralTrue2660P095`, then `rw [hInt]` closes by reflexivity;
- ball: `rw [panelCenterNormalization2661P095]` and
  `exact panelValueBall2660P095`.

Probe evidence

`_probe2661.log` (throwaway module, mechanism probes): kernel `rfl` closes
the vector-literal extractions `capturedNodes2584 0`, `capturedModulations
2584 3` and `capturedWidth2584 3`; `push_cast; ring` closes the complex
exponent identity with free variables; the exp-rewrite chain closes the
assembly without a trailing `rfl`; `abs_add_le` + `linarith` closes the
panel guard.  The probe also caught the two mechanical fixes applied before
the real build: literal extraction defs need `noncomputable`, and the
instance module needs `open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit` for
`storedWidth`.  First real build: green; the only diagnostic was one unused
`simp` argument (`zero_add` in the real-component block), removed, re-built
warning-free.

Evidence

- Lean modules: `ConnesWeilRH/Dev/C1RouteAPanelCenterNormalization2661.lean`
  and `ConnesWeilRH/Dev/C1RouteAPanelCenterNormalization2661P095.lean`.
- Build logs: `_b2661.log` (first green; one unused-simp warning) and
  `_b2661b.log` (final bytes: 0 `error:`, 0 `uses sorry`, 0 warnings on
  the two new modules, 10/10 axiom lines exactly the standard trio,
  `Build completed successfully (3740 jobs)`, both oleans present).
- Source-hash sync (Windows == WSL): generic
  `dd10baa78dbe3b222b1eec24144e007c`, instance
  `26e89dbb949e2a66ff3aae2ae5c5dbb4`.
- Linux-native workspace: `/home/peter/projects/Connes-Weil-RH-Proof`
  (the `/home/peter/rh` mirror is stale at the 2628 era; workspace path
  recovered from the era's build logs, not assumed).

Scope

Entry (0,3), panel P095, plus the generic lemma (which covers any
entry/panel once `hcoef` and the two pins are instantiated).  The remaining
obligations to (0,3) containment are unchanged: the 190-panel partition sum
(per panel: tie + two pins + one instantiation + the certified panel term),
the two edge slices, and the comparison against
`analyticMomentInterval2597_row_03`; then the 870 off-diagonal memberships.
No producer GO and no RH claim is made here.
