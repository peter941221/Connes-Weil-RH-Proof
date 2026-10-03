# Record 2522 — discharge the 392 fallback cell premises

Target: for `sigma = -1/2` or `sigma = 1/2`, prove the actual repaired
production term is below the replacement table on every cell outside
196..443, without a numerical-bound premise. In particular `cell0_hcell2522`
is a concrete cell inequality whose only hypothesis selects the producer sign.

`C1RouteAFallbackScalar2522.lean` first proves the exact identity

```text
family weighted L1 curvature
  = exp(r/2 - 30) * (|Re c| + |Im c|)
    * (3720/r^2 + 120|theta|/r + |theta|^2 + 60/r + |theta| + 1/4).
```

This combines the positive weight with the negative bump exponent; it does
not use the coarse 2520 upper 64. For each of the 30 exact owner radii,
the 2498 degree-19 Taylor polynomial plus its order-20 remainder bounds
`exp(-(30-r/2))`. Python computes only rational witnesses. Each exponent
bound and each resulting family bound is proved afresh by Lean `norm_num`.
The generator uses exact `Fraction` arithmetic, rounds the exponent upper
upwards to a multiple of 10^-28 and the family upper upwards to a multiple
of 1/1024. There is no imported floating-point analytic assertion.

The 30 rational family uppers sum to `177577883/128 = 1387327.2109375`.
The exported scalar upper is **1387328**. `fallback_hcell2522` proves all
392 non-safe cells for both signs. `ownerProductionTable2522` replaces only
the fallback entries of the old table; the 248 safe entries are unchanged.
The downstream theorem `ownerPanelStripNorm_le_safeTable2522` therefore asks
only for those 248 safe inequalities, instead of all 640 inequalities.

The new table's external remainder reading is `414.5754133864649` versus
the original family-weighted `414.57518775159883`; explicit scalar rounding
costs about `0.000225635`. The total is not yet a Lean-certified analytic
remainder: the safe entries remain unproved. This also does not certify the
node sum, identify the midpoint coefficients with the exact interpolant,
close the selected-detector signed budget, or establish RH.

Evidence and reproduction:

```sh
python3 scripts/routea_fallback_certificate_2522.py
python3 scripts/routea_fallback_certificate_2522.py --check
lake build ConnesWeilRH.Dev.C1RouteAExpFamilyFallback2521Audit ConnesWeilRH.Dev.C1RouteAFallbackCertificate2522Audit
python3 scripts/validate_fallback_build_2522.py --mirror BUILD_MIRROR --log BUILD_LOG
```

Run the build under `scripts/run_resource_aware_task.sh`, retaining the log.
`results/2522_fallback_certificate.json` pins the generated witnesses and
sources; its status deliberately requires a separate build.
`results/2522_fallback_build_validation.json` records actual build/audit
acceptance and source-cone comparison. Initial build failures are retained
in local logs: table comparison needed the correct side of addition
monotonicity, and the real-valued rational table needed `noncomputable`.
Regeneration follows every generator edit before the accepted build.

Accepted validation: the resource-managed Linux build completed successfully
(3901 build-plan jobs). All ten audited declarations have exactly
`[propext, Classical.choice, Quot.sound]`. All 188 project-source files in
the import cone match the authoritative working tree byte for byte; six
pre-existing newline-only mirror differences were synchronized before the
final build. Mathlib HEAD equals the manifest pin
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. The numeric control reproduced
the entire 2517 artifact exactly and checked both signs.
