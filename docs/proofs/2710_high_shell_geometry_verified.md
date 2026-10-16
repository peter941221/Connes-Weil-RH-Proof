# Record 2710: kernel-checked high-shell geometric bounds

Status: FOUR GEOMETRY THEOREMS CHECKED; NO COMPLETE-OWNER TAIL CERTIFICATE.

`C1HighShellGeometry2710.lean` independently verifies the geometry proposed in
2709 with Mathlib imports only. No 2695 aggregate or entry tree is imported.
The finite target had a 120-second timeout per invocation and one runtime
worker. The final timed invocation succeeded in 45.38 seconds with maximum
resident memory 2,672,512 KiB (about 2.55 GiB), exit status 0, and generated
an OLean. Windows and WSL source SHA-256 values were compared after checking.

The four audited theorems are:

```text
distance_sq_le                  each orbit distance squared <= (13/4)*y^2
orbit_product_le                four-factor modulus <= (169/16)*y^4
orbit_multiplier_le             shifted modulus <= (169/16+abs(lambda))*y^4
spectral_distance_product_le    two weighted squared distances <= (169/16)*y^4
```

All require source and evaluation points in the strip, y=abs(Im z)>=1,
and the existing high-shell separation `2*abs(Im rho)<=y`. They bound the
complex norm, not merely the real part, and work for both signs of Im z.
The multiplier theorem permits any real lambda. Each audited declaration
has exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

Reproduction in a prepared Linux workspace:

```text
LEAN_NUM_THREADS=1 timeout 120 lake env lean \
  ConnesWeilRH/Dev/C1HighShellGeometry2710.lean \
  -o results/C1HighShellGeometry2710.olean
```

The log is `results/2710_high_shell_geometry_lean.log`. Initial unsuccessful
iterations exposed associativity and square-expression normalization issues;
only the final successful log is evidence for the completed four declarations.

## Complete-owner readiness check

The remaining input is substantive. Record 2033 obtains C4/C2 by a finite
height grid (401 nodes, three sigma values); these are not directed global
upper bounds. Its source-zero owner is an under-approximation. Record 2031's
weighted contraction estimate is likewise a numerical price on its specific
owner and cannot be transferred to the three different 2709 passing rows.
The actual shell-prefix factor and multiplicity are also absent there.

Consequently the 2709 prices 0.235..0.305 are not certified margins. Even
in the unit proxy with q fixed, they allow only roughly a factor 1.8..2.1
inflation of the sampled C4*C2 product, because that product is squared.
No evidence here bounds that inflation. The gate values likewise still need
complete-owner certification. Building the new lemma does not establish any
of these inputs or reopen the frozen family.

The next admissible target is an analytic, directed high-strip bound for the
exact selected base/correction, with its prefix and gate owner explicitly
identified. Stop before any batch or aggregate build if those objects cannot
be identified from the committed evidence. The geometry is now available as
a checked ingredient; full analytic tail wiring and producer positivity remain
open. No Producer GO, SourceRH, or RH claim is made.
