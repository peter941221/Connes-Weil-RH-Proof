# G8 P1 prolate-history energy consumer (2026-09-11)

`C1G8P1BoundaryColumnEnergy` now proves the first concrete same-owner
Hilbert--Schmidt consumer for the metric boundary history.  For the genuine
source-prolate factor `Q₀(E−R₀)`, transported through the source inclusion and
its adjoint, Lean proves

```text
∑ᵢ ‖History_S ((J† · Q₀(E−R₀) · J) eᵢ)‖²
  ≤ ∑ᵢ ‖Q₀(E−R₀) bᵢ‖².
```

The proof uses the named-basis Hilbert--Schmidt precomposition inequality,
the contractive subtype inclusion (and adjoint), and the previously proved
Julia-history energy contraction.  It does not identify metric boundary maps
with radial prime-power crossings, and it does not provide the finite-prime
trace comparison, cutoff remainder limit, or the detector-specific P2
producer.

Evidence: owning build `1369_g8_p1_prolate_history.log` and audit build
`1370_g8_p1_prolate_history_audit.log` completed successfully (3464/3465
jobs), with no `error:` or `sorryAx` lines; the audit reports only
`[propext, Classical.choice, Quot.sound]`.  The six-target P1/P2/P3 import
batch, `1371_g8_p1_p2_p3_batch.log`, also completed successfully (4082 jobs)
with no `error:` or `sorryAx` lines.

Status: **formal consumer-side P1 energy bound; P2/P3 remain open**.

RH is not claimed.
