# Record 3309: corrected signed-real block manifest

Result: the 3308 corrected signed-real block upper survives outward rounding,
and its exact 160-term sum is still strictly negative. The Lean arithmetic
mirror and the parameterized signed consumer compile and pass axiom audit.
The 160 block dominance inequalities are still open.

The manifest generator is
`scripts/routea_signed_real_upper_manifest_3309.py`. It reads the 3308
diagnostic rows, rounds every signed-real block upper upward to the common
grid `10^-80`, and records the source hash and per-block rounding slack. The
source value is never imported into Lean as a theorem.

The resulting aggregate is

```text
block_upper_sum =
-656499146182745501736821251496030290980612928457864067127693217116763489
/
50000000000000000000000000000000000000000000000000000000000000000000000000000000
approximately -1.312998292365491e-8
```

The maximum per-block rounding slack is approximately `4.09e-81`, so the
rounding operation is far below the negative aggregate margin. The manifest
has 160 blocks of 256 cells covering all 40960 cells.

The exact arithmetic mirror is
`ConnesWeilRH/Dev/C1RouteARationalCorrectedSignedBlockManifest3309.lean`.
It proves both the rational sum and its real cast are negative. The consumer
is
`ConnesWeilRH/Dev/C1RouteARationalCorrectedSignedBlockConsumer3309.lean`.
It wires the 3306 signed-real second/fourth rows and the 3220 sixth-order norm
row into the 3305 consumer, with the new 3309 block constants as explicit
`hblock` targets.

```text
3306 signed real second/fourth bounds
                 |
                 v
3298 tight endpoint + 3220 sixth norm row
                 |
                 v
3309 160-block manifest, exact sum < 0
                 |
                 +--> open: 160 Lean hblock inequalities
                 +--> open: finite-window strict integral theorem
```

Verification was run in a Linux-native WSL2 ext4 workspace with
`leanprover/lean4:v4.30.0` and Lean `4.30.0`:

```text
lake build ConnesWeilRH.Dev.C1RouteARationalCorrectedSignedBlockManifest3309
lake build ConnesWeilRH.Dev.C1RouteARationalCorrectedSignedBlockManifest3309Audit
lake build ConnesWeilRH.Dev.C1RouteARationalCorrectedSignedBlockConsumer3309
lake build ConnesWeilRH.Dev.C1RouteARationalCorrectedSignedBlockConsumer3309Audit
```

The audit reports exactly `[propext, Classical.choice, Quot.sound]` for the
arithmetic and consumer declarations. This record does not claim `producer_go`,
`SourceRH`, or RH.
