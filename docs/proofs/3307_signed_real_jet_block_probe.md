# Record 3307: superseded signed real jet block probe

Status: superseded diagnostic. The row shape tested here was too weak for the
3306 theorem and must not be used as the current mathematical conclusion.

The probe evaluates the exact record 2680 owner at every cell midpoint and
uses the 3306 row shape

```text
second row  = abs(real(signed aggregate second jet))
fourth row = abs(real(signed aggregate fourth jet))
```

It keeps the 3220 uniform sixth-order complex-norm row and reuses the directed
3300 endpoint rows and 3302 block constants. The script is
`scripts/routea_signed_real_jet_block_probe_3307.py`; its result is stored in
`results/3307_signed_real_jet_block_probe.json`.

All 160 blocks remain above the corresponding 3302 manifest constant. The
diagnostic summary is:

```text
positive gaps: 160 / 160
minimum gap:   approximately 6.385559487775981e-12
maximum gap:   approximately 4.8946980969093e-2
block sum:     approximately 6.315548500316968e-1
```

This is a named no-go for the combination

```text
3300 directed endpoint
        +
3306 exact-owner midpoint second/fourth rows
        +
3220 uniform sixth norm row
```

The `abs(real(...))` operation discards the sign of negative derivative rows.
That is stronger than necessary and is not the corrected 3306 upper shape.
Record 3308 reruns the same screen with `real(signed aggregate jet)` and is the
current diagnostic record. The Arb run is external evidence only and is not
imported into Lean.

Execution note: the WSL2 system Python did not have the `flint` package, and
the configured package mirror did not provide it during the run. The diagnostic
was therefore executed with the already installed Python 3.13 `flint` runtime
on the Windows side. The Lean provider and axiom audit remain independently
verified in the required WSL2 ext4 Lean 4.30.0 environment.
