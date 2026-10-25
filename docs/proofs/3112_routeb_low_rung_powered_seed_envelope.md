# Route-B low-rung powered-seed envelope (record 3112)

Status: completed analytic envelope adapter. This record does not prove the
three full-frequency cardinal pins, `hgate24`, the spectral prefix bound,
SourceRH, or RH.

Record 2727's controlled comparison identified `{1,2,3,4}` as the first rung
set that clears all three stored row-B pin prices at model grade. Record 3112
formalizes the corresponding low-rung input on the actual Lean seed:

```text
D1 <= 2
D2 <= 8
D3 <= 84
D4 < 1500
```

The first two bounds use the existing exact seed identities, the third uses
the certified rational interval for the third derivative mass, and the fourth
uses the actual D4 certificate from record 3103. These bounds feed the existing
powered-seed endpoint envelope, producing
`norm_cardinalSum_poweredSeed_le_lowRung_env3112` for every finite node set,
coefficient function, strip coordinate in `[0,1]`, and real frequency.

Source and audit modules:

```text
ConnesWeilRH/Dev/C1RouteBLowRungPoweredSeedEnvelope3112.lean
ConnesWeilRH/Dev/C1RouteBLowRungPoweredSeedEnvelope3112Audit.lean
```

Verification used Linux ext4. The source module was compiled with
`lake env lean` and an explicit `.olean` output; the audit entry then printed
all four declarations and their axiom footprints. The analytic envelope and
the D3/D4 leaves use only the standard project axiom trio. The finite rung
membership theorem is computational and has the smaller footprint
`[propext, Quot.sound]`.

This is the exact seam still required before the pin consumer can close:

```text
kernel-checked low-rung envelope (3112)
        |
        v
finite-cell and tail replay against the three wired prices
        |
        v
three cardinal pins -> hgate24 + hprefix -> SourceRH
```

The numerical replay remains separate because an analytic upper envelope is a
formula, while a pin is a quantified inequality over the entire frequency
line. No model-grade float result is promoted by this record.
