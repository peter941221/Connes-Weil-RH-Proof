# Proof 715: Uncomposed Endpoint Energy Bridge

Proof 715 removes the invalid identity-input handoff exposed by Proof 714.
The Gate consumer now has a direct source-facing contract:

```text
actual completed endpoint/readout producer
  -> combined physical right energy <= fixedPhysicalEnergyMajorant
  -> existing signed Gate trace consumer
```

No premise of the form `Summable (fun i => ||sourceBasis i||^2)` is used, and
no source operator is inserted into the endpoint equality by rewriting. The
remaining source obligation is explicit: produce `hcombined` for the actual
finite-S physical endpoint while preserving the complete signed outer,
reflected, second-support, and prolate branches.

This is an interface correction and a real consumer, not a Gate 3U producer.
The finite-S-uniform `hcombined` source theorem, Gate 3U sign, finite-S sign,
Burnol's identity, and RH remain open.
