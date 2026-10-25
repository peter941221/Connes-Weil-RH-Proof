# Actual D4/D7 input reaches the poweredSeed envelope (3104)

Date: 2026-10-25.

Record 3103 proved the actual seed bounds. Record 3104 now instantiates the
generic poweredSeed envelope from record 2725 with those bounds and the exact
mass identity from record 2728.

The fixed data are:

```text
l1Mass smoothSeed = 3
D(4) = 1500
D(7) = 2000000000
rungs = {4, 7}
```

The theorem
`norm_cardinalSum_poweredSeed_le_d4d7_env3104` proves, for every finite node
set, coefficient function, strip coordinate in `[0,1]` and real frequency,
that the same-owner `cardinalSum` at `poweredSeed` is bounded by the explicit
endpoint-max and two-rung envelope `d4d7PoweredSeedEnvelope3104`.

This is the precise interface now closed:

```text
actual smoothSeed D4/D7 integrals
              |
              v
derivOrderL1 bounds at k = 4, 7
              |
              v
2725 poweredSeed transform envelope
              |
              v
3104 explicit cardinal-sum envelope       CLOSED
              |
              v
three numerical cardinal pins              OPEN
```

The envelope still contains the actual node products, coefficients and
frequency-dependent minimum. This is intentional. A scalar cardinal pin is a
uniform numerical inequality over the concrete owner and both frequency
tails; it needs its own node/cancellation and full-line coverage certificate.
The old triangle derivative-mass route remains rejected by record 2722B.

The module is analytic and must audit with exactly
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`. It does not
claim a producer result, poweredSeed carrier completion, universal rho duties,
selected Weil positivity or RH.

Verification completed on Linux ext4: build footer `Build completed
successfully (4028 jobs)`, no error lines, no `sorryAx`, and all four audited
declarations use only the standard trio. The reproducible checker is
`scripts/powered_seed_d4_d7_adapter_audit_3104.py`; its portable result is
`results/3104_powered_seed_d4_d7_adapter_audit.json`.
