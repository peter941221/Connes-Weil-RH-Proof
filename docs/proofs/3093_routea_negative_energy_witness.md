# 3093 - actual local negative-energy witness

Record 3093 closes the local screen. Its final theorem takes only the actual
`OrbitG8Geometry rho g`; every analytic and sign input is proved:

```text
exists_nonzero_frequency_negative_energy_witness geometry
  -> exists xi != 0,
       routeAJointSymbol geometry xi < 0
       and routeAOrbitTransform geometry xi != 0
       and routeAFrequencyEnergyDensity geometry xi < 0
```

The dependency chain is:

```text
3090: c3Sigma(0) > 0 ----> 3089: jointSymbol(0) < 0
                                     |
3091: continuity --------------------> 3088: negative ball
                                                |
3092: analytic + global nonzero ----> 3087: nonzero point
                                                |
                                                v
                                      3093: negative density
```

`not_routeAFrequencyEnergyDensity_pointwise_nonneg` is the explicit scoped
no-go: the joint-symbol density cannot be a pointwise nonnegative producer.
Record 3094 proves that inserting the positive Fourier normalization factor
`1/(2*pi)` leaves a negative density point.

The audit also proves the required boundary checks. An empty prime sum still
leaves a strict zero-frequency symbol margin. For an off-line geometry, the
transform and energy at zero are exactly zero, so the negative symbol there
alone supplies no witness. Finally, a transform vanishing on a witness's
entire ball contradicts the witness's nonzero-transform field directly.

This is a falsification of pointwise nonnegative-square production. It is not
a proof that `qw < 0`, and it does not prove RH.

Reproduction: `python3 scripts/routea_local_screen_audit_3094.py` in the Linux
verification environment. The machine-independent audit result is
`results/3094_routea_local_screen_audit.json`.
