# 2131 — C3' diagonal signs do not imply the directed cross sign

Date: 2026-09-28.

Status: SCOPED-NO-GO-FOR-DIAGONAL-SIGNS-IMPLYING-CROSS-SIGN. This closes an
algebraic shortcut only. It is not a no-go for the actual zeta owner, and it
is not a producer theorem or an RH result.

Consumer and exact obligation:

```text
CarrierTwoSpanSignCertificate
  diagonal_signs
  directed_cross_nonneg
      -> CarrierTwoSpanDeterminantCertificate
      -> orbitWindowSemiLocalGate
      -> same-owner qw >= 0
      -> SourceRH
```

The tested shortcut was: opposite signs on the two Archimedean diagonal
terms and the two prime diagonal terms might force

```text
carrierPairArchimedeanTermPhase * carrierPairPrimePhaseSum >= 0.
```

That implication is false on the registered two-span pricing family.

Result from `results/1798_twospan_cross_gate.json`:

```text
pair                                  orientation   Arch cross       prime cross       product
head_bump0.9 x ref_D3_root            v,u            +1.158199e-3      -1.160089e-3      -1.343614e-6
head_bump1.8 x ref_D3_root            v,u            +3.269253e-4      -5.677580e-4      -1.856144e-7
```

Both rows satisfy the opposite diagonal sign predicate in the `v,u`
orientation, but both fail `directed_cross_nonneg`. The independent screen
reports two counterexamples out of eight rows in
`results/2131_routea_c3p_cross_sign_screen.json`.

Decision:

- Do not add a Lean theorem deriving `directed_cross_nonneg` from
  `diagonal_signs`.
- Do not replace the aggregate signed certificate with channelwise signs.
- The live Route-A obligation remains an actual-owner cross certificate or a
  different aggregate physical-kernel inequality with a named margin.
- This result does not transfer from the registered family to every formal
  owner and does not close Route A globally.

Reproduce:

```text
python scripts/twospan_cross_gate_1798.py
python scripts/routea_c3p_cross_sign_screen_2131.py
```

Artifacts:

- `results/1798_twospan_cross_gate.json`
- `results/2131_routea_c3p_cross_sign_screen.json`
