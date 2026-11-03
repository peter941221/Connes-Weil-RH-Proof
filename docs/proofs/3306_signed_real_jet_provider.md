# Record 3306: signed real jet provider

Status: formal provider complete; the 160 block inequalities and the sixth
derivative norm provider remain open.

The 3304 no-go showed that the existing 3224 rows are too weak for the 3302
directed block manifest because they sum absolute values family by family. The
3306 provider changes the row semantics at the correct boundary:

```text
actual real derivative
        |
        v
real(center jet sum + coefficient-error jet sum)
        |
        +--> center: keep signed family cancellation
        |
        +--> error: use triangle inequality and scalar error budget
        v
real(center jet sum) + sum(error_i * norm(unit jet_i))
```

The main theorem is
`weightedExternal3306_real_jet_le` in
`ConnesWeilRH/Dev/C1RouteASignedRealJetProvider3306.lean`. For coefficient
centers `centers`, coefficient errors `errors`, and unit family jets
`weightedUnitJet2539`, it proves the real derivative upper bound

```text
iteratedDeriv order (weightedExternal3201 sigma coefficients modulations) position
  <= signedRealJetUpper3306 order sigma centers errors modulations position
```

The proof uses the existing owner identity
`weightedExternal3201_eq_weightedPhysical2539_re`, the derivative projection
lemma `iteratedDeriv_re_eq_re_iteratedDeriv3220`, and the exact signed family
decomposition `weightedPhysical2539_iteratedDeriv`.

For the selected record 2680 owner, the concrete rows are
`record2680SignedRealSecondUpper3306` and
`record2680SignedRealFourthUpper3306`. Their audited bounds are
`record2680_signed_real_second_bound3306` and
`record2680_signed_real_fourth_bound3306`. These instances use the exact
owner coefficients as centers and the zero error function, so no model gate or
external coefficient payload is transferred.

The provider is deliberately limited to real second- and fourth-order rows.
The 3305 consumer still needs a sixth-order bound in complex norm, plus the 160
explicit inequalities comparing each signed cell block with the 3302 directed
manifest. The corrected real row is materially sharper than an absolute-value
row because a negative center derivative remains negative in the upper bound.

Verification evidence:

```text
WSL workspace: Linux-native ext4 verification copy
toolchain:     leanprover/lean4:v4.30.0
Lean:          4.30.0
provider:      lake build ConnesWeilRH.Dev.C1RouteASignedRealJetProvider3306
audit:         lake build ConnesWeilRH.Dev.C1RouteASignedRealJetProvider3306Audit
axioms:        [propext, Classical.choice, Quot.sound]
```

Logs are stored in
`results/3306_signed_real_jet_provider_lake_build.log` and
`results/3306_signed_real_jet_provider_audit_build.log`.
