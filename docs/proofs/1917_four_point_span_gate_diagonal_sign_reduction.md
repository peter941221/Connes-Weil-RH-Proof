# 1917 — Four-point span gate: exact parabola and the single diagonal sign

Date: 2026-09-23.

Status: FORMAL algebraic reduction. The remaining Cut-2 obligation is one
strict scalar sign on the four-point annihilator. That sign, the joint
high-shell margin, and the RH contradiction remain open. This record is a
project derivation from the committed gate algebra, not an originality or RH
claim.

## Owner and result

New Lean leaf `ConnesWeilRH/Dev/C1FourPointSpanGateCertificate.lean` with paired
audit. On the committed owners `u = fullFunctionalEquationOrbitAnnihilator g
rho` and the selected detector `g`, and the committed span
`h(lam) = annihilatorDetectorSpanVector u g lam`, the module proves:

1. `annihilator_span_gate_eq_parabola`: for any `CompactLogTest` pair `u, g`
   with joint support in `Ioo (-B) B`,

   ```text
   ICgate ((annihilatorDetectorSpanVector u g lam).convolutionSquare)
     = ICgate u.convolutionSquare
       - lam * (ICgate (u.involution.convolution g)
                + ICgate (g.involution.convolution u))
       + lam ^ 2 * ICgate g.convolutionSquare.
   ```

   The proof is the legalless quadratic-form representation
   `gate_qform_span_free` specialized along the committed double-sum bridge
   `pair_gate_sum_eq_qform`; no new integrability hypothesis enters. The two
   cross terms are kept separately. The campaign ledger writes the middle
   coefficient as one `B` with factor `2`; that normalization is exactly the
   cross-term symmetry `ICgate (g.involution.convolution u) = ICgate
   (u.involution.convolution g)`, which this statement does not need and does
   not assume.

2. `exists_nonzero_lambda_quadratic_nonpos_iff`: with `C > 0` and
   `Q(lam) = D - lam * B + lam ^ 2 * C` where `B` is the cross-term sum, a
   nonzero coefficient with `Q(lam) <= 0` exists exactly when

   ```text
   D < 0  or  (D = 0 and B != 0)  or  (0 < D and B ^ 2 - 4 * C * D >= 0).
   ```

   In the campaign's single-cross-term normalization the third case is the
   ledger's determinant certificate `B != 0 and D * C - B ^ 2 <= 0` with
   `lam = B / C` (the parabola vertex); its `B != 0` side condition is
   automatic there, and it is genuinely needed only in the `D = 0` case.

3. `exists_pos_lambda_quadratic_nonpos` and `gatePlusRoot_pos_of_neg`: a
   strictly negative diagonal `D < 0` alone supplies a **strictly positive**
   coefficient. The witness is the closed-form plus root

   ```text
   gatePlusRoot D B C = (B + sqrt (B ^ 2 - 4 * C * D)) / (2 * C)
   ```

   with `Q (gatePlusRoot D B C) = 0` (`gate_quadratic_at_gatePlusRoot`). No
   nonvanishing or sign condition on either cross term is required, so the
   gate-selected coefficient of Cuts 1 and 3 is positive by construction.

4. Wires: `exists_pos_lambda_orbitWindowSemiLocalGate_of_annihilator_gate_neg`
   turns a healthy detector, the support inclusion, and the single strict sign
   `ICgate ((fullFunctionalEquationOrbitAnnihilator g rho).convolutionSquare) < 0`
   into `orbitWindowSemiLocalGate (annihilatorDetectorSpanVector u g lam)` at
   the same positive `lam`;
   `exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg` adds the
   committed finite-prefix bound
   `sum spectralTerm <= - xiMultiplicity rho * lam ^ 2` on the identical owner
   and the identical coefficient, via
   `finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport`.
   The strict positive pivot `C = ICgate g.convolutionSquare > 0` is the
   committed `pinned_orbit_positive_pivot` after carrier demodulation.

## Exact remaining obligation (Cut 2)

```text
ICgate ((fullFunctionalEquationOrbitAnnihilator g rho).convolutionSquare) < 0
```

for the selected healthy detector `g` and the hypothetical off-line zero
`rho`. Everything else in Cut 2 is formal. This is a single scalar inequality
on the gate of a test with the annihilator's full support, whose exact visible
prime set is inherited from `g`; the narrow-root prime-free support mechanism
of the 091 lane does not transfer and no estimate of this sign is claimed
here. In the opposite case `D >= 0` the trichotomy shows a gate witness exists
only through the `D = 0` degeneracy or the discriminant condition, so a
counterexample to the diagonal sign would not by itself kill the span route;
it would force the certificate onto the vertex root.

## Design remark: the gate-selected coefficient is pinned

The witness is not free: `lam = gatePlusRoot D B C` is determined by the three
gate values, and the committed bound (derived on paper, verified by the rig
below, not formalized) is

```text
gatePlusRoot D B C >= 2 * abs D / (sqrt (B ^ 2 - 4 * C * D) + abs B),
```

with equality exactly when `B <= 0` and strict gap `B * (B + sqrt (disc)) /
(2 * C * abs D)` when `B > 0`. So the Cut-1 quantifier coupling is now
concrete: the joint margin must be checked at this explicit `lam`, and a small
`abs D` forces a small witness.

## Verification

Focused commands:

```text
lake build ConnesWeilRH.Dev.C1FourPointSpanGateCertificate
lake build ConnesWeilRH.Dev.C1FourPointSpanGateCertificateAudit
```

The owning build completed successfully in 3808 jobs and the paired audit
build in 3809 jobs, each with zero `error:` lines and no warnings in either
new file. The audit prints exactly `[propext, Classical.choice, Quot.sound]`
for all seven public declarations, with no `sorryAx`.

Independent self-check rig (pure Python, standard library only):

```text
python3 scripts/fourpoint_span_gate_trichotomy_1917.py
```

Result: `checks=1753 failures=0` on adversarial anchors (zero cross term,
tangent discriminant, `D = 0`, magnitudes `1e-12 .. 1e12`), 400 random draws,
and 40 exact discriminant-zero draws. Engines: direct evaluation, closed-form
witnesses, grid search over `|lam|` in `[1e-6, 1e6]` compared against the
trichotomy predicate on the same draws, 50-digit `Decimal` re-evaluation, and
the sharp bound identity above. Conditioning note recorded as rig discipline:
the direct root form `(B + sqrt disc) / (2C)` cancels catastrophically for
`B < 0` and small `abs D`; the rig uses the rationalized `2 * D / (B - sqrt
disc)`, which is what turned 118 apparent failures into 0. The Lean statement
is unaffected — it does not evaluate the root numerically.

No gate sign, no joint high-shell margin, and no RH statement is proved.
RH NOT claimed.