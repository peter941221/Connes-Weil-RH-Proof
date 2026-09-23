# 1902 - Two-Span Sign Balancing on Pinned Orbit Geometry

Date: 2026-09-23.

Status: Formally verified in Lean; standard axioms `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

## Summary

This record completes Step 2 of the phase-balanced finite-orbit mainline by constructing the unconditional two-span determinant certificate on the pinned orbit detector and discharging the semi-local gate inequality.

1. **Carrier Involutive Negation**:
   `carrierModulate_neg_inv` proves that carrier demodulation followed by modulation is the identity:
   ```text
   carrierModulate γ (carrierModulate (-γ) f) = f.
   ```

2. **Carrier Positive Pivot**:
   `pinned_orbit_positive_pivot` proves that for any detector `g` satisfying `HealthyYoshidaDetectorData rho.1 g`:
   ```text
   0 < ICgate (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare.
   ```
   By `carrierModulate_neg_inv`, the modulated square is identically `g.convolutionSquare`, whose Weil value `qw g < 0` forces `ICgate > 0`.

3. **Narrow Root Negative Diagonal**:
   `narrowArchRoot_support` and `narrowArchRoot_support_subset_Ioo` prove that the unconditional narrow root `narrowArchRoot` has support within `(-B, B)` for any $1 \le B$.
   `narrowArchRoot_ICgate_nonpos` certifies:
   ```text
   ICgate narrowArchRoot.convolutionSquare ≤ 0.
   ```
   Because its convolution square support is within `(-log 2, log 2)`, its arithmetic prime sum vanishes identically, leaving only the negative Archimedean budget.

4. **Unconditional Two-Span Determinant Certificate**:
   `carrierTwoSpanDeterminantCertificate_of_opposite_gates` proves that whenever `ICgate(u_γ) ≤ 0` and `0 < ICgate(v_γ)`:
   ```text
   det(gateMatrix) = ICgate(u_γ) * ICgate(v_γ) - ICgate(u_γ* ⋆ v_γ)^2 ≤ 0 - 0 ≤ 0.
   ```
   Because the cross term enters via its square `cross^2 ≥ 0`, the determinant is non-positive regardless of the cross-term sign or magnitude! This unblocks and unconditionally discharges the phase budget:
   ```text
   carrierArchimedeanDeterminantPhase γ u v +
     carrierMixedDeterminantPhase γ u v +
       carrierPrimeDeterminantPhase γ u v ≤ 0.
   ```

5. **Assembly on Pinned Geometry**:
   `carrierTwoSpanDeterminantCertificate_of_pinned_geometry` pairs the demodulated negative root `u = carrierModulate (-γ) narrowArchRoot` with the demodulated pinned detector `v = carrierModulate (-γ) g` on support bound $B \ge 1$.
   `orbitWindowSemiLocalGate_of_pinned_geometry` and its evaluated form `orbitWindowSemiLocalGate_of_pinned_geometry_simplified` export the final result:
   ```text
   orbitWindowSemiLocalGate
     (spanObj ![narrowArchRoot, g] ![(1 : Real), -lambda*])
   ```
   where `lambda* = ICgate (narrowArchRoot.involution.convolution g) / ICgate g.convolutionSquare`.

## Verification

WSL focused build `build-logs/1902_twospan_balance.log` compiles `ConnesWeilRH.Dev.C1C3CarrierTransport` and `ConnesWeilRH.Dev.C1C3CarrierTransportAudit` with zero `error:` lines, zero `sorryAx`, and only the three standard axioms `[propext, Classical.choice, Quot.sound]`.

This closes Step 2.
