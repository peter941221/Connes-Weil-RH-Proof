# Gate 3U 右腿能量底：`sourcePhysicalCoframeLeakage` 范数 = Proof 717 等价的非平凡目标

Date: 2026-08-04 · Status: blocked (analytic-bottom precisely located, one-step
reduction to Proof 717) · Owner lane: Gate-3U completed-readout

## Result

The direct adjoint completed-kernel route to the real Gate 3U
(`canonicalRealGate3UAt`, `CCM24FiniteSCanonicalRealGate.lean:62`) reduces to a
**single** missing inequality, and then to a **known** open target (Proof 717)
whose equivalent the repository already states.  This round converges the
Gate-3U "right-energy" analytic bottom to **one equality-equivalent object.**

## Chain of evidence (file:line)

1. **Gate 3U → single right-energy premise.** `canonicalRealGate3UAt_of_
   completedKernelRightEnergy` (`CCM24FiniteSCanonicalAdjointEnergyGate.lean:375`)
   needs only `hright : sourcePhysicalCoframeCompletedKernelRightEnergy ≤
   fixedPhysicalEnergyMajorant`.  Definition (:183-208):

   ```
   RightEnergy = Σ' ‖pair.right ∘L sourcePhysicalCoframeLeakage λ f (basis i)‖²
   ```

   `pair.right = sourceThreeBranchPairData.right` (HS, `l2Sum`), and each
   physical leakage branch right-composes the same `finiteEulerMetricCoframe`.

2. **HS precomp bounding.** `tsum_normSq_precomp_le` (`HilbertSchmidtIdeal.lean:88`):
   ```
   RightEnergy ≤ ‖sourcePhysicalCoframeLeakage‖² · (Σ' ‖data.right (globalBasis i)‖²)
   ```
   The right factor already has the fixed majorant
   (`sourceThreeBranchPairData_right_basisEnergy_le_fixedMajorant`,
   `CCM24FiniteSFixedPhysicalEnergyBound.lean:249`). So the **only new scale** is
   `‖sourcePhysicalCoframeLeakage‖`.

3. **The mixed scalar gap (module-confirmed).** `norm_schurMarkovMixedMetricCoframe_le_one`
   (`CCM24FiniteSSchurMarkovUniformBound.lean:118`) proves the *mixed* coframe
   (=`suffix ·  coframe`, `:83-87`, `suffix = ∏_p (1−c_p)/(1+c_p)`) is contraction.
   The module header (`:18-20`) says verbatim: *“This ... does not yield the
   additional Schur--Markov scalar on the right-hand side required by Gate  3U.”*
   That right-side scalar is `1/suffix = ∏_p (1+p^{-1/2})/(1−p^{-1/2})` (since
   `ccm24PrimeEulerCoefficient p = 1/√p`, `CCM24EulerTransport.lean:33`).

4. **Biorthogonal obstruction (independent).** `sourceInclusionAdjoint_comp_
   metricCoframe` (`CoframeResponse.lean:53`) gives `J†∘D = id`, so
   `1 = ‖id‖ ≤ ‖J‖·‖D‖ ≤ 1·‖D‖`, hence `‖finiteEulerMetricCoframe‖ ≥ 1`. The
   un-scaled metric coframe is never a contraction.

5. **The exact norm gate is Proof 717-equivalent.** `CCM24FiniteSEndpoint
   ContractionGuard.lean:245-252`:
   ```
   norm_sourceActualBandForwardEndpointCoframe_le_one_iff_forward_add_physicalLeakage_eq_zero
   ‖combined endpoint‖ ≤ 1  ↔  sourceActualBandForwardCoframe + sourcePhysicalCoframeLeakage = 0
   ```
   So `‖sourcePhysicalCoframeLeakage‖ ≤ 1` is **not** an isolated provable fact;
   it is exactly the forward+physical cancellation that is the open Proof 717
   target.

## Judgment

- **Blocked (analytic bottom), not a signature rewrite.** The adjoint–precomp
  (HS) machinery provably cannot yield `‖physical leakage‖ ≤ 1` by itself:
  `boundedPrecomp`'s `tsum_normSq_precomp_le` needs it as an *input*, and
  biorthogonality forces `‖D‖ ≥ 1` unless the leakage vanishes.
- **The only closures are** (a) Proof 717's forward+physical cancellation making
  the *combined* endpoint a contraction, or (b) a genuinely new
  band-limited/operator estimate. Both are new analytic work, not a Lean
  re-assembly.

## Handoff fields

- RH status: conditional (Gate 3U open).
- Files read: `CCM24FiniteSCanonicalAdjointEnergyGate`, `CCM24FiniteSSchurMarkovUniformBound`,
  `CCM24FiniteSEndpointContractionGuard`, `CCM24FiniteSSchurMarkovPairing`, `CoframeResponse`,
  `CCM24EulerTransport`, `HilbertSchmidtIdeal`.
- Declarations: none changed in Source.
- Active root removed/lowered: no (remains Gate 3U right-energy ≤ majorant;
  now identified = Proof 717 cancellation up to the finite `1/suffix` factor).
- Old weak path inactive: the bare support+tail assembly of
  `CCM24FiniteSCausalMarkovRawRenewalTailBound` is a side branch; the direct
  adjoint closure dominates (AGENTS §2 updates Gate 3 queue).
- Build / audit: not run this round (no Lean change); MEMORY + AGENTS updated.
- Remaining bottom: `‖sourcePhysicalCoframeLeakage‖ ≤ 1` ⇔ Proof 717
  forward+physical cancellation.
- Next safe action: assemble/set a Proof-717-aware producer, or green a
  band-limited estimate for the leakage leg (new math).