# 1901 - Finite index pinning and frozen visible prime domain

Date: 2026-09-23.

Status: Formally verified in Lean; standard axioms `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

## Summary

This record completes Step 1 of the phase-balanced finite-orbit mainline by anchoring the orbit index to an explicit minimal integer $n_0$ and freezing the visible-prime summation domain.

1. **Existence of admissible index**:
   `exists_nat_quadratic_tail_lt_one` proves that for any real constant $C$, there exists a natural number $n$ such that:
   ```text
   (6 * pi)^2 * ((1 / 2)^(n + 1) * C) < 1.
   ```
   For $C \le 0$, $n = 0$ suffices; for $C > 0$, convergence of $(1/2)^n \to 0$ supplies the eventual bound.

2. **Minimal index definition and specification**:
   `minimalTailOrbitIndex C` selects the least such natural number via `Nat.find`, and `minimalTailOrbitIndex_spec` certifies that it satisfies the tail inequality.

3. **Direct package construction**:
   `rawOrbitG8GeometryOfIndexedConstruction` directly instantiates `OrbitG8Geometry rho g` from indexed raw components, ensuring `geometry.orbitIndex = orbitIndex` holds definitionally.

4. **Master pinned theorem**:
   `exists_pinnedOrbitG8Geometry_of_sourceNontrivialZero_right` combines the indexed assembly with the minimal index $n_0 = \text{minimalTailOrbitIndex}(C)$, exporting for every right off-line zero $\rho$:
   - Minimal index $n_0$;
   - Test $g$ and geometry `OrbitG8Geometry rho g` with `geometry.orbitIndex = n0`;
   - Strict health: `HealthyYoshidaDetectorData rho.1 g`;
   - Explicit support: `support g.test ⊆ Set.Ioo (-(n0 + 2)) (n0 + 2)`;
   - Prime cutoff: $\forall q \in \text{globalPrimeIndexSet}, q < \exp(2(n_0 + 2))$;
   - Discrete sum identity:
     ```text
     finitePrimeSum g.convolutionSquare =
       ∑ n ∈ Finset.range (Nat.ceil (exp(2 * (n0 + 2))) + 1),
         finitePrimeTerm g.convolutionSquare n.
     ```

## Verification

WSL focused build `build-logs/1901_pinned_geometry.log` compiles `ConnesWeilRH.Dev.C1G8R0OrbitGeometry` and `ConnesWeilRH.Dev.C1G8R0OrbitGeometryAudit` with zero `error:` lines, zero `sorryAx`, and only the three standard axioms `[propext, Classical.choice, Quot.sound]`.

This closes Step 1. The remaining obligation is Step 2: two-span sign balancing on this frozen finite-prime domain.
