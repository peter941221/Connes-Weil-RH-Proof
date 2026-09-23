# 090 — Finite index pinning and frozen visible prime domain

Date: 2026-09-23.

Status: Active binding route record; formal closure of Step 1.
Upstream: [087](087_support_overlap_harmonic_chebyshev_route.md), [089](089_base_contraction_zero_target_no_go.md), Record 1901.

## 1. Context & Route Progression

Following the formal scoped no-go in [089] refuting geometric base contraction $2 \cdot \text{seminorm}(base) < 1$, the project ceased attempts to send $n \to \infty$.

Instead, the mainline pivots to the **phase-balanced finite-orbit route**:
1. In `C1G8R0OrbitGeometry.lean`, any integer $n$ satisfying $(6\pi)^2 (1/2)^{n+1} C < 1$ produces a legitimate, healthy `OrbitG8Geometry`.
2. By selecting the minimal such index $n_0 = \text{minimalTailOrbitIndex}(C)$, the geometry is anchored at a fixed finite index.
3. The support radius is permanently frozen at $L = n_0 + 2$.
4. The arithmetic prime sum is permanently frozen as a finite summation over `Finset.range (Nat.ceil (exp(2 * (n0 + 2))) + 1)`.

## 2. Formal Result

Theorem `exists_pinnedOrbitG8Geometry_of_sourceNontrivialZero_right` now formally establishes:
For every hypothetical right off-line zero $\rho$ ($\mathrm{Re}(\rho) > 1/2$), there exist $n_0$, $g$, and $\text{geometry} : \text{OrbitG8Geometry } \rho\ g$ such that:
- $\text{geometry.orbitIndex} = n_0$;
- $\text{HealthyYoshidaDetectorData } \rho.1\ g$ holds;
- $\text{support } g.\text{test} \subseteq (- (n_0 + 2), n_0 + 2)$;
- $\forall q \in \text{globalPrimeIndexSet}, q < \exp(2(n_0 + 2))$;
- `finitePrimeSum g.convolutionSquare = ∑ n ∈ Finset.range (Nat.ceil (exp(2 * (n0 + 2))) + 1), finitePrimeTerm g.convolutionSquare n`.

Evidence: `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean` and `ConnesWeilRH/Dev/C1G8R0OrbitGeometryAudit.lean`. All declarations checked with standard axioms `[propext, Classical.choice, Quot.sound]` and zero `sorryAx`.

## 3. Next Action: Step 2 (Two-Span Sign Balancing)

With the prime domain frozen to a finite range, the gate obligation:
```text
archimedeanTerm g.convolutionSquare + finitePrimeSum g.convolutionSquare <= 0
```
is no longer an asymptotic limit problem. The live producer target is now Step 2: injecting negative gate energy through the two-span discriminant certificate `CarrierTwoSpanSignCertificate` ([080]) on this exact frozen owner.
