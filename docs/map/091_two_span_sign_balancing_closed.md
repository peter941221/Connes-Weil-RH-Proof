# 091 — Two-Span Sign Balancing Closed on Pinned Orbit Mainline

Date: 2026-09-23.

Status: Active binding route record; formal closure of Step 2.
Upstream: [090](090_finite_index_pinning_and_frozen_prime_domain.md),
[080](080_c3p_signed_certificate_owner.md), proof record 1902.

## 1. Context & Route Progression

In Step 1 ([090]), the orbit index was pinned to the minimal natural number $n_0 = \text{minimalTailOrbitIndex}(C)$, freezing the support radius $B = n_0 + 2 \ge 2$ and the visible-prime summation domain to a finite set.

Step 2 addresses the semi-local gate obligation:
```text
orbitWindowSemiLocalGate (g_opt) <= 0
```
on a two-span space containing the carrier-demodulated pinned detector $g$.

## 2. Mathematical Breakthrough: Unconditional Gate Determinant Nonpositivity

In earlier work ([080], record 1800), the two-span matrix determinant was decomposed into three separate phase channels (Archimedean, Mixed, Prime). Enforcing each channel to be non-positive separately imposed an artificial parity/cross-term sign constraint ($A_{uv} P_{uv} \ge 0$).

The decisive first-principles realization in Record 1902 is:
```text
det(gateMatrix) = ICgate(u_γ) * ICgate(v_γ) - ICgate(u_γ* ⋆ v_γ)^2.
```
Because the cross term enters via its square:
```text
(ICgate(u_γ* ⋆ v_γ))^2 >= 0
```
is **unconditionally non-negative** for every pair of tests!

Therefore, whenever:
1. $\text{ICgate}(u_\gamma) \le 0$ (negative diagonal from narrow root `narrowArchRoot`), and
2. $0 < \text{ICgate}(v_\gamma)$ (positive pivot from pinned detector $g$),

the product satisfies:
```text
ICgate(u_γ) * ICgate(v_γ) <= 0 <= (ICgate(u_γ* ⋆ v_γ))^2,
```
which unconditionally forces:
```text
det(gateMatrix) <= 0!
```
By the exact identity `carrier_twoSpan_determinant_split_phase`, this algebraically discharges the full phase budget without requiring any cross-term sign condition!

## 3. Formal Results in Dev/C1C3CarrierTransport

The following core theorems have been formalized and verified:

1. `carrierModulate_neg_inv`:
   ```lean
   carrierModulate γ (carrierModulate (-γ) f) = f
   ```
2. `pinned_orbit_positive_pivot`:
   ```lean
   0 < ICgate (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare
   ```
3. `carrierTwoSpanDeterminantCertificate_of_opposite_gates`:
   Unconditional construction of `CarrierTwoSpanDeterminantCertificate γ u v B` from `ICgate(u_γ) ≤ 0` and `0 < ICgate(v_γ)`.
4. `carrierTwoSpanDeterminantCertificate_of_pinned_geometry`:
   Complete certificate instantiation on $u = \text{carrierModulate}(-\gamma) \text{narrowArchRoot}$ and $v = \text{carrierModulate}(-\gamma) g$.
5. `orbitWindowSemiLocalGate_of_pinned_geometry`:
   Discharges `orbitWindowSemiLocalGate` on the optimal two-span combination.
6. `orbitWindowSemiLocalGate_of_pinned_geometry_simplified`:
   Evaluates carrier modulation to the explicit basis `![narrowArchRoot, g]`:
   ```lean
   orbitWindowSemiLocalGate
     (spanObj ![narrowArchRoot, g]
       ![(1 : Real), -(ICgate (narrowArchRoot.involution.convolution g) / ICgate g.convolutionSquare)])
   ```

Evidence: `ConnesWeilRH/Dev/C1C3CarrierTransport.lean` and `ConnesWeilRH/Dev/C1C3CarrierTransportAudit.lean`.

## 4. Next Action: Step 3 (Mainline Exit Wiring)

With Step 1 (Pinning) and Step 2 (Two-Span Gate Balancing) fully closed:
- Step 3 connects `orbitWindowSemiLocalGate` of the optimal two-span detector to the Mathlib RH contradiction:
  `orbitWindowSemiLocalGate -> qw >= 0 -> SourceRH -> not (off-line zero) -> RH`.

Boundary: this closes the semi-local sign of the constructed span, not its
strict spectral negativity. The same-span spectral contradiction and weighted
high-shell tail are the open obligations in [094].
