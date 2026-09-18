# 1624 — The B4 certificate and the carrier base are one Toeplitz condition

Date: 2026-09-18.

Status: route record (reduction + unification). Paper-level; the H² dictionary
used here is NOT formalized in the tree. B4 and the carrier base both stay
OPEN. RH is not claimed.

Consumer (named): the healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)); B4 is the WO-B
internal-gap leg, the carrier is the base of both WO legs, of map
[042](../map/042_g8_diagonal_leg_operator_bridge_audit.md).

## 1. What is being compared

B4's producer premise, committed shape
([1612](1612_source_column_wide_support_bridge.md)/[1613](1613_fourier_gap_b4_consumer.md),
landed corollary in [1619](1619_strip_confinement_landed_signed_b4_target.md)):

```text
E_{lambda''} ∘L H ∘L M ∘L J = H ∘L M ∘L J,      lambda'' = lambda * exp(-s), s >= 0
```

i.e. for every source vector `x`: with `v := M (J x)`,

```text
supp (H v)  subset  [log lambda'', inf)            (a WIDE radial certificate).
```

The carrier base ([999](999_sonin_window_leaf_blocking.md) section 1,
`SoninWindowWitness.lean:44`):

```text
exists u != 0 : supp u subset [log lambda, inf)  AND  supp (H u) subset [log lambda, inf).
```

## 2. Both conditions in the conjugate frame

Inputs: `H = R ∘L U_m` (record [1622](1622_multiplier_conjugate_factorization_and_1621_erratum.md))
and the Paley–Wiener dictionary for the tree's Fourier transform `F`
(verified on `f(t) = e^{-t}1_{t>0}`, whose `Ff = 1/(1+2πiξ)` has its pole in
`ℂ₊`):

```text
supp w subset [c, inf)   <=>   xi |-> e^{2πi c xi} (F w)(xi)  in  H^2(C_-),
```

equivalently: the boundary function's positive-frequency part vanishes,
`P_+(e^{2πi c xi} F w) = 0`.

Applying this to `w = H v` and substituting the committed readback
`F (H v) = m . (R (F v))` (`CCM24HardyTitchmarsh.lean:340`, where `m` is
`ccm24ArchimedeanScatteringPhase`, `:104`):

```text
+----------------------+-----------------------------------------------------------------+
| condition            | conjugate-frame form                                            |
+----------------------+-----------------------------------------------------------------+
| B4 wide certificate  | P_+( e^{2πi c xi} . m . psi_v ) = 0,  c = log lambda'',         |
|                      | psi_v := R (F v)                                                |
| B4 sharp certificate | same with c = log lambda                                        |
| carrier condition    | P_+( e^{2πi c xi} . m . psi_u ) = 0,  c = log lambda,           |
|                      | psi_u := R (F u), PLUS supp u subset [log lambda, inf)          |
| 1003 T1-T4 target    | exists psi in H^+, psi != 0,  P_+(m . psi) = 0                  |
+----------------------+-----------------------------------------------------------------+
```

The three rows are the same operator equation on different vectors: the
threshold enters only through a unimodular modulation `e^{2πi c xi}`, which is
absorbed by translating the vector, with the sign fixed by
`R (F (u(· + c))) = e^{−2πi c xi}(R (F u))`.
Consequently the *sharp* and the *wide* certificates are the same H²
condition, and the carrier base is exactly record
[1003](1003_psp_inner_outer_attack_plan.md)'s Toeplitz-kernel statement
`ker(T_m) ≠ {0}` — the statement T1/T2 set up but never decided.

## 3. What this says about where the difficulty lives

The Toeplitz kernel can only be nonzero because `m` is not bounded in the
upper half-plane:

- `m` is unimodular on the line and analytic in `ℂ₊` with zeros at
  `+i(4n+1)/(4π)` and poles at `−i(4n+1)/(4π)` (the pole/zero ledger of record
  [1590](1590_carrier_base_obligation_is_a_de_branges_existence_and_1331_erratum.md)'s
  erratum on 1331 section 2.1).
- Stirling's formula on `m(z) = π^{2πiz} Γ(1/4 − πiz)/Γ(1/4 + πiz)` gives, on
  a horizontal line `z = x + iy`, `|m| ≍ (πx)^{2πy}` for `x → ∞`: polynomial
  growth with exponent `2πy → 0` as `y → 0⁺`, reproducing the weight
  `(1+|x|)^{2πη}` matched numerically in 1590.
- If `m` were bounded in `ℂ₊`, the product `m·psi` would stay in `H²(ℂ₊)`
  whenever `psi ∈ H²(ℂ₊)`, and `P_+(m psi) = 0` would force `m psi = 0`, hence
  `psi = 0`: the kernel would be trivial. The extreme case `m ≡ 1` is
  decidable by hand and agrees: then `H = R` (committed `F⁻¹ = R F`), and
  `V_arch = {u : supp u ⊆ [log λ,∞), supp u ⊆ (−∞,−log λ]} = {0}`.

So the carrier base is nonzero *only* through the multiplier's half-plane
growth; every bounded-multiplier model of it is empty.

## 4. Consequences and honest limits

- **Unification.** WO-B's producer premise and the carrier base are one and
  the same analytic object (`ker T_m`), not two independent obstructions. A
  solution of one is a solution shape for the other; from now on they should
  be tracked as one item with two consumers.
- **No free lunch.** The rewriting in section 2 is a rename unless one uses
  `m`'s ledger or growth (law F8). Nothing here proves or refutes
  `ker(T_m) ≠ {0}`, and nothing here estimates anything.
- **Not formalized.** The Paley–Wiener/H² dictionary is paper-level. The tree
  has the frequency-half projectors and their algebra
  (`CCM24PaleyWienerSpectral.lean`), but no analytic-continuation or
  `H²(ℂ_±)` layer, and Mathlib has none (record
  [1623](1623_t4_prolate_attack_four_obligations_and_two_mismatches.md) section 5).
- **Sharp versus wide.** Since the threshold is only a modulation, a "wide"
  certificate is not weaker than a sharp one at the H² level; the width
  `s` in the landed strip corollary (1619) enters the *geometry* of the
  remaining defect, not the H² membership.

## 5. Typed next step

The decisive cheap test is a scalar one, not a brick: for the committed
column vectors `v = M (J x)`, decide whether `P_+(e^{2πi c xi} m · R(F v))`
can vanish. A necessary condition is already visible from the ledger: the
product must vanish at the zeros of `m` in `ℂ₊` only in the `H^2(C_+)` sense
of section 3, so the column's transform must be *large* exactly where `m` is
large — a quantitative version of "the unboundedness is the freedom".
Formalization of even this test needs the `H²` layer first.

## 6. Boundaries

`StripDensity(Λ)`, `EndpointMass(ε)`, T1, (★), B4, ρ5, R4/(OB)/W1 and RH are
unchanged and open. No gap premise, `SourceRH`, or universal gate is
introduced.