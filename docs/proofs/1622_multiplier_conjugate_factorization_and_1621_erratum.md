# 1622 — The Hardy–Titchmarsh involution is a reflection of a multiplier conjugate; erratum on 1621

Date: 2026-09-18.

Status: formal, accepted. No existence statement, no estimate. RH is not
claimed.

Consumer (named): the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)); the carrier is
the base of the WO-S/WO-B legs of map
[042](../map/042_g8_diagonal_leg_operator_bridge_audit.md).

## 1. Erratum on record 1621

[1621](1621_carrier_eigenvector_bridge_and_t4_route.md) recorded the
half-phase computation `U H U⁻¹ = R` for `U = F⁻¹ M_{m^{−1/2}} F` as a paper
calculation and stated that the Fourier–reflection covariance was "not yet a
committed lemma in this tree". Both statements are withdrawn:

| 1621 said | Committed reality |
| :-- | :-- |
| covariance not committed | `ccm24_fourierInv_eq_reflection_fourier` (`CCM24ArchimedeanCarrier.lean:863`), `ccm24_fourier_reflection_eq_fourierInv` (`:904`) |
| a half-phase square root `m^{1/2}` is needed | not needed: the factorization below is free, and no square root of the phase is constructed |

The phase-square-root route was a detour: it is not the cheapest reading of
`H`, and the tree already had the covariance that removes the reflection from
the middle of `H`.

## 2. The factorization

Committed inputs, quoted:

```text
H      := F⁻¹ ∘L M_m ∘L R ∘L F              (CCM24HardyTitchmarsh.lean:331)
F⁻¹    =  R ∘L F                            (CCM24ArchimedeanCarrier.lean:863)
```

Substituting the covariance and writing `U_m := F ∘L M_m ∘L F⁻¹`:

```text
H = F⁻¹ ∘L M_m ∘L R ∘L F = F⁻¹ ∘L M_m ∘L F⁻¹ = R ∘L (F ∘L M_m ∘L F⁻¹) = R ∘L U_m .
```

`U_m` is the scattering multiplier transported to the logarithmic domain. It
is the *same* shape as `H` with the reflection removed; no square root, no
new analytic object.

## 3. Landed declarations

`ConnesWeilRH/Dev/SoninCarrierMultiplierConjugate.lean` with audit twin, ten
declarations, no `sorry`, standard axioms only:

| Declaration | Content |
| :-- | :-- |
| `ccm24LogSpectralReflection_apply_involutive` | involution law for the reflection *equivalence* (the committed law is stated for the underlying isometry) |
| `archimedeanMultiplierConjugate` | `U_m = F ∘L M_m ∘L F⁻¹` |
| `archimedeanMultiplierConjugate_apply` | pointwise form of `U_m` |
| `ccm24ArchimedeanHardyTitchmarsh_apply_eq_reflection_multiplierConjugate` | `H u = R (U_m u)` |
| `ccm24ArchimedeanHardyTitchmarsh_eq_multiplierConjugate_trans_reflection` | operator form `H = R ∘L U_m` |
| `archimedeanMultiplierConjugate_eq_reflection_apply` | `U_m u = R (H u)` |
| `hardyTitchmarsh_fixed_iff` | `H u = u ↔ U_m u = R u` |
| `hardyTitchmarsh_antifixed_iff` | `H u = −u ↔ U_m u = −R u` |
| `mem_sonin_iff_radial_and_multiplierConjugate_mem_map` | carrier = radial ∩ `U_m`-preimage of the reflected radial subspace |
| `archimedeanSoninCarrier_nontrivial_iff_multiplierConjugate_reflection` | 1621's bridge in closed form |

The last row replaces 1621's eigenvector condition "`H u = ±u`, `u` radial"
by "`U_m u = ±R u`, `u` radial": the eigenproblem is a self-reflection
condition under the transported multiplier, i.e. the Toeplitz/de Branges shape
of [1590](1590_carrier_base_obligation_is_a_de_branges_existence_and_1331_erratum.md).

## 4. Reading

```text
+--------------------------+-------------------------------------------------+
| object                   | condition                                       |
+--------------------------+-------------------------------------------------+
| carrier V_arch(λ)        | supp u ⊆ [log λ,∞)   and                        |
|                          | U_m u ∈ R(radial λ) = supp U_m u ⊆ (−∞,−log λ]  |
| fixed equation           | U_m u = R u                                     |
| anti-fixed equation      | U_m u = −R u                                    |
+--------------------------+-------------------------------------------------+
```

So the carrier's second condition is one-sided support of `U_m u` on the
*reflected* half-line — the shape already used by the B4 side
([1599](1599_b4_unbounded_reflected_tail_boundary.md)); record
[1624](1624_b4_certificate_and_carrier_are_one_toeplitz_condition.md) records
what that coincidence means analytically.

## 5. Boundaries

- No carrier element is produced; `archimedeanSoninCarrier_nontrivial` stays a
  definition, not a theorem (law F33). Records
  [1586](1586_residual_reduction_two_exact_bounds_and_angle_gap_interface.md)–[1589](1589_sonin_carrier_structure_and_strip_density_verdict.md)
  remain CONDITIONAL on it.
- No estimate, no gap premise, no `SourceRH`, no universal gate is introduced.
- `StripDensity(Λ)`, `EndpointMass(ε)`, T1, (★), B4, ρ5, R4/(OB)/W1 stay OPEN.

## 6. Acceptance

Build log:
`/home/peter/rh/build-logs/1622_multiplier_conjugate.log`.
`Build completed successfully (3322 jobs)`, zero `error:` lines, zero
`sorryAx`, ten axiom prints all resolving to
`[propext, Classical.choice, Quot.sound]`, no warning in the two new modules.