# 1625 — S3 form selection among the five equivalent forms; the StripDensity fork closes at `Λ`

Date: 2026-09-18.

Status: route record + one paper-level closure of a premise (not a Lean brick;
the brick is specified in section 4). S3, WO-S, WO-B stay OPEN. RH is not
claimed.

Consumer (named): the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)); S3 is the sole
WO-S survivor obligation, `StripDensity` is its residual pricing object, of
map [042](../map/042_g8_diagonal_leg_operator_bridge_audit.md).

## 1. The five forms, and which one to attack

Record [1620](1620_s3_reduction_layer_complete.md) proved the five shapes
equivalent (`C1G8R3GateAmbientNormalForm.lean`, links 1–5). Selection is a
decision about *attack surface*, not about content:

```text
+---+------------------------------+----------------------------+---------------------+
| # | form                         | what binds it              | verdict             |
+---+------------------------------+----------------------------+---------------------+
| i | P ∘L C ∘L P  (ambient)       | ambient non-HS obstruction | dead shortcut       |
|   |                              | (1512, 1614)               | (kept as statement) |
| ii| J† ∘L C ∘L J (source gate)   | needs a named source basis | keep as readback    |
| iii| C ∘L J      (input energy)  | no compression => no       | weakest: hides P    |
|   |                              | carrier geometry           |                     |
| iv| E ∘L Q ∘L E ∘L C ∘L J        | prolate remainder split    | superseded by v     |
|   | (Hardy-compressed)           | (1616: remainder HS)       |                     |
| v | P ∘L C ∘L J  (source proj.)  | the carrier projection P   | CHOSEN              |
+---+------------------------------+----------------------------+---------------------+
```

Reasons for form v:

- Records [1616](1616_exact_prolate_split_b4_basis.md)/[1617](1617_source_compressed_root_kernel_one_sided.md)
  already removed the second Hardy corner exactly
  (`J† C J = J† (E Q E) C J − J† R C J`, prolate term controlled), so v carries
  strictly less machinery than iv.
- v is the only form in which the estimate is *visibly* an energy of the
  carrier: `Σ_i ‖P (C J e_i)‖²` restricts the detector output to the Sonin
  space, which is exactly the geometry pinned by
  [1584](1584_wave_v_cont8_carrier_defect_erratum.md)–[1586](1586_residual_reduction_two_exact_bounds_and_angle_gap_interface.md).
- By record [1624](1624_b4_certificate_and_carrier_are_one_toeplitz_condition.md),
  the carrier is the `ker T_m` object; choosing v puts the S3 estimate on the
  same analytic object as the carrier base and the B4 certificate, so the
  three open items become three readings of one Toeplitz condition rather than
  three separate analytic problems.

**Selection: form v.** The next S3 work should be stated as a square-sum for
`P ∘L C ∘L J`, and any brick that rewrites between i–iv is a rename (law F8).

## 2. The StripDensity fork closes

[1589](1589_sonin_carrier_structure_and_strip_density_verdict.md) section 6
re-typed StripDensity as the local trace
`StripDensity(Λ) = Tr(P M_Δ P)`, `Δ = [log λ, log λ + Λ)`, and filed its
*finiteness* as a new obligation with a three-way fork (zero / Poisson-finite
/ `+∞`). Two committed facts close the fork:

```text
P  <=  E                 (1588: source Sonin projection below radial projection)
S := supp E = [log λ, inf)          (committed radial subspace, one-sided)
E  =  multiplication by 1_S   (`radialSupportProjection_coeFn_indicator`,
                               C1G8P1HeadWindowEnergyLowerBound.lean:81)
Δ  subset of the strip, volume(Δ) = Λ
```

Claim (paper-level): `Tr(P M_Δ P) <= Λ∩ = volume(Δ ∩ S) <= Λ`.

Proof, five lines. Since `P ≤ E` and both are orthogonal projections,
`P = P E P`, hence

```text
P M_Δ P = P (E M_Δ E) P        (sandwich at the E level)
0 <= E M_Δ E                   (M_Δ an orthogonal projection)
0 <= P (E M_Δ E) P <= E M_Δ E  (0 <= P <= 1, positive sandwich)
```

Taking traces: `Tr(P M_Δ P) <= Tr(E M_Δ E) = Tr(M_Δ E M_Δ)`
(cyclicity for positive operators) `= Tr(M_{Δ ∩ S}) = volume(Δ ∩ S) <= Λ`.

The earlier infinite-trace scare (`Tr(M_Δ) = +∞`) is avoided because the
comparison is made at the level of `E`, and `E` is a *multiplication*
projection, whose composition with `Δ` has finite measure.

Consequences:

- The finiteness obligation of 1589 section 6 is discharged; the fork lands in
  the "finite" branch with the trivial constant `Λ`, and no Poisson-type
  computation is needed.
- This supersedes the status (not the content) of the 1589 line "finiteness a
  NEW obligation".
- The bound is *not* an estimate: `Λ` does not decay, and `Λ → 0` is not
  available. It prices the strip term in 1586's residual identity
  `residual² = StripDensity(Λ) + Σ_i dist(h_i, carrier)²` at at most the strip
  length, i.e. the surviving content stays where 1586 put it.
- Nothing here distinguishes zero from positive density: the bound is an upper
  bound only.

## 3. What this does not do

`StripDensity(Λ) <= Λ` is law-F29-compatible support geometry: it is
positivity of projections plus the measure of a multiplication projection. It
supplies no singular-value content for `P ∘L C ∘L J`, and the S3 square-sum
remains open in form v.

## 4. The Lean brick, specified (not written)

Statement to formalize:

```text
for closed subspaces with orthogonal projections P <= E of L2(volume),
E a multiplication projection 1_S, and Δ of finite measure,
  ordinaryTraceAlong b (P M_Δ P) <= volume (Δ ∩ S),   for any Hilbert basis b.
```

Irreducible ingredients:

1. the committed `P ≤ E` comparison (1588) and `P = P E P`;
2. positive sandwich monotonicity `0 ≤ A ≤ B -> Tr A ≤ Tr B` for
   `ordinaryTraceAlong` (`PositiveTrace.lean` has the trace API at
   `:32/:186/:628`, but not this monotonicity lemma);
3. the steps `E M_Δ E = M_{Δ ∩ S}` (elementary once the committed indicator
   readback is rewritten) and the basis-to-measure identity
   `Σ_i ⟨b_i, M_f b_i⟩ = ∫ f` — **the missing piece** is the second one: the
   tree's traces run along an abstract `HilbertBasis` and nothing yet ties a
   basis to the Lebesgue measure.

Item 3 is why this is not a one-session brick; it is the *same* missing layer
that record 1624 section 4 flags (the tree has no measure-theoretic H²/kernel
layer relating bases to integrals).

## 5. Boundaries

S3, WO-S, WO-B, `EndpointMass(ε)`, T1, (★), B4, ρ5, R4/(OB)/W1 and RH are
unchanged and open. No gap premise, `SourceRH`, or universal gate is
introduced.