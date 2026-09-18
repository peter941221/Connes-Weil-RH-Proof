# 1623 — T4 prolate attack: the four obligations, the tree's naming, and two mismatches

Date: 2026-09-18.

Status: route record (attack + recon). No new Lean beyond the 1621/1622
interface. T4 remains OPEN; the prolate route is NOT refuted and NOT
formalized. RH is not claimed.

Consumer (named, unchanged): the healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)); T4 is the
carrier-base producer of the WO-S/WO-B faces of map
[042](../map/042_g8_diagonal_leg_operator_bridge_audit.md).

## 1. The four obligations, typed

[1003](1003_psp_inner_outer_attack_plan.md) T4: "Construct a nonzero kernel
vector from a prolate/Sonin spectral problem — the implementation must prove
the domain, spectral sign, carrier transport, and window restriction. Each is
an independent theorem, not a stored scalar."

```text
+----+---------------------+------------------------------------+-----------------------+
| #  | obligation          | exact statement needed             | what it needs          |
+----+---------------------+------------------------------------+-----------------------+
| D  | domain              | the self-adjoint extension W_sa of | singular Sturm-        |
|    |                     | the prolate operator is a well-    | Liouville theory with  |
|    |                     | defined self-adjoint operator on a | two interior singular  |
|    |                     | dense domain in L2(R)              | points; deficiency     |
|    |                     |                                    | indices; extensions    |
| S  | spectral sign       | W_sa has a negative eigenvalue mu  | negative-eigenvalue    |
|    |                     | (with an eigenfunction phi_mu)     | counting for a class   |
|    |                     |                                    | of Sturm-Liouville     |
|    |                     |                                    | operators (Heywood)    |
| C  | carrier transport   | phi_mu lies in the tree's          | support/H2 continuation|
|    |                     | sourceSoninCarrier(lambda)         | of a specific function |
| W  | window restriction  | restriction of phi_mu to           | determining set /      |
|    |                     | W = (log lambda, lambda+log 2) is  | unique continuation    |
|    |                     | nonzero in L2(restrict W)          | (docs/999 section 2)   |
+----+---------------------+------------------------------------+-----------------------+
```

## 2. Source, quoted

Connes–Moscovici, "The UV prolate spectrum matches the zeros of zeta"
(PNAS 2022, [PMC9295779](https://pmc.ncbi.nlm.nih.gov/articles/PMC9295779/)):

```text
(W_lambda xi)(x) = d_x (p(x) d_x xi(x)) + q(x) xi(x),
    p(x) = x^2 - lambda^2,   q(x) = (2 pi lambda)^2 x^2
"But, having two interior singular points, it is not directly treatable
 by the usual Sturm-Liouville theory."

"Corollary 2.2. With the above notation, assume mu is a negative
 eigenvalue. Then phi_mu belongs to the Sonin space. The Sonin space
 coincides with the orthogonal complement of the eigenspaces of W_sa
 associated with the classical prolate functions and their Fourier
 transforms."

"Sonin's space corresponds to the conditions p^2 - lambda^2 >= 0 and
 q^2 - lambda^2 >= 0"   (semiclassical phase-space description)

"Proposition 3.2. The semiclassical approximation to the number of
 negative eigenvalues xi of W_sa with -xi <= E^2 on even functions is
 the same as on odd functions and is equal to 2 sigma(E, lambda) ..."
```

Two honesty notes on the source chain itself:

- The counting statement in the paper is labelled a **semiclassical
  approximation** (`sigma ≈ ... + o(1)`), i.e. the existence half of `S` is a
  soft link in the paper as written.
- The paper's *Dirac* side is harder: "A Liouville transformation shows that
  `W_sa'⁺` is unitarily equivalent to the Sturm–Liouville operator `S` on
  `(0,∞)`", after which a rigorous negative-eigenvalue counting formula
  (Heywood) is applied. If the prolate route is ever formalized, that
  Liouville-equivalence + Heywood pair is the rigorous entry point — and it is
  the expensive part.

## 3. Tree recon: "prolate" in this repository is a different object

A keyword sweep over `ConnesWeilRH/` returns 3318 occurrences of
`prolate|Prolate` across 333 files. They are the **finite-S strict-angle
band-crossing factors**, not the CCM prolate wave operator:

| Committed object | File | What it is |
| :-- | :-- | :-- |
| `supportComplementProjection` | `Source/CC20Concrete/ProlateTraceReduction.lean:34` | the support-complement projection |
| `prolateFactor` | `:38` | prolate factor of the two-projection layer |
| `prolateDefectFactor` | `:42` | the defect factor |
| `prolateFactor_summable_of_strictAngle` | `:212` | summability under a strict-angle premise |
| `prolateRemainder_isTraceClassAlong_of_strictAngle` | `:230` | trace-class remainder under the same premise |

No module in the tree defines the differential operator `W_lambda`, its
self-adjoint extension, or a prolate eigenvalue problem. docs/999 section 2's
repo-wide search conclusion ("finds NO example / witness member of any Sonin
space") was re-confirmed by this sweep.

## 4. Two mismatches between Corollary 2.2 and our obligation

### 4.1 One-sided versus two-sided

Committed carrier (docs/999 section 1; `CCM24LogRadialSupport.lean:30/48`,
`CCM24HardyTitchmarsh.lean:361/376`):

```text
V_arch(lambda) = Radial(lambda) INTER {u : H u in Radial(lambda)},
Radial(lambda) = {u : u = 0 a.e. on t < log lambda}      (a HALF-LINE)
```

CCM's Sonin space is the orthogonal complement of the prolate eigenspaces,
whose own semiclassical description in the paper is `p^2 - lambda^2 >= 0` and
`q^2 - lambda^2 >= 0`, i.e. the **two-sided** complement of an interval in
each variable. These are different support geometries. Corollary 2.2 therefore
does not assert membership in `V_arch(lambda)`, and the transport

```text
CCM Sonin space  ->  V_arch(lambda)
```

is a *separate* obligation, not a rename. The naive argument (cut the two
tails by an indicator) fails: an indicator cut does not preserve the
`H u ∈ Radial` condition, since applying `F` to a cut is a full-support
convolution. The parameter normalisation (multiplicative `lambda` versus the
additive `log lambda` of the tree) is likewise unformalized.

### 4.2 The whole difficulty is the multiplier, and one sanity check proves it

The `H²`/Paley–Wiener reading of the two support conditions (details in
[1624](1624_b4_certificate_and_carrier_are_one_toeplitz_condition.md)) gives:

```text
u in V_arch  <=>  supp u subset [log lambda, inf)  AND  P_+(m . psi) = 0,
                  where psi := R(F u) in H^2(C_+)
```

— the Toeplitz-kernel condition of record 1003 T4 itself. Setting `m ≡ 1` is
decidable by hand and gives `H = R` (from the committed `F⁻¹ = R F`:
`H = F⁻¹ R F = F⁻¹ F⁻¹ = R`), hence
`V_arch = {u : supp u ⊆ [log λ,∞), supp u ⊆ (−∞,−log λ]} = {0}` for
`log λ > 0`: **a bounded (H∞) multiplier forces an empty carrier**. The
tree's multiplier is not bounded in the upper half-plane — its horizontal-line
growth is `(1+|x|)^{2πy}` (the weight matched numerically in record
[1590](1590_carrier_base_obligation_is_a_de_branges_existence_and_1331_erratum.md),
law F34) — and that unboundedness is exactly the freedom the witness must
exploit. Consequence for T4: any prolate witness must be a *growing* object in
the conjugate frame; a witness built from bounded multipliers cannot exist.

## 5. Mathlib sweep

`find .lake/packages/mathlib/Mathlib` for `*bessel*`, `*paley*`, `*hardy*`,
`*debranges*`, `*nevanlinna*`, `*herglotz*`, `*deficiency*`: **no file**.
For `*sturm*`/`*liouville*`: only Liouville numbers, Liouville's theorem (complex),
and differential-algebra Liouville — no Sturm–Liouville operator theory. The
tree vendors its own frequency-half projectors
(`CCM24PaleyWienerSpectral.lean`) but has no analytic-continuation layer.

## 6. Verdict

- The interface half of `C` is machine-checked (1621, 1622). Nothing else in
  T4 is currently brick-scale: `D` and `S` need a Sturm–Liouville /
  self-adjoint-extension layer that neither Mathlib nor the tree has, and the
  paper's own `S` leg is semiclassical as written.
- The cheap decisive test is not in Lean: it is the scalar check on the
  pole/zero ledger of `m` described in 1624, and the T3/T5 statements (our own
  committed objects) are the parts of the route that are formalizable in
  principle.
- The prolate route stays alive but is not this wave's spend: the wave's
  finding is the two mismatches above, which must be discharged before T4's
  witness can feed T5/T6 (law F33: check the existence and the *type* of the
  base object first).

## 7. Boundaries

`StripDensity(Λ)`, `EndpointMass(ε)`, T1, (★), B4, ρ5, R4/(OB)/W1 and RH are
unchanged and open.