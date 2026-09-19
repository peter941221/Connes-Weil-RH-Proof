# 1691 — The chirp block is INJECTIVE (Privalov): the fold carries no atom, only the race-rate concentration; barrier re-ranking; the bone's completion ledger

Date: 2026-09-19.

Status: proof record (paper level, hand-derived) + one machine-checked
anchor brick (`ConnesWeilRH/Dev/C1G9R1ChirpFoldAnchor.lean` + Audit;
build `build-logs/1691_chirp_anchor_build.log`, 8476 jobs, the three
standard axioms, zero sorryAx).  No uniform bound is proved and RH is
not claimed.  This record closes the "all three steps" request: the §4
exact face of 1690 (step 2), the formal anchor (step 1), and the
barrier re-ranking (step 3).

## 1. Theorem C — the chirp block is injective

For every `a > 0`, on `L²(0, ∞)`:

```text
ker( P₊ F_a P₊ )  =  {0},     F_a(s) = a^{−1/2} e^{iπ/4} e^{−iπs²/a}.
```

Proof.  Let `b ∈ L²(0, ∞)` with `P₊F_aP₊ b = 0` and set
`g := b · e^{−iπy²/a}` (a.e. equal modulus, so `supp g ⊆ (0, ∞)`).

(i) *Exact shear identity* (machine-checked in the brick,
`chirp_shear_identity`, at L¹ level; L² by truncation
`b·1_{(1/n,n)}` + a.e. subsequence):

```text
(F_a ∗ b)(x) = a^{−1/2} e^{iπ/4} e^{−iπx²/a} · ĝ(−x/a).
```

(ii) *Ray vanishing* (brick, `chirp_fold_freq_vanishing`): the output
vanishing on `x > 0` forces `ĝ = 0` a.e. on the NEGATIVE frequency ray
— a set of positive Lebesgue measure.

(iii) *Privalov uniqueness*: `supp g ⊆ (0, ∞)` makes `ĝ` the boundary
value of an `H²(ℂ₋)` function (Paley–Wiener, lower half-plane by the
`e^{−2πiξy}` convention); an `H^p` half-plane boundary function
vanishing on a boundary set of positive measure is identically zero
(Privalov / F. & M. Riesz; e.g. Duren, *H^p Spaces*; Koosis,
*The Logarithmic Integral I*).  Hence `ĝ ≡ 0`, so `g = 0`, so `b = 0`.
∎

Formalization boundary: the L¹-level exact identity and the ray
vanishing ARE machine-checked; the L² upgrade (truncation + a.e.
subsequence) and Privalov uniqueness are paper-level — Mathlib has no
half-plane `H²` boundary-uniqueness framework yet.  (Scale covariance
`F_{r²a}(rs) = F_a(s)` and unit modulus stay paper-level: real-level
one-liners; the `ℝ → ℂ` coercion grain makes the Lean restatement
unprofitable — recorded so nobody retries blindly.)

## 2. Law F63 — the fold's spectral shape (no atom, no gap)

Combining 1690 Theorem B (near-kernel vectors at the erfc/truncation
race rate) with Theorem C (no exact kernel):

```text
the fold block is INJECTIVE but NOT BOUNDED BELOW:
0 = inf‖Ab‖/‖b‖ is approached, never attained;
the two-sided measure's fold contribution is a CONTINUOUS
concentration, NOT an atom; there is no spectral gap at 0.
```

Consequences: (a) any route expecting a computable fold atom is dead —
1683's divergent surrogate masses are concentrations, not atoms; (b)
front B obligation 2b is exactly Theorem B, while the exact face
(carrier nonemptiness, F33) CANNOT be decided by the normal form — the
chirp is only the fold's leading term, so the committed symbol's
GLOBAL structure is essential (the square-completion algebra of Theorem
C does not extend to a general symbol `m`, and that failure is
precisely the open carrier question); (c) index-type expectations fail
in BOTH directions — F62 (no classical index) and Theorem C (injective
despite the infinite winding).

## 3. Barrier re-ranking after 1690/1691

```text
+------------------------------------------------------------------+
| lane                                | verdict after today        |
+-------------------------------------+----------------------------+
| classical WH index / factorization  | DEAD (F62 + Thm C; would   |
|                                     | mislead in both directions)|
| inner-model replacements            | DEAD (1682 trap / F43)     |
| finite-type witnesses               | DEAD (1627)                |
| Hardy clause (1.6) at p = 2         | DEAD (F51 pole/zero cert.) |
| MP Thm A(ii) + Corollary (p < 1/3)  | DICTIONARY, not a route:   |
|                                     | the p = 2 shortness-sum    |
|                                     | refinement IS the global   |
|                                     | statement (circular)       |
| Câmara–Partington maximal vectors   | rank 3 (feeds front-B      |
|                                     | existence, not the bound)  |
| §4.1 proposition / MP Thm 8.5       | RANK 1 — the fold-split    |
| (d = 0, decreasing argument)        | lane: each smooth branch   |
|                                     | is a d = 0 problem; the    |
|                                     | glue at xi_0 is now fully  |
|                                     | described (Thm A normal    |
|                                     | form + Thm B race + Thm C  |
|                                     | injectivity); missing =    |
|                                     | branch-completeness ->     |
|                                     | trace/mass transfer        |
+------------------------------------------------------------------+
```

The single live named repair is the fold-split lane, and its missing
piece is now stated exactly: the committed two-sided condition on each
monotone branch is a `d = 0` Makarov–Poltoratski-type problem with the
measured Lebesgue-type density (1683); ALL remaining content = whether
the fold's continuous concentration has finite mass against the global
two-sided measure.

## 4. Completion ledger — how much of the bone remains

```text
+------------------------------------------------------------------+
| layer                    | status                                |
+--------------------------+---------------------------------------+
| formal chain             | 100% machine-checked (1680 iff, 1676, |
|  estimate <=> gate <=> RH | 1659, 1636): zero analytic content   |
| localization             | done at surrogate level (1682/1683):  |
|                          | 1 residual gap = true-measure AC on   |
|                          | smooth branches (canonical-system     |
|                          | transfer, MP machinery)               |
| local/fold layer         | COMPLETE (1690 Thm A/B, F62; 1691     |
|                          | Thm C, F63, brick): zero remaining    |
|                          | local content                         |
| global layer             | OPEN — the bound itself; irreducible  |
|                          | by the 1680 no-slack iff; exact form  |
|                          | = finiteness of the fold's continuous |
|                          | concentration vs the two-sided measure|
+------------------------------------------------------------------+
```

Named open objects: five legs at 1634 (Base / T4 / B4 / S3 / WO) have
collapsed to ONE — the global two-sided finite-mass statement — plus
the front-B input (carrier nonemptiness), which by F33 was never a
theorem to prove but a witness to construct, and whose approximate
face is now a constructive theorem at normal form.  Every reducible
structure is reduced; what remains is not reducible, because it is
machine-checkably equivalent to RH.

## 5. Boundary

No uniform annular bound, no carrier nonemptiness, no RH.  The
deliverables: Theorem C + Law F63 (the fold's local layer closed:
normal form, depth, injectivity, no-index), the machine-checked shear
anchor, the re-ranked barrier table, and the ledger above.
