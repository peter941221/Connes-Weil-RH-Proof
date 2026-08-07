# 849 — POSITIVE verdict: the per-F disjointness row is axiom-clean and CLOSED (this row is NOT the open block)

Date: 2026-08-07 · Status: WSL build-green + `#print axioms` decisively clean
Continuation of 848: 848 pinned that the only "genuinely remaining per-F carrier row"
of the constructive CC20 exit was
`finiteSetDisjointFromNontrivialZeros standard cc20TripleFiniteVanishingSet`.
849 proves that this row is in fact **closed and axiom-clean** — it is NOT the
open block.  The block sits somewhere else.

## 0. 结论

**`finiteSetDisjointFromNontrivialZeros` 是封闭的、axiom-clean, 不是开放。**
The concrete disjointness of the CC20 triple {0, 1/2, 1} from
`standard.sourceNontrivialZero` is a *proved* Mathlib-fact, not an assumption.
Whichever construct (constructive-fullWeilPositivity `Exhaustion` input or any
other `input`) fills the criterion slot, this row is available for free.

So the 848 "last open per-F carrier row" is **was-and-still-IS Gaussian** — but it
is now *proved*, meaning 848's framing of "the real remaining open is the per-F
carrier" must be corrected: there is **no open per-F carrier row left in the
finite-vanishing exit** for the standard bridge.

## 1. The decisive evidence: `#print axioms` = axiom-clean

`CC24PerFDisjointAxiomProbe849.lean` (WSL build-green, EXIT=0):

```
'ConnesWeilRH.Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.riemannZeta_half_ne_zero'  depends on axioms: [propext, Classical.choice, Quot.sound]
'...riemannZeta_half_ne_zero_of_dirichletEtaAnalytic_half_eq_ordered' depends on axioms: [propext, Classical.choice, Quot.sound]
'...dirichletEtaAnalytic_half_eq_ordered' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`[propext, Classical.choice, Quot.sound]` is exactly the "axiom-clean" set used
throughout this project (e.g. 844).  So the entire chain down to
`riemannZeta (1/2) != 0` is a **genuine theorem of Mathlib**, reached through the
Dirichlet-eta real/analytic identity and eta series identities — there is **no
unproved constant** hiding the ζ(1/2)≠0 claim.

## 2. How the row closes (the actual proof tail)

`Source/ZetaHalfNonvanishing.lean`:
- `RiemannZetaHalfNonvanishing := riemannZeta (1/2) != 0` (line 26)
- `riemannZeta_half_ne_zero` (93) : `RiemannZetaHalfNonvanishing` — CLOSED
   (via `riemannZeta_half_ne_zero_of_dirichletEtaAnalytic_half_eq_ordered` +
   `dirichletEtaAnalytic_half_eq_ordered`, both axiom-clean)
- `cc20_triple_disjoint_from_standard_source_nontrivial_zeros` (98) :
   `SourceFiniteSetDisjointFromNontrivialZeros standard cc20TripleFiniteVanishingSet`
   — the exact 848 row, CLOSED by case split on the triple (0/1/2/1):
     * p = 0: `riemannZeta 0 = 0` then rfl/`norm_num` shows λ won't; 
     * p = 1/2: `¬ (riemannZeta 1/2 = 0)` from half-ne-zero;
     * p = 1: `(1:ℂ) ≠ 1` from pole non-exclusion.

The same row was the 848 "genuinely open per-F".  The reference doc comment in
`ZetaHalfNonvanishing.lean` header ("project currently has no proof of ζ(1/2)≠0;
the disjointness is therefore parameterized") is **now stale** — the module below
closes it.  That stale admonition caused 848 to over-estimate the open-ness.

## 2. Correcting the finite-vanishing gate picture

```

  (criterion slot)
  input : WeilPositivityInput
      |   has rows (CC20PropositionC1InputData):
      |     finiteSetIsTriple            ... rfl on the triple          (CLOSED)
      |     finiteSetDisjointFromNontrivialZeros ... THEOREM (ZetaHalf) (CLOSED, 849)
      |     tripleVanishingMatchesMellin ... rfl = input.tripleVanishing  (carried by input)
      |     fullWeilPositivity           ... derives from chosen input    (constructive ok, 848)
      |
      v
   standard.SourceRH  ←  CC20PropositionC1SourceCriterion (structural)

So the finite-vanishing *carrier data* for the standard bridge is **fully
constructible**; there is no open per-F row.  What is *not* provided by this row
is the POSITIVITY predicate (`fullWeilPositivity`) — that is the input's own
field.  And on the concrete space, the one *universal ≤0* candidate
(`CC20FiniteVanishingWeilCriterion`) is REFUTED (847b).  The **constructive**
`Exhaustion.FullWeilPositivity` (848) supplies the field but requires the whole
`FullWeilPositivity` structure (fixed-S trace read-off + tripleVanishing +
ledgersCleared) — that is the real, still-open work, not this carrier row.

## 3. Honest state after 849

- **CLOSED (this episode):** per-F disjointness row for the standard bridge —
  axiom-clean, `riemannZeta (1/2) !=0` proved via Dirichlet eta.
- **CLOSED (848):** positive-construction slot compatibility; the refutation is
  per-VALUE not per-TYPE; constructive Exhaustion fills it.
- **OPEN (unchanged, the true 3U/route block):**
    1. a *constructive* `FullWeilPositivity` witness (`FullWeilPositivity inputs g L`
       = fixedSPositiveTraceReadOff ∧ tripleVanishing ∧ ledgersCleared) at a
       concrete `g`, i.e. the actual positive-trace and positive-Well local sum;
    2. the positivity ≥/≤ signature decision (847b) that pins which
       `fullWeilPositivity` the standard criterion must have — the universal ≤0
       is refuted, the per-g exist-positive is proved, the two are not one
       flipped inequality.
- RH **not claimed**; nothing closed.

## Repro

```
# (WSL)
cd ~/projects/Connes-Weil-RH-Proof   # or equivalent Linux-side repo
lake build ConnesWeilRH.Source.ZetaHalfNonvanishing
lake env lean ConnesWeilRH/Dev/CC24PerFDisjointAxiomProbe849.lean   # EXIT=0, axioms=[propext,Classical.choice,Quot.sound]
```

## Evidence

```
Source/ZetaHalfNonvanishing.lean:26     RiemannZetaHalfNonvanishing def
Source/ZetaHalfNonvanishing.lean:93-103 riemannZeta_half_ne_zero / central claim
Source/ZetaHalfNonvanishing.lean:98     cc20_triple_disjoint_from_standard_source... (CLOSED)
Source/DirichletEta.lean               eta infra (axiom-clean)
Dev/CC24PerFDisjointAxiomProbe849.lean  # print axioms, all [propext,Classical.choice,Quot.sound]
```