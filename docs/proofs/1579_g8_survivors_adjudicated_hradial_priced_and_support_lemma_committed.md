# 1579 — G8 survivors adjudicated from source: the support lemma is committed, `hradial` is priced

Date: 2026-09-17.

Status: `PAPER ADJUDICATION`. Zero Lean spend, zero digits - this record is a
source-reading pass over already-committed theorems, executed under the wave's
own rule that committed source is the first instrument and that a card option
is a spend claim (laws F26/F27 in the project law register).

Consumer: the survivor queue of record 1576 section 4. The owner card of 1576
section 5 has been executed in 1577 (options (i)-(iii) adjudicated) and 1578
(option (iv), track W W0 landed). What remains is the two-item non-phase class
that 1576 section 4 left alive; this record exhausts it at paper level.

## 1. Item 4.1's "prereq" is a double phantom

1576 section 4 item 1 registered the B3 composite window as surviving on one
cheap prereq: a pointwise support-propagation lemma that it asserted was "NOT
committed yet", plus a check that the 1495 pattern "accepts a shifted half-line
union". Both claims are false against committed source.

**(a) The lemma is committed and heavily used.**

```text
ConnesWeilRH/Source/CC20YoshidaConvolution.lean:386
theorem convolution_support_subset_add_Ioo
    (f g : CompactLogTest) {fLower fUpper gLower gUpper : ℝ}
    (hf : Function.support f.test ⊆ Set.Ioo fLower fUpper)
    (hg : Function.support g.test ⊆ Set.Ioo gLower gUpper) :
    Function.support (f.convolution g).test ⊆
      Set.Ioo (fLower + gLower) (fUpper + gUpper)
```

with ten-plus internal callers, and its engine one level down:

```text
CC20YoshidaConvolution.lean:397
  MeasureTheory.support_convolution_subset   -- support(f ⋆ g) ⊆ support f + support g,
```

which is a SET-sum statement needing no interval shape at all - a half-line
propagation instance is two lines (`Set.add_subset_iff` plus pointwise
`exists`), not a new brick. 1576's own "standard and short" description was
correct about the mathematics and wrong about the commit state.

**(b) The 1495 pattern never needed a union check.**
`selectedRoot_radialSourceLeakage_eq_translatedFiniteWindow`
(`C1G8R3RadialBoundarySupportIdentity.lean`, record 1495) is an EXACT
translation conjugation

```text
(I - E_λ) ∘ C ∘ J = T(-log λ) ∘ selectedRootBoundaryWindowOperator owner ∘ T(log λ) ∘ J
```

landing on the canonical compact window `[-R, 0]` by construction; shifted
windows are what the conjugation produces, not what it must accept. There was
no measurability/coframe plumbing question.

**(c) The consumer is gone anyway.** 1577 adjudicated B3 itself as landed and
its composite-window brick as a phantom; a prereq to a phantom is a phantom.

## 2. Item 4.2 (`hradial` strip object): priced - no committed route exists

1576 priced the strip square-sum as "UNPRICED (no verdict claimed here)". The
reading below closes the pricing with a typed negative about ROUTES (not about
the estimate's truth), so the queue carries no open paper question here.

**The chain shape.** The committed B4 obligation (record 1568 section 1,
transcribed in 1573 section 1) is

```text
B4    Summable i, ‖(D ∘L E ∘L H ∘L (I - E) ∘L H ∘L E ∘L M_p ∘L sourceInclusion) e_i‖²
```

- there is NO root convolution `C` anywhere in the physical B4 chain;
- the `hradial` premise the two-column consumer demands alongside it is
  `Summable ‖(D ∘L (I - E) ∘L M_p ∘L sourceInclusion ∘L N) e_i‖²`
  (`C1G8R3BoundaryOutputFactorizationBridge.lean:509-527`, M abstract);
- 1575 section 3.3 placed its defect in the strip `[τ - Λ(p::S), τ)`,
  `Λ = log ∏ q`.

**Every committed radial/gap summability machine requires the C-slot.** Both
generics in `C1G8R3CompositeBoundaryEnergy.lean` state their conclusions with
`rootConvolution owner` hardwired between the defect and the abstract factor:

```text
:911  compositeRadialLeg_sourceBasis_normSq_summable  (s ≥ 0, M abstract, hwide at λ″)
      ==>  Summable ‖((id - E_λ) ∘L C ∘L M ∘L J ∘L N) e_i‖²
:1287 compositeGapLeg_sourceBasis_normSq_summable     (s ≥ 0, M abstract, hwideHT)
      ==>  Summable ‖((E_λ - P) ∘L E_λ ∘L C ∘L M ∘L J ∘L N) e_i‖²
```

and each draws ALL of its compactness from a named Hilbert-Schmidt factor in
its proof: :911 splits `I - E_λ = (I - E_λ″) + (E_λ″ - E_λ)` and runs both
terms through the 1495/1496 window mechanism (the strip term is the bounded
band `E_λ″ - E_λ` of width `s` COMPOSED INTO the kernel window, never a
standalone map); :1287 routes through
`sourceProlateHilbertSchmidtFactor` (summable at `:1310-1314`) plus the
reflected-owner B3 leg. The abstract `N` and `M` in both statements are the
proof that neither machine ever uses compactness of the source-side plumbing.

**Why strip confinement contributes nothing (the level error the queue nearly
made).** Support confinement is a LOCATION fact about the range; square-summability
is a SINGULAR-VALUE fact about the map. They are independent: every separable
infinite-dimensional Hilbert space is isomorphic to `L²` of a finite strip, so
there exist isometries `U` with `range U ⊆ L²([τ-Λ, τ))` and
`‖U e_i‖ = 1` for all `i` - range inside the strip, square-sum divergent.
The physical map `(I - E) ∘ (transport column) ∘ J ∘ N_p` may well be
Hilbert-Schmidt (the Gaussian-weight structure of the Sonin carrier is the
plausible reason), but that would be a NEW compactness estimate of
source-side plumbing, and no such estimate is committed anywhere in the file
whose theorems all flow through the kernel or the prolate factor.

**Verdict (typed, routes-only, F25-style level check).** `hradial` is
priced CLOSED-AS-SUPPORT-COMBINATORIAL: the route class 1576 §4 advertised
("one cheap support-propagation lemma before the 1495/1496 brick") does not
reach it, because 1495/1496 is a C-window mechanism and the B4 chain has no
C. Funding it would require a new carrier-level compactness estimate; and by
1577(ii) the object is CAPPED regardless - the `hgap` premise remains inside
the 1576 typed stop, so closing `hradial` advances B4 by zero. No spend.

## 3. The survivor queue is now exhausted at paper level

```text
1576 §4 item 1  B3 composite window   PHANTOM      (1577: B3 landed; 1579 §1: prereq doubly phantom)
1576 §4 item 2  hradial strip object  PRICED-CLOSED(1579 §2: no committed route; capped by 1577(ii))
1576 §4 item 3  prime-aggregation AO  REGISTERED   (unchanged: no paper name, not scheduled)
1576 §5 (iv)    track W               LIVE         (W0 landed in 1578; W1 is the funded face)
```

Consequence: on the (★)/B4 phase face there is no funded next action after the
typed stop - the pre-registration of 1568 discharged its own queue. The only
live funded face from the executed card is map 011 track W, where W1 asks the
constrained-extremum question inside the class corrected by 1578.

## 4. Boundary: what moved and what did not

- MOVED: `hradial` re-registered from UNPRICED to priced-with-typed-route-
  verdict; 1576 §4's two "cheap" paper steps identified as committed-material
  re-derivations (first occurrence of the 1415 phantom mode inside a SURVIVOR
  item rather than a card option); law F29 (support is location, summability
  is volume) recorded in the project law register.
- NOT MOVED: (★), B4, ρ4, ρ5, R4, transport all OPEN; no estimate proved or
  refuted; the 1576 stop unchanged; the tower and RH untouched; nothing in
  this record is machine-checked because no Lean changed. RH NOT claimed.
