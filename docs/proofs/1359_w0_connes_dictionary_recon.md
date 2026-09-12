# Record 1359 (W0 RECON LOG, open) - Connes math/9811068: first-pass gap observations

```text
+---------------------------------------------------------------------+
| Wave W0 of the 1358 direct-attack charter (owner "直接打" 2026-09-  |
| 12). Status: FIRST PASS, 2 reads on the question budget; page-level |
| inventory of the number-field sections CONTINUES (task #14). No     |
| claims below are load-bearing yet; all quotations raw from          |
| https://arxiv.org/abs/math/9811068 (88 pages, v1 1998-11-10).       |
+---------------------------------------------------------------------+
```

## 1. Raw evidence (verbatim)

Abstract:
> "We give a geometric interpretation of the explicit formulas of number
> theory as a trace formula on the noncommutative space of Adele
> classes. This reduces the Riemann hypothesis to the validity of the
> trace formula and eliminates the parameter δ of our previous
> approach."

Theorem 5 (positive-characteristic case, section still being located):
> "Let k be a global field of positive characteristic and Q_Lambda be
> the orthogonal projection on the subspace of L2(X) spanned by the
> f ∈ S(A) such that f(x) and f^(x) vanish for |x| > Lambda. Let
> h ∈ S(C_k) have compact support."
preceded by the passage: "the trace formula (16) implies the positivity
of the Weil distribution, and hence the validity of RH for k.
Remember that we are still in positive characteristic where RH is
actually a theorem of A. Weil."

## 2. First-pass dictionary observations (tentative, page-check pending)

1. SHAPE MATCH: his positivity object is named "positivity of the Weil
   distribution" = our gate's classical species; B0b (d767a1d) is the
   Lean formalization of the number-field version of exactly that
   distribution on a truncated test class. Same wall, bigger class.
2. DIRECTION BOOKKEEPING (the whole W0 point): in char-p the formula
   implies positivity and RH is ALREADY Weil's theorem - the
   equivalence is certified against a true statement. In char-0 the
   abstract's word is "REDUCES": formula => RH; the converse
   (RH => formula) is the geometric content he could not finish. Our
   machine-checked tower says: on our side, positivity <=> RH is both-
   ways and PROVED (as an iff) - what neither world has is a proof of
   positivity itself.
3. TEST-CLASS LEVERS to map next: (a) his Λ-truncation of f with both
   f and f-hat vanishing beyond |x| > Λ vs our realized bump support
   radius ~0.335 (log-lattice truncation); (b) h compactly supported
   on the idele class group vs our CompactLogTest + cc20TripleFinite-
   VanishingSet; (c) his absorption-spectrum language (all zeros enter
   with the non-critical ones possible only in a larger component)
   vs our W3/W4b on/off-line split - the two decompositions may be
   literally the same partition seen spectrally vs arithmetically.
4. The earlier folk echoes at this wall (1355 Yakaboylu Ŵ; 1352
   Blinovsky) both re-enter at item 2: none supplies positivity;
   consistent with "the wall is the positivity itself" (1346 s3
   audit). W0 adds the third independent confirmation of location.

## 3. Open questions (next reads, in order)

Q1  Number-field trace-formula statement: exact theorem numbers, and
    where the distributional positivity is defined (his §III-§V region;
    Selecta version pagination differs from the arXiv scan).
Q2  Does any lemma in the paper prove positivity on a SUBCLASS that
    our vanishing class can be restricted into? (If yes: B-blueprint
    collapses to a pullback exercise - check honestly, expectation low.)
Q3  The "eliminates the parameter δ" claim vs our prereg δ-parameter
    geometry (1345 s1: delta = distance from line): is his δ-elimination
    the adelic trick that our compact-log truncation re-introduces?

## 4. Register line

W0 recon, first pass: no breach, no harvest yet, wall location
confirmed from a fourth source. Deliverable target unchanged:
B-blueprint v1 (spec of the object to invent), priced in 1358 s3.
RH NOT claimed anywhere.
