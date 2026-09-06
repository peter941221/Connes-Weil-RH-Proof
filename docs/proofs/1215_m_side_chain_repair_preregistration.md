# Record 1215 - M-side chain repair (option B), pre-registration

Date: 2026-09-07.  Status: PRE-REGISTRATION, committed BEFORE any
certificate generation run (law 42).  Consumer: records 1146/1214.  The
route fork A/B/C of record 1214 was decided as B (Peter, 2026-09-07
"继续" on the recommended option).

## 1. What is being repaired

Record 1214 (F1-F3) showed the q28 ABSOLUTE chain is unsatisfiable as
wired: the hrep slot forces `M_true = gateMatrix w` (arch - prime,
1121) while `Hbox` boxes the 1112 arch + prime matrix, and the gate
convention is not negative on ker R.  The repair re-binds the chain to
the quantity the Weil positivity actually needs:

```text
Q(w) = poleTerm w^2 - (arch + prime)(w^2) >= 0.
```

The 1112 bundle already certifies `(arch+prime)(w^2) <= U (G-normalized)
< 0` on ker R - its convention is KEPT; only its degenerate point box
must be regenerated with real widths, and the representation slot must
be re-pointed from ICgate to the arch+prime functional.

## 2. Deliverables (in landing order)

```text
D1  Parity lemma (pure gain, needed by every branch):
    for the class window family, i + j odd =>
      (pairTest w i j).test x + (pairTest w i j).test (-x) = 0
      and (pairTest w i j).test 0 = 0,
    hence ICgate (pairTest w i j) = 0 AND ICarchPrime
    (pairTest w i j) = 0 (both functionals read only the even part
    and the value at 0).  Proof shape: 1126 class-Gram parity +
    s -> -s substitution on the correlation integral.

D2  arch+prime representation theorem (1121 clone):
    def ICarchPrime F := archimedeanTerm F + finitePrimeSum F
    theorem archPrimeMatrix representation:
      ICarchPrime (spanObj w y).convolutionSquare
        = y (archPrimeMatrix w y),
      archPrimeMatrix w i j = ICarchPrime (pairTest w i j).
    Clones the 1121 packedSum machinery (additivity/smul of the two
    functionals); no statement of 1118-1120 changes.

D3  hrep re-binding + consumer restatement:
    absolute_true_q28 gains a variant whose representation hypothesis
    is `ICarchPrime w.convolutionSquare = c (M_true c)` and whose
    conclusion is
      `mu_q28 + poleTerm w.convolutionSquare >= 0`
    via Hbox (with M_true := archPrimeMatrix w, the 1112 convention).
    The original absolute_true_q28 statement is KEPT (it is vacuous
    but true); the variant is the live consumer.

D4  Pole brick:
    for real window tests, poleTerm (w^2) = laplaceAt W (1/2) +
    laplaceAt W (-1/2) = 2 Re (laplaceAt W (1/2)) >= 0 (convolution
    pull-out: laplaceAt (u * v) s = laplaceAt u s * laplaceAt v s with
    the involution flip).  Registered as a lemma with EXACT statement;
    lower-bounding it away from zero on the concrete family is NOT
    needed for D3's conclusion.

D5  Certified M box regeneration (numerics):
    interval-quadrature certificate for
    archPrimeMatrix (classTestFamily 2 h) entrywise, widths
    <= 1e-9 absolute per entry (probe accuracy 1.55e-12), rational
    outward rounding, committed as a NEW data module ingesting
    Q28-compatible MLo/MHi (replace the degenerate point box).
    16 of 28 independent entries are EXACT ZEROS (D1) - their boxes
    are [0, 0]-free: use [0, eps] with eps the certified width.

## 3. Acceptance / falsifiers

- Acceptance: Lean build green at HEAD with D1-D4; D5 accepted when
  the generated rational boxes are proved entrywise in Lean and the
  D3 variant consumes them end-to-end on the class owner.
- Falsifier: if D5's certified widths exceed the row slack
  (mu_q28 ~ 1.04e-6 budget) the run is ABORTED-UNINFORMATIVE and the
  widths are reported, not widened by hand (1097).
- No statement weakening: 1118-1120 statements unchanged; 1121 gains a
  sibling theorem; absolute_true_q28 keeps its form.  No native_decide,
  no q28 box change beyond the D5 data-module replacement (which is
  the point of the repair).
- RH NOT claimed; P2 NOT claimed; SourceRH NOT claimed.

## 4. What this record does NOT do

It does not re-run the 1112 pipeline, does not touch Line B (frozen by
1196), and does not decide the downstream single-c vs subspace
consumption question - D3 is stated for a single (w, c) pair, which is
what the Lean chain consumes.
