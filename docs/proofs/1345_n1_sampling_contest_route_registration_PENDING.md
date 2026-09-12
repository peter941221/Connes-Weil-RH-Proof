# Record 1345 - N1 sampling-contest route: VERIFIED, REGISTERED, PENDING (待打)

```text
+---------------------------------------------------------------------+
| VERDICT QUALITY: ROUTE REGISTRATION - paper-only. No digits          |
| consumed, no probe executed, no Lean object touched, no execution    |
| preregistered.  Status: PENDING; activation requires the s5 gates.   |
| Q1 "does it reach RH?"  : YES - verified lossless + non-circular (s2)|
| Q2 "is there potential?": difficulty ISOLATED to one named missing   |
|   input (NLLE, s3) + a mechanical explicit-constant synthesis (s4).  |
| Claim grade: MODEL/paper.  RH NOT claimed.                           |
+---------------------------------------------------------------------+
```

## 0. Provenance

Owner-ordered verification ("先确认好:这条路如果打通,是不是真的能到RH,以及是否真
的有潜力打通") of the N1 sampling-contest decomposition proposed under the
1344 B0d-FULL charter, followed by the owner directive "把方案先记录待打" and
"寻找一个大概率能成的方案,而不是抽彩票".  This record registers the route,
the verification, and the literature round (2026-09-12; every URL inline).
It does NOT activate anything: the 1342 probe is spent and stays spent, and
the A1 preregistration (1344 s3) precedes this route in execution order.

## 1. Route statement (the contest)

All objects from committed source; one convention parse still pending
(s5 task 1 of the synthesis phase):

```text
  G(s) := laplaceAt g s = int e^{sx} g(x) dx        (e^{+sx} convention per
          SelectedWeilFormula.lean:35-38; laplaceAt = int (exponentialWeight
          f s).test, CC20YoshidaConvolution.lean:55-56 - exponentialWeight
          primary definition = first parse task of synthesis)
  g    : real, vanishing class, supp g subset (-R, R);
          R = 0.33657359027997263 on the adjudicated 1342 bump subclass
          (1342_falsifier_results.json, committed bound);
          R -> log 2 = 0.6931... on the full prime-free window class (G7:
          support must avoid +-log p, first prime log 2)
  F    := convolutionSquare g = g.involution.convolution g
          (CompactLogConvolution.lean:114-124, Hermitian F(-x)=star F(x))
  term := spectralTerm F rho = xiMultiplicity rho * laplaceAt F (rho - 1/2)
          (C1SpectralWeil.lean:108-115, centeredXiCoordinate rho = rho - 1/2)
  qw   = onLineSpectralMass + offLineSpectralMass   (W3 split + additivity,
          C1SpectralOnlineSplit.lean:47-67)
```

Key algebra (re-derived against the committed convolution law, NOT memory):
for real g, `laplaceAt (convolutionSquare g) s = G(s) * G(-s)`; with w the
centered coordinate of an off-line zero (w = delta + i*gamma,
delta = beta - 1/2 != 0) and Schwarz reflection G(conj z) = conj(G(z)):

```text
  on-line  rho = 1/2 + i*gamma:   term = mult * |G(i*gamma)|^2      >= 0 (W1)
  off-line rho = beta  + i*gamma: term = mult * Re[ G(w) * G(-w) ]  sign-free
  quartet {rho, conj rho, 1-rho, 1-conj rho}: all four members carry the
          SAME real part  =>  quartet total = 4 * mult * Re[G(w)G(-w)]
  sanity: delta = 0 collapses to mult*|G(i*gamma)|^2 = W1  (check passed)
```

CORRECTION ON RECORD (F5 discipline): the chat-level sketch of 2026-09-12
wrote the off-line term as `mult * Re[G(delta+i*gamma)^2]` with quartet
factor 2.  The committed-source derivation gives `Re[G(w)G(-w)]` with
quartet factor **4** (the two factors are conjugate only on the line).
The route is unchanged; every downstream constant inherits the factor 4.

**The contest (★)** - sufficient form, worst phase:

```text
 (★)   sum_{on-line gamma} mult(gamma) * |G(i*gamma)|^2
         >=  4 * sum_{quartets} mult(rho) * |G(w_rho) * G(-w_rho)|
       for every admissible G of the vanishing class.
       (The signed version - keeping Re, exploiting phase cancellation -
       is a sharpening the synthesis may use; (★) is the safe form.)
```

Growth control (the only analytic estimate (★) needs beyond sampling):
|G(+-w)| <= ||g||_2 * e^{R*|delta|} * sqrt(2R), and the explicit zero-free
region gives |delta| < 1/2 - c/log T, so the off-line/on-line evaluation
ratio is bounded by e^{2R*|delta|} <= 2 on the full prime-free class
(<= ~1.4 on the adjudicated subclass).  The contest therefore lives or
dies on the LOCAL NODE ARITHMETIC of the on-line zero sequence, not on
growth.

## 2. Q1 verification - (★) reaches RH, losslessly, non-circularly

```text
 (★) holds uniformly  ==>  gate (forall vanishing g, 0 <= qw g)
     [termwise: Re[G(w)G(-w)] >= -|G(w)G(-w)|, on W3 split, s1 identities]
 gate  ==>  SourceRH  ==>  RH
     [weilCriterion_iff_sourceRH, C1WeilCriterionEquivalence.lean:136-141,
      committed d767a1d, green log 1546_1343_brick_green.log]
 NOT RH  ==>  gate fails  ==>  (★) fails
     [committed reverse leg: capstone + right-zero detector existence,
      C1WeilCriterionEquivalence.lean:118-129 - the detector's G defeats
      any uniform (★)]
```

Consequences, each load-bearing for the owner's Q1:

- **Lossless**: (★)-uniform, the gate, and SourceRH are pairwise
  equivalent; the reformulation weakens nothing and the factor-4 form is
  sufficient-not-necessary (slack goes the safe way).
- **Non-circular** (de Branges trap audit): de Branges-style positivity
  conditions build the Hilbert-space structure FROM the RH-equivalent
  positivity (watkins catalogue + branges/dirichlet-zeta-functions.pdf).
  (★) instead consumes ONLY unconditional inputs: Paley-Wiener type from
  committed support bounds, node set = actual zeros (RVM density +
  verified heights), explicit zero-free region, explicit S(T) bounds.
  No input may presuppose RH or any positivity equivalent to it - this
  is a STANDING RULE of the route, not a comment.
- **Equivalence-to-RH is the honest price**: (★) is as hard as RH.  The
  route does not dissolve the difficulty; it RELOCATES it to a single
  named input (s3) plus constant bookkeeping (s4).
- **Conrey-Li kill-vector audit** (added same day, second search round):
  formulation-level barrier theorems are real - Conrey-Li 1998
  (arXiv:math/9812166) REFUTED de Branges's positivity conditions by
  exhibiting defining functions for which they fail, killing that route
  while RH stayed open.  That kill vector applies to SUFFICIENT-ONLY
  conditions.  (★) is machine-verified EQUIVALENT to RH (chain above):
  under RH-true it is true, so no counterexample can kill it - the route
  cannot be wrong, only hard, and hardness is what s5.1 measures.
  Second check, same round: no impossibility/obstruction theorem exists
  against Nyman-Beurling-type formulations (family still active:
  arXiv:2607.12084, Jul 2026); 75-yr non-closure is hardness evidence,
  not impossibility evidence.  Independence wildcard (RH is Pi_1; if
  ZFC-independent then true in the standard model - MoE 79685,
  n-Category Cafe 2019-09-07) applies equally to every route and is not
  measurable in advance; it changes no decision below.

## 3. Q2 verification - the crack, and the one named missing input

The over-sampling optimism of the chat sketch ("5-21x margin, contest
auto-wins at height") is FALSE as stated, and the failure mode is now
precise:

```text
  Crack: (★) must hold in every world consistent with what we can prove.
  Explicit density technology (Ingham-type N(sigma,T) << T^{A(1-sigma)}
  log^C T) allows, at sigma = 1/2 + eps with eps ~ 1/log T, an off-line
  population of ~ T * polylog = a polylog-fraction of all zeros, sitting
  ULTRA-NEAR the line (delta ~ 1/log T, where e^{2R|delta|} ~ 1 and the
  off-line values are indistinguishable from on-line ones).  In such a
  world a Nyquist window can contain off-line quartets whose 4*mult*|GG|
  loss matches the on-line gain - density theorems are INTEGRATED and
  say nothing about LOCAL concentration at the window scale.
```

**The missing input, named**:

```text
  NLLE (near-line local exclusion): explicit U(T), V(T) with U*V < 1
  such that in every window of Nyquist width pi/sigma at height T,
  4 * (off-line quartet count with multiplicity) * V(T)
      <= (on-line node count) * U(T)^{-1} ... [target SHAPE only - the
  exact inequality is the synthesis phase's output, not this record's]
  status: NO SUCH INPUT EXISTS in the literature (s4 verified).
  Deuring-Heilbronn repulsion is the near-1 analogue and exists only
  there (explicit DH: Benli, arXiv:2410.06082, and only ASSUMING a
  Landau-Siegel zero, for Dirichlet L-functions).  A near-1/2 version
  for zeta itself is exactly the absent theorem.
```

This is the route's single point of failure, and it is now a TARGET
SPECIFICATION rather than a fog: everything else in (★) assembles from
explicit published constants (s4).

## 4. Literature round (2026-09-12; constants are DATA - "reported" means
parse-the-primary-source is a synthesis-phase task before any use)

| input | best known (reported) | source | status for route |
|---|---|---|---|
| explicit S(T) bound | \|S(T)\| <= 0.112 log T + 0.278 log log T + 2.51 | Trudgian, "An improved upper bound for the argument..." (researchgate.net/publication/230756947 cites the classical constants; a 2026 "II" refinement exists) | parse primary; gives max absolute gap between zeros <= ~2*pi*0.224 + o(1) ~ 1.41 << Nyquist width (4.53 / 9.33) |
| verified height | RH true up to 3*10^12 | Platt-Trudgian 2021 (semanticscholar 5a661e73...) | off-line zeros, if any, live above 3e12 |
| multiplicity bound | m(rho) <= 10 log T (unconditional; "no published value for the implied constant" - answerer's Jensen derivation) | mathoverflow.net/questions/514655 (2026-08-25), via Titchmarsh Thm 9.2; Ivic 1999 (jstor 44095720): "no good upper bounds in the literature" | rederive in synthesis; caps quartet loss multiplier |
| explicit zero-free region | Mossinghoff-Trudgian line (mathtube.org lecture page) | parse primary in synthesis | bounds \|delta\| < 1/2 - c/log T |
| near-line repulsion | NONE (DH only near Re=1; Benli arXiv:2410.06082 explicit DH assumes Siegel zero, L-functions) | s3 | THE missing input (NLLE) |
| local zero detection tech | half-isolated zeros (arXiv:2206.11729); effective log-free density (Lemke Oliver, academic.oup.com/imrn 2019) | candidates for NLLE-adjacent technology | survey in synthesis |
| NB family, active | off-line zero => d > 0 with EXPLICIT per-zero product factor (structural parallel of our reverse leg); "Báez-Duarte constant under a weakened moment hypothesis" dated 2026-09-09 | preprints.org/manuscript/202506.0772 (cited 14); researchgate 414054094; Darses 2021 numdam cml.71; explicit NB sums arXiv:1806.05070 | cousinage CONFIRMED: same species (RH as quantitative functional inequality with per-zero deficit); 70-yr non-closure = hardness evidence for the shared core |
| dedup | watkins RH-reformulations catalogue (empslocal.ex.ac.uk/.../RHreformulations.htm) lists M. Riesz, Bombieri's refinement of Weil positivity, Li, Robin, Nicolas, Farey - NO sampling-contest form | one catalogue + two search rounds | (★) formulation appears NOVEL; systematic review deferred to any publication step; Bombieri refinement = nearest classical relative, check in synthesis |
| de Branges trap | positivity conditions that would imply RH | watkins + math.purdue.edu/~branges/dirichlet-zeta-functions.pdf | avoided by the s2 standing rule |
| 2026 survey | "The Riemann Hypothesis: Past, Present and a Letter Through Time" (commissioned) | arXiv:2602.04022 | frontier reference for A3/A4 |
| A3 prey located | arXiv:1703.03827v14 (rev 2026-02-07) "Proof of Riemann hypothesis"; r/math thread 1rc0i3o (2026-03-12): "the key ... is to get Weil's positivity condition" | arxiv.org/abs/1703.03827 + reddit | task #8 target now concrete |
| Claude-RH primary PDF | "More Than Two Thirds of the Zeros..." (2026-08-10), multiplicity machinery "C < 2 => proportions >= 2-C of simple zeros" | www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf | definiteness-fusion primary source; deep read belongs to A1/A3 phases |

## 5. Activation gates (PENDING -> funded), in order

1. **Constant-synthesis thermometer** (mechanical; ~1-2 wk): parse the
   primary sources above (exponentialWeight sign first), assemble the
   explicit chain for (★) with factor 4, m <= 10 log T, gap <= 1.41,
   verified base 3e12, and OUTPUT THE SHORTFALL: the minimal NLLE
   strength X that closes the chain.  Heat/kill, declared BEFORE the
   computation: X within ~2x of existing explicit technology => HOT
   (fund s5.2); orders of magnitude away => COLD (route stays pending;
   ladder rungs still harvestable as conditional theorems).
2. **A1c exception-simulator prereg** (own record number; law 42): inject
   synthetic quartets into the G8-faithful dictionary, map the contest
   margin D(beta0, gamma0, g) with/without a DH-style exclusion window.
   Expectation management committed NOW: the simulator maps DIFFICULTY,
   not truth - under RH-true it can never find a real violation, only
   "if this quartet existed, the gate would break here" (= the committed
   reverse leg, constructively displayed).
3. **Owner funding decision**, informed by 1 and 2 and by the A1 result
   (task #7; alpha <= 1 keeps the uniform-constant net-program alive and
   feeds directly into the synthesis).

## 6. What this record does NOT claim

- Not a proof of (★), of the gate, or of RH; not a Lean object; no digit
  was consumed and none is preregistered here.
- "Novel formulation" = absence of hits in one standard catalogue plus
  two search rounds, NOT a systematic prior-art review.
- Every "reported" constant in s4 is DATA PENDING primary-source parse;
  none may enter a computation or a record verbatim from this table
  (constants-are-data law).
- The equivalence chain s2 inherits the grades of its committed legs:
  formal for the iff legs, paper for the (★) algebra until formalized.

## 7. Next steps

1. A1 execution (task #7, prereg already committed in 1344 s3) - its
   alpha readout feeds s5.3.
2. A3 audit of arXiv:1703.03827v14 (task #8, target now concrete).
3. Constant-synthesis thermometer (s5.1) - owner decision requested
   together with the MEASURED-DISTANCE portfolio presented alongside
   this record.
