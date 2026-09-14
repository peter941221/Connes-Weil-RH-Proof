# 1417 — the phase/density filter, and why the next attempt changes category instead of sharpening the gate

Wave: post-1416 generation, owner-directed. Peter's instruction was to invent
new mathematics rather than re-package the wall, and the decision taken at the
end of the recon is to **change category** (path A) rather than continue
generating bones inside `CompactLogTest`.
Depends on: 1416 (minimal normal form), 125 (Suzuki screw-kernel screen),
263 (prime-log total-positivity counterexample), 004 §8 (obstacle ledger).
Status: **no Lean built, no digits produced, no sign claim made. RH is not
claimed.** Everything analytic in sections 2-4 is PAPER evidence under law 65.

**AUDITED BY [`1418`](1418_arakelov_path_reachability_audit.md) THE SAME DAY.**
Two corrections and one confirmation, applied in place below: section 2's
"with `g` real" hypothesis is unnecessary (1418 §4 proves `qw` factors through
`Re F`, so the cone `F-hat = |g-hat|^2 >= 0` is exactly right as used in
section 3b); section 3b's `lambda_max` is the wrong object, because `Phi` is
unbounded below and `C'` is unpinned (1418 §5); and section 5's framing of the
bridge as a route that reaches RH is NOT supported - condition (i) re-encodes
the gate, and A4's Lean leg is blocked by an absent library (1418 §§2-3).

+========================================================================+
| [1] VERDICT                                                            |
+========================================================================+

```text
+---------------------------------------------------------------------+
| 1. Three promising "new math" cards were killed by the F8 grep      |
|   BEFORE any spend, because the repo had already buried them: total |
|   positivity (263 s8, explicit minor), the Bohr-compactification    |
|   geometric kernel (263 (Z.30), same object, derived here           |
|   independently), Beurling-Malliavin (1332:96 already the frame).   |
|                                                                     |
| 2. Those kills forced a structural finding: the wall is a           |
|   PHASE-level statement and every input the project currently owns  |
|   is DENSITY-level. This is now O3's typed form (section 3).        |
|                                                                     |
| 3. That filter kills "generate another bone inside the same         |
|   category" as a strategy, and selects path A: rebuild the wall as a|
|   regularized arithmetic self-intersection, where the target-side   |
|   theorem (Yuan-Zhang arithmetic Hodge index) is ALREADY PROVED.    |
|                                                                     |
| 4. The program is registered with a sharp first milestone (A2): an  |
|   identity test between the arithmetic degree's constant part and   |
|   the committed head coefficient log(4*pi) + gamma. One symbol      |
|   either matches or it does not.                                    |
|                                                                     |
| 5. AUDIT, same day (1418): path A does NOT reach RH. Condition (i)  |
|   re-encodes the gate rather than reducing it, and A4's Lean leg is |
|   not statable in the pinned library (zero occurrences of Arakelov /|
|   adelic / Chow / Hodge index vocabulary). Items 3-4 stand as the   |
|   selection argument; the headline attached to them does not. First |
|   spend is now W0.                                                  |
+---------------------------------------------------------------------+
```

The expected value of path A is dominated by its **negative** outcome. A typed
impossibility of the Arakelov transport would close a class of approaches for
everyone, not only for this project; a bridge that survives A2 would be the
first genuinely new object the face has produced since the tower. Neither is
claimed here.

+========================================================================+
| [2] THE FOURTH NORMAL FORM OF THE WALL (PAPER, derived here)           |
+========================================================================+

Records 1416 and 125 give three normal forms. Reading the committed
archimedean definitions exposes a fourth: the gate is a weighted `L^2`
positivity question with an explicit symbol.

Source, verbatim.

```lean
-- ConnesWeilRH/Dev/C1SameOwnerWeil.lean:48-52
noncomputable def archimedeanNumerator
    (F : CompactLogTest) (y : Real) : Complex :=
  Complex.ofRealCLM (Real.exp (y / 2)) *
      (F.test y + F.test (-y)) -
    2 * F.test 0

-- ConnesWeilRH/Dev/C1SameOwnerWeil.lean:60-64
/-- The archimedean functional reads `F` itself; it does not square `F`. -/
noncomputable def archimedeanTerm (F : CompactLogTest) : Real :=
  ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
        F.test 0) +
      ∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y).re
```

```lean
-- ConnesWeilRH/Source/CCM25Concrete/SelectedWeilFormula.lean:102-104
/-- The denominator `2 sinh y` of the archimedean density. -/
noncomputable def archimedeanDenominator (y : ℝ) : ℝ :=
  Real.exp y - Real.exp (-y)
```

For the convolution square `F = g * g~`, `F y + F (-y)` is `2 * (F y).re` and
`e^y - e^{-y} = 2 sinh y`, so for real `g` the `Re` is a no-op and `(D1)`
follows. **The reality hypothesis is unnecessary**, and this record's first
draft did not know that: `convolutionSquare` uses `involution`, which
conjugates (`CompactLogConvolution.lean:114-119`, `star (g.test (-t)) * g.test
(x - t)`), which makes `F` Hermitian (`:122-124`, `F(-x) = star (F x)`), and
both readouts of the gate consume `F` only through `F x + F (-x) = 2 * (F x).re`
(`C1SameOwnerWeil.lean:36-45`, `:48-52`, `:61-64`). So `qw` factors through
`Re F` for complex `g` too, `F(0)` is real and nonnegative, and
`F-hat = |g-hat|^2 >= 0` holds as an identity about a nonnegative function. The
cone used in section 3b and 4 is therefore the true cone - established in
1418 §4 from committed source rather than assumed here.

```text
  (D1)   A(F) = (log 4pi + gamma) * F(0)
                + integral_0^inf [ e^{y/2} F(y) - F(0) ] / sinh y  dy
```

`(D1)` is a **renormalized** integral: the kernel is `~ 1/y` at `y = 0` and the
`-F(0)` subtraction is the counter-term. This is consistent with the committed
`archimedeanNumerator F 0 = 0` (`C1SameOwnerWeil.lean:67-70`, proved by
`simp` + `ring`), and it explains why Euler's constant appears at all:
`gamma` is the finite part of `integral (1/y - ...)`.

Expanding the kernel `e^{y/2}/sinh y = 2 sum_{k>=0} e^{-(2k+1/2)y}` and
inserting `F(y) = (1/2pi) integral e^{i y r} |g-hat(r)|^2 dr` gives, termwise,

```text
  integral_0^inf e^{y/2} e^{i y r} / sinh y dy
     = sum_{k>=0} 1/(k + 1/4 - i r/2)
     = -gamma - psi(1/4 - i r/2)              (renormalized, since
                                               psi(a) = -gamma + sum [1/(k+1) - 1/(k+a)])
```

hence, in the shape only,

```text
  (D2)   A(F) = (1/2pi) integral |g-hat(r)|^2 * Phi(r) dr
         Phi(r) = -Re psi(1/4 + i r/2) + C'
```

**`C'` is NOT determined here.** It is assembled from `log(4*pi) + gamma`, the
finite part of `integral_0^inf dy/sinh y` (which is `log 2`-type), and the
repo's Fourier normalization, which is Mathlib's `exp (-2*pi*I*x*xi)`
(record 1331 section 1). Pinning `C'` symbolically under the repository's own
conventions is milestone A0/A1, not a fact of this record.

What is independent of `C'` is the tail. With the Gauss digamma value
`psi(1/4) = -gamma - pi/2 - 3 log 2 = -4.2274...` and
`Re psi(1/4 + i t) ~ log|t|`:

```text
  Phi(0) ~ 4.2274 + C'          (positive core)
  Phi(r) ~ -log|r/2| + C'  ->  -inf    as |r| -> inf    (negative log tail)
  ==> exactly one sign change, at some r_0
```

`r_0` is a constant of the archimedean side that this project has never named.
It is not a zeta invariant (no zeros enter `Phi`), and it is exactly
computable. It is the only genuinely new object section 2 produces, and it is
deliberately deferred: naming a constant before pinning `C'` would violate
law F18.

+========================================================================+
| [3] THE PHASE/DENSITY FILTER, AND THE MECHANISM BEHIND LAW F14         |
+========================================================================+

By 1416 Part 4 the gate on the certificate class is
`qw = -archimedeanTerm - finitePrimeSum`, so `A` alone is not the obligation.
Write the prime measure

```text
  nu = sum_{p} sum_{m>=1} (log p) p^{-m/2} delta_{m log p}
```

so the prime term is `integral F dnu`. Its distribution function, by partial
summation against `theta(t) ~ t` (the prime number theorem) with the `m = 1`
term dominating, is

```text
  nu([0,u])  =  sum_{p <= e^u} (log p) p^{-1/2} + O(u)
             ~  2 e^{u/2}
```

i.e. **the number of effectively contributing terms grows exponentially in the
support radius.** Therefore:

```text
+--------------------+---------------------+--------------------------------+
| support radius R   | contributing terms  | can a sign be decided?         |
+--------------------+---------------------+--------------------------------+
| <= log 2 / 2       | O(1)                | no - too few terms, no phase   |
| (the certificate   |                     |    resolution available        |
|  windows of O2)    |                     |                                |
+--------------------+---------------------+--------------------------------+
| unbounded          | ~ e^{R/2}           | no - the available input is    |
|                    | oscillating         |    density-level (PNT, Q-linear|
|                    |                     |    independence of {log p},    |
|                    |                     |    Gamma-only Phi); a density  |
|                    |                     |    cannot fix the sign of an   |
|                    |                     |    exponentially long          |
|                    |                     |    oscillating sum             |
+--------------------+---------------------+--------------------------------+
```

This is the mechanism law F14 was reporting. Record 1400/1401 found
`delta/R <= ~1e-12` on the `(J1)`-feasible region and concluded there is
structurally no taper lever; that was an observation about a rig. `(D1)`-`(D2)`
plus the `nu` growth show *why*: a taper moves mass in `r`, which changes
`A` at density level, while the prime sum responds at phase level, and the two
sides are not comparable by any estimate that only knows densities.

**Scope correction, made after reading the committed source.** The filter
below is a claim about the FULL gate, over all supports. It does NOT apply to
the committed root-support subclass, and the difference is important enough
that this record initially overstated it. See section 3b.

**The filter, stated as a rule:** the only strictly lower data the project
owns is

```text
  L1  Phi, a Gamma-only symbol            (density-level)
  L2  supp g subset [-R,R] => g-hat of exponential type R   (density-level)
  L3  Q-linear independence of {log p} + PNT               (density-level)
```

and the conclusion `0 <= qw g` is phase-level. **No theorem whose hypotheses
are drawn from L1+L2+L3 can have the gate as its conclusion.** That is not a
claim of impossibility for RH - it is a claim that *this category* cannot
supply the missing input, which is exactly the reason 1342-1353 kept finding

```text
  "every candidate positivity theorem encountered was the same Weil-Bombieri
   wall in different clothes"          (004 section 8, :476-478)
```

and the reason to change category instead of generating another bone.

+========================================================================+
| [3b] THE SIGN, PINNED FROM COMMITTED SOURCE, AND THE WINDOW EXCEPTION  |
+========================================================================+

The 1214/1216 sign-convention fracture made the direction of every statement
above provisional. Reading the committed brick resolves it, verbatim:

```lean
-- ConnesWeilRH/Dev/C1MinimalWeilCriterion.lean:230-232
    C1SameOwnerWeil.qw g =
      -(C1SameOwnerWeil.archimedeanTerm g.convolutionSquare) -
        C1SameOwnerWeil.finitePrimeSum g.convolutionSquare

-- ConnesWeilRH/Dev/C1MinimalWeilCriterion.lean:247-248
    C1SameOwnerWeil.qw g =
      -C1SameOwnerWeil.archimedeanTerm g.convolutionSquare
```

and the name of the interface theorem states the required direction outright:
`qw_nonneg_of_archimedeanTerm_nonpos_of_vanishesOn_halfOnly_of_rootSupport_logTwoHalf`
(`:263`). So the obligation on that class is

```text
  (OB)   archimedeanTerm (g * g~)  <=  0
```

**not** the `0 < archimedeanTerm` recorded in 1389, which is therefore a stale
or opposite-convention note and must not be quoted as the obligation. With the
sign corrected, `(D2)` reads coherently at last:

```text
   Phi :   positive core near r = 0,  negative tail ~ -log|r/2|
   (OB):   integral |g-hat|^2 Phi <= 0, i.e. the NEGATIVE TAIL MUST WIN
   L2   :   supp g subset [-log2/2, log2/2] forces |g-hat|^2 to have
            width >= 2/log 2 ~ 2.885, so the positive core CANNOT be
            protected by localization
```

**The uncertainty principle is therefore not merely an obstruction; on this
class it is the positivity source.** That inverts the role it has played in
this project: record 1078 used it to destroy a construction
("Mechanism is the uncertainty principle, not a defect", `:120`). Here the same
fact is what pushes spectral mass into `Phi`'s negative tail, which is the
direction `(OB)` needs.

And this is precisely why the phase/density filter of section 3 does NOT apply
to the window class: by
`finitePrimeSum_eq_zero_of_support_subset_open_log_two` (used at `:255`), the
prime sum vanishes identically there, so there is no `~ e^{R/2}`-term
oscillating sum to control. On the window the obligation is a **single
Gamma-kernel inequality against a type-constrained `L^2` function** -
density-level data throughout, and therefore the one place in this face where
`L1 + L2` can in principle decide a sign.

Consequences, stated without inflation:

* This does NOT prove RH. `(OB)` is required only on the
  `supp <= log2/2` subclass, and the committed gate quantifies over all
  `CompactLogTest`. Getting off the window is exactly O2's radius gap, and the
  phase obstruction of section 3 is what lives there.
* It DOES identify a self-contained, plausibly decidable theorem with a
  committed statement and no primes in it: prove `(OB)` for the window class.
  That is a real deliverable independent of the bridge program, and it is the
  natural form of what this record earlier called card D-3.
* It gives a cheap consistency probe on `C'`: if `Phi(0) = 4.2274 + C'` were
  large and positive while `|g-hat|^2` could be made narrow, `(OB)` would
  fail, i.e. RH would be false. So pinning `C'` at A1 also measures how much
  work the support constraint is being asked to do. That is a sanity check on
  the arithmetic of `(D2)`, not a result.

### The operator reduction: (OB) is one number

`F = g0 * g0~` is even, so the spatial and bilinear forms coincide:

```text
  A(g0 * g0~)  =  integral_R F(y) K_eff(y) dy  =  <g0 , T_{K_eff} g0>

  K_eff  =  (1/2) e^{|y|/2} / sinh|y|         (renormalized at y = 0)
            +  (log(4*pi) + gamma) * delta_0   (the head, a positive multiple
                                                of the identity)

  R = log 2 / 2

  (OB)   ?==   sup { <g0, T_K_eff g0> : g0 in PW_R, ||g0||_2 = 1 }  <=  0
```

**Corrected by 1418 §5: this is a supremum of a quadratic form, not an
eigenvalue, and the `?==` is not cosmetic.** `T_K_eff` is the multiplier by
`Phi`, and `Phi(r) ~ -log|r/2| + C' -> -infinity`, so it is an UNBOUNDED
self-adjoint operator: compressing it to `L2(-R,R)` is undefined until a form
domain is named, and `lambda_max` of something unbounded below is not a
quantity. The kernel is also not in `L1` (the `1/|y|` singularity), so `T` is
not Hilbert-Schmidt and attainment of the sup is open. And `C'` is unpinned
while it shifts the form by `C' * ||g||_2^2` - so on the unit sphere the
quantity under test moves with `C'`, and the `<= 0` above has no numeric
content until W0 fixes it.

So the window obligation is ONE explicit truncated convolution **form** with
ONE explicit delta term, over an explicit Paley-Wiener class. Two things follow
that matter for pricing.

* The sign check against history: record 1398 measured `A = -88.1952` at
  tier-1, i.e. `A < 0`, i.e. `qw = -A > 0`. With the corrected direction that
  is consistent, and it is a data point supporting `lambda_max <= 0` rather
  than contradicting it. (Under the stale 1389 sign it would have looked
  backwards; that is what the 1214/1216 fracture was.)
* The head term is a positive scalar `3.1083... * I`, so `(OB)` would be
  equivalent to the `1/sinh` part having form-supremum at most `-3.1083...`
  **once `C'` is pinned**; as written the rival is `-(3.1083... + C')`, i.e.
  one number plus one unknown constant (1418 §5, defect 5b). The competition is
  still a quantity rather than a mood - how negative can the `1/sinh` part be
  on an interval of half-width `log 2 / 2` - but it is not yet ONE number, and
  W0 must not be priced as if it were.

This is a Selberg/Beurling-Slepian extremal problem in its standard shape -
truncated convolution operator, explicit even kernel - a class with a large
literature and sharp asymptotics, and it is the one item on the board that is
plausibly closable rather than only statable.

+========================================================================+
| [4] WHAT CHANGED CATEGORY, AND WHY THE TARGET SIDE IS A THEOREM        |
+========================================================================+

Weil's function-field proof of the *same* positivity criterion runs through
the Hodge index theorem on `C x C`: an intersection form of signature
`(1, rho-1)` is negative on the degree-zero hyperplane, and positivity of the
Weil form is the negative of a self-intersection there. The number-field
obstruction is that `Spec Z x Spec Z = Spec Z`: there is no surface, hence no
intersection form, hence nothing for the Hodge index theorem to say.

The 2026-09-14 literature check located a category where that obstruction is
already partially dismantled, and the finding is not a conjecture. Yuan and
Zhang, `arXiv:1304.3538` (45 pages, MSC 14G40 primary), abstract verbatim:

```text
  "We prove an arithmetic Hodge index theorem for adelic line bundles on
   projective varieties over number fields. It extends the arithmetic Hodge
   index theorem of Faltings, Hriljac and Moriwaki on arithmetic varieties."
```

The load-bearing word is **adelic**: an adelic line bundle carries a coherent
system of norms at every place, so the metric component of
`widehat{Chow}^1` is infinite-dimensional even when Neron-Severi is finite-
rank. **That infinite-dimensional metric direction is the second factor
`Spec Z x Spec Z` fails to provide.** A 2025 successor makes the exact
hypotheses visible - `arXiv:2503.14099`: "If L,M are integrable adelic line
bundles with L nef and M vertical" - i.e. negative definiteness is available
precisely on the **vertical / degree-zero** classes, which is the arithmetic
name for the hyperplane Weil uses.

The bridge to zeta-side data is also already a developed subject rather than a
hope: Kudla's program identifies arithmetic degrees of special cycles with
Fourier coefficients of (derivatives of) Eisenstein series, with the
archimedean contribution carried by a regularized Green-current integral -
structurally the same shape as `(D1)`, a `1/y` divergence cancelled by a
subtraction whose finite part is a named constant. Live in 2026:
`arXiv:2607.06285` (survey, Jul 2026), `arXiv:2606.19158` /
`arXiv:2606.18579` / `arXiv:2509.24363` (Modular Heights of Unitary Shimura
Varieties II/III, Aug-Sep 2026).

Deninger's program and Morishita's bridge to the Connes-Consani adelic spaces
(`arXiv:2508.15971`, v5 2026-01-21, to appear in Muenster J. Math.) remain the
place where the *right* surface is proposed - but they propose, they do not
prove. Path A is deliberately built on the proved side.

+========================================================================+
| [5] THE BRIDGE, AND THE ONE-SYMBOL TEST THAT DECIDES IT                |
+========================================================================+

The program's entire content is the existence of a map `phi` from the test
space into adelic line-bundle classes such that

```text
  (i)   widehat{deg}( phi(g) ^ 2 )   =   -c * qw(g)        for a fixed c > 0
  (ii)  widehat{deg}( phi(g) )       =   0                 for EVERY g
```

Then, on the nef class `L` supplying the ample direction, Yuan-Zhang Hodge
index gives negative definiteness on the degree-zero (vertical) classes, `(ii)`
places every `phi(g)` in that hyperplane, `(i)` converts the resulting
inequality into `0 <= qw(g)`, and 1416's committed
`weilGate_unconditional_iff_sourceRH` closes to `SourceRH`. **That would be a
proof of RH from a 2013 theorem plus a construction.** The prior on the
construction is low and is stated as low in the registration.

**What the audit (1418 §2) adds to that sentence.** Reading the display in the
direction of difficulty rather than of proof, the last three lines are free
given `phi`, so *all* of the difficulty is inside the existential "does `phi`
exist". That is not a reduction of RH unless the existence is easier than the
sign, and 1418's three tests say it is not: in Weil's function-field case the
bridge (`C x C`, its divisors, its signature) exists for reasons independent of
RH, whereas over `Spec Z` the bridge must be manufactured to satisfy an identity
whose consequence is exactly the sign being sought; and condition (i) is, in
this repository's own 1415 §3 taxonomy, an EXTERNAL dictionary claim - a
normalization-and-sign coincidence that can never become a machine fact without
importing the source as a formal theory. **This record selected the category
correctly against the phase/density filter and incorrectly inferred that
changing category therefore shrinks the problem.**

Why 1416 is what makes this testable rather than vague: because the gate is
side-condition-free, `(ii)` cannot be arranged by restricting the test class.
`widehat{deg} o phi` must vanish **identically**, so `phi` has to be a
*renormalized* map with its ample-direction already removed. And `(D1)` names
the only candidate for what that removal must cancel: the head term

```text
  (log(4*pi) + gamma) * F(0)      with   F(0) = ||g||_2^2   for F = g * g~
```

which is exactly the shape of an arithmetic degree (linear in the metric,
proportional to the `L^2` mass). Hence milestone A2:

```text
  A2:  compute the constant part of widehat{deg}(phi(g)) for the most
       natural candidate phi, symbolically, and compare against
       log(4*pi) + gamma = 3.1083...
       PASS  -> the renormalization is the one Arakelov theory already
                knows how to do; escalate to A3
       FAIL  -> the failure must be typed: state WHICH term of the
                arithmetic degree cannot be made to match, and register
                the transport as closed
```

A2 is a coincidence test. Nothing forces `(log 4*pi + gamma)` to be the
degree-side constant; if it appears unprompted from Arakelov-side definitions,
that is evidence the bridge is the right one, and if it does not, the mismatch
is a concrete obstruction rather than a mood.

+========================================================================+
| [6] WHAT THIS RECORD DOES NOT CLAIM                                    |
+========================================================================+

* No Lean was built. The repository is unchanged by this record: the last
  committed brick remains `C1MinimalWeilCriterion.lean` from 1416, green on
  try2, 13 declarations, standard axioms.
* `(D1)` and `(D2)` are PAPER derivations under law 65. `C'` is unpinned, the
  `2*pi` normalization is not yet reconciled with Mathlib's convention, and
  the sign convention of `qw = -A - prime` is subject to the recorded
  1214/1216 audit, which must be re-read before any inequality direction is
  used.
* No number in this record is certified. `4.2274...`, `3.1083...` and the
  `2 e^{u/2}` growth are hand/standard-value computations offered so they can
  be checked, not evidence.
* The Yuan-Zhang theorem is quoted at abstract level only. Its precise
  statement - vector space, equivalence relation, signature, hypotheses - is
  NOT reproduced here because it has not been transcribed. That is milestone
  A0, and per laws F17/F19 it must be transcribed from the source, never
  reconstructed from memory.
* Section 3's filter is a claim about the reach of L1+L2+L3 inside the current
  category. It is not a claim that RH is unprovable, and it is not a claim
  that path A succeeds.

RH is not claimed.
