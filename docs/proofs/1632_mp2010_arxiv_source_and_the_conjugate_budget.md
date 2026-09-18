# 1632 — MP 2010 from the arXiv e-print: the criteria verbatim, the class audit with a certificate, and the conjugate budget (Erratum D, Erratum E)

Date: 2026-09-18. Round: the four items of 1631 section 8 executed
(`R1`, `R2`, `R3`, and the `Q3` rig) plus the branch note for map 043.
No Lean brick this round; two scripts land (`scripts/dvi_extract.py` upgraded,
`scripts/conjugate_budget_1632.py` new).

Read with: 1631 (the inventory this round completes), 1630 (the first MP 2010
retrieval), 1629 (the base re-typed), map 043 (the decision tree).

## 1. Verdict block

```text
(A) SOURCE      MP 2010 (Invent. Math. 180, 443-480) exists on arXiv as
                math/0702497; its e-print is the SAME TeX file as the MIF2.dvi
                on Poltoratski's page (gzip name MIF2f.TEX, Feb 2007).  The
                criteria, both theorems and the section 2 lemmas are now read
                verbatim from LaTeX, not from DVI prose.

(B) Q1 RESOLVED the Hardy-space criterion needs alpha = the argument of SOME
                INNER FUNCTION -- "meromorphic inner" is the survey's
                specialisation for meromorphic symbols, not the source's
                hypothesis.

(C) Q2 RESOLVED the source's clause is  e^{-h} in L^{p/2}(R);  at p = 2 it is
                e^{-h} in L^1(R) (one L-1 condition, equivalently the outer
                factor lies in H^2).  The survey's "L^1" and "L^2" sentences are
                the same condition in two letter conventions.  Exponent 1.

(D) Q5 RESOLVED hypotheses verbatim: Theorem A needs kappa >= 0, gamma' >~ -|x|^kappa,
                sigma' >~ |x|^kappa and carries eps in BOTH directions; the eps
                is removed only in the corollary (sharp transition at c) and in
                Theorem B (all p <= infinity) -- the latter only for symbols
                J Sbar^a with J meromorphic inner, or when U is inner.
                The exponent is p < 1/3 (Erratum E: 1631 wrote p < 1/2).

(E) FLAG CLOSED 1630 section 4's "power-law hypotheses FAIL" is wrong in
                detail: the power-law slot is the MULTIPLIER exponent kappa,
                and the symbol's hypothesis gamma' >~ -|x|^kappa is satisfied
                by our phase for EVERY kappa >= 0.

(F) ERRATUM D   1631 section 4's budget table ("h~ of an L^1(dPi) function can
                carry at most exponent beta < 1, our phase is OUTSIDE") is
                refuted by MP 2010 section 2: the ceiling is o(|x|^{1+kappa})
                from the ONE-SIDED LIPSCHITZ exponent kappa, and the density
                exponent beta and the conjugate exponent 1+kappa are different
                slots coupled by beta < 1 + kappa.  Our phase has kappa = 0+
                and sits strictly below the ceiling for every kappa > 0: the
                growth budget does NOT obstruct the representation.

(G) Q3 ANSWER   the obstruction is a joint density/atoms condition on the BM
                intervals (the shortness sum, critical scaling l ~ d^{(1-kappa)/2}),
                not a pointwise ceiling on the conjugate; the one-sided
                Lipschitz hypothesis is a real restriction (ramp: log-spikes;
                power model: ceiling attained in Theta - sharp).

(H) CLASS       Theorem B's class is closed to us with a certificate: at
                z = i(8n+1)/(4 pi) the orientation m has a ZERO (|m| ~ 0.314 d)
                and the orientation m(-.) has a POLE (|m| ~ 318/d), with
                |m(iy) m(-iy)| = 1.  No entire factor cancels a pole, so the
                symbol is not J Sbar^a with J inner, in either orientation.

(I) NOT CHANGED the base / T4 / B4 / S3 / WO legs stay OPEN and no criterion
                retrieved decides the base at p = 2.  RH not claimed.
```

## 2. What was retrieved, and how

```text
+----------------------------------+----------------------------------------------+
| object                           | provenance                                   |
+----------------------------------+----------------------------------------------+
| MP 2010, "Beurling-Malliavin     | arXiv:math/0702497, e-print = gzipped        |
| theory for Toeplitz kernels"     | MIF2f.TEX (70314 bytes); same paper as the   |
| (Invent. Math. 180 (2010)        | MIF2.dvi pinned in 1631 (file <- paper link  |
| 443-480)                         | on people.math.wisc.edu/~poltoratski)        |
| MP 2005, "Meromorphic inner      | MIF.dvi (chapter, no arXiv source found);    |
| functions, Toeplitz kernels and  | read through the upgraded extractor;         |
| the uncertainty principle"       | statement-level rows stay POINTERS (F45)     |
| survey Hartmann-Mitkovski        | arXiv:1511.08326, LaTeX e-print               |
| arXiv:1511.08326                 | ToeplitzKernel5.tex                          |
+----------------------------------+----------------------------------------------+
```

The DVI of MP 2010 was already readable for prose, but every *formula* was
missing, and the criteria of this paper are formulas.  `scripts/dvi_extract.py`
was upgraded for this round:

```text
1. MATH FONTS      cmmi/cmmib (Greek at codes 0-39, Latin at their ASCII codes,
                   the six variants, the named symbols plain.tex places by
                   hand), cmsy/cmbsy (pinned on LaTeX fontmath.ltx: "14 = \leq,
                   "32 = \in, "6A = \vert, ...), cmex (integrals/sums at
                   "48-"60, extensible delimiters at 0-15), msbm (blackboard
                   bold, so that R does not vanish).
2. SUB/SUPERSCRIPTS  the z family is a sub/superscript displacement that does
                   not disturb v: small moves emit _ or ^, which is what makes
                   L^1(dPi), h_0, x^{kappa} readable.  Vertical moves are
                   classified by SIZE, not by opcode family.
3. TRUE PAGE BOUNDS  each page is parsed from its bop to the NEXT bop.  The
                   earlier version parsed every page to end-of-file and
                   concatenated, so a one-byte desynchronisation swallowed the
                   rest of that chunk and the redundancy of the copies hid it.
4. GLOBAL FONT SCAN  TeX writes a fnt_def only the FIRST time a font is used,
                   in practice all of them on page 1.  A page parsed in
                   isolation therefore has an EMPTY font table and renders
                   nothing (it still emits the newlines and the _ markers, which
                   is what a first diagnosis looks like).  scan_fonts() walks
                   the whole file, validates the record layout and the printable
                   name, and seeds every page.
```

Diagnostics used, kept in the transcript rather than the record: a dropped-glyph
counter by (font, code) - it showed 7924 glyphs dropped under the name cmex10
while the byte stream was still in sync, which is the signature of a font-table
fault rather than a byte fault; and a re-walk of the opcode stream logging
font/push/pop/unknown events with byte offsets.

The arXiv e-print makes the upgrade a fallback rather than the main road: when
both exist, LaTeX first (law F50).

## 3. The criteria, verbatim (arXiv:math/0702497)

Dictionaries first, because the class ladder is the point:

```text
N[U]      = ker T_U on H^2                      (the Hardy Toeplitz kernel)
N^+[U]    = {F in N^+ cap L^1_loc(R) : Ubar Fbar in N^+}       (Smirnov-Nevanlinna)
N^p[U]    = N^+[U] cap L^p(R),   0 < p <= infinity
```

so `N^2[U] = N[U]` (Smirnov), which is exactly the class of the base.

**The basic criterion** (display labelled `basic`, the published (1.6)):

> Suppose gamma: R -> R is a smooth function. Then `N^+[e^{i gamma}] != 0` if and
> only if `gamma = -alpha + ht` for some smooth **increasing** function alpha and
> some `h in L^1_Pi`.

**The Hardy-space criterion** (the sentence following it, no separate number):

> There is a similar criterion for Toeplitz kernels in Hardy spaces:
> `N^p[e^{i gamma}] != 0` if and only if gamma admits a representation (basic)
> with **alpha being the argument of some inner function** and with
> `h in L^1_Pi` such that `e^{-h} in L^{p/2}(R)`.

**Theorem A.** Let `kappa >= 0`, and let `U = e^{i gamma}`, `S = e^{i sigma}` be
smooth unimodular functions on R such that

```text
gamma'(x) >~ -|x|^kappa,     sigma'(x) >~ |x|^kappa,    (x -> infinity)     (TA)
```

(i) if gamma is not (kappa)-almost decreasing then `N^+[U S^eps] = 0` for all
eps > 0; (ii) if gamma is (kappa)-almost decreasing then
`N^p[U Sbar^eps] != 0` for all eps > 0 and all **p < 1/3**.

**(kappa)-almost decreasing** (the generalized shortness): `gamma(-inf) = +inf`,
`gamma(+inf) = -inf`, and

```text
sum_{l in BM(gamma), d(l) >= 1} d^{kappa-2} l^2 < infinity,      BM(gamma) = components of {x : gamma(x) != max_{[x,+inf)} gamma}
```

**Corollary.** with `sigma' ~ |x|^kappa` and `c = c(U,S;kappa) = inf{a : gamma - a sigma is (kappa)-almost decreasing}`: for all `p < 1/3`,
`N^p[U Sbar^a] = 0` for `a < c` and `!= 0` for `a > c`.  Then the sentence that
matters for us:

> In the special case where `U` is an inner function, we can extend the
> statement of the corollary to all values of `p`, in particular `p = 2`.

**Theorem B.** Let `J` be a **meromorphic inner** function and suppose the
unimodular `S` satisfies `(arg S)'(x) ~ |x|^kappa`.  With `c = c(J,S;kappa)`,
for all `p <= infinity`: `N^p[J Sbar^a] = 0 (a < c)`, `!= 0 (a > c)`.

**Theorem C** (sub-exponential, `kappa in (-1,0]`): same shape in the weighted
classes `N^+_kappa`, `N^p_kappa`, still `p < 1/3`.

## 4. The five questions, answered

```text
+----+------------------------------+---------------------------------------------+
| Q  | question (1631 sec 8)        | answer (this round)                          |
+----+------------------------------+---------------------------------------------+
| Q1 | inner or meromorphic inner?  | INNER.  The p-criterion says "the argument   |
|    |                              | of some inner function".  The survey's       |
|    |                              | "meromorphic inner" is its own universe      |
|    |                              | (U = Thetabar Psi with both meromorphic).    |
|    |                              | Since gamma and ht are smooth, the effective |
|    |                              | requirement is a smooth argument, which      |
|    |                              | inner functions with singular parts may or   |
|    |                              | may not have.                                |
+----+------------------------------+---------------------------------------------+
| Q2 | e^h in L^1(R) or L^2(R)?     | e^{-h} in L^{p/2}(R); at p = 2 that is one   |
|    |                              | L^1 condition, equivalently the outer factor |
|    |                              | F = e^{-h/2 + i ...} lies in H^2.  The       |
|    |                              | survey's two sentences differ only by the    |
|    |                              | letter convention (its H = e^{h+i ht} has    |
|    |                              | |H| = e^h, so "e^h in L^2" is the same as    |
|    |                              | "e^{-h_MP} in L^1").                         |
+----+------------------------------+---------------------------------------------+
| Q3 | joint ceiling on ht?         | SEE SECTION 6: the ceiling is o(|x|^{1+kappa})|
|    |                              | from the one-sided Lipschitz exponent, and   |
|    |                              | the remaining content is the density/atoms   |
|    |                              | condition (the shortness sum).               |
+----+------------------------------+---------------------------------------------+
| Q4 | transfer to d = 0            | unchanged: the epsilon-perturbed theorems    |
|    |                              | do not transfer to a clean statement at our  |
|    |                              | symbol, and no retrieved theorem removes the |
|    |                              | eps outside the meromorphic-inner class.     |
+----+------------------------------+---------------------------------------------+
| Q5 | is the eps-gap removable?    | NO in general (Theorem A(ii) and Theorem C    |
|    |                              | carry eps in both directions); YES in two     |
|    |                              | precisely delimited cases: the corollary's    |
|    |                              | sharp transition at c, and Theorem B, both    |
|    |                              | for meromorphic inner J (resp. inner U), all  |
|    |                              | p.  Both are out of class for our symbol.     |
+----+------------------------------+---------------------------------------------+
```

Erratum E (exponent): 1631 section 5's table says Theorem A(ii) + Corollary
"APPLIES, p < 1/2".  The primary source says **p < 1/3** in Theorem A(ii) and in
the corollary (and in Theorem C).  The `1/2` is unsourced; the DVI extraction
that first produced it shows the mangled glyph-run `p < 1 Gamma-Gamma-fe-Gamma-Lambda-s-3`
which is `1/3` with a broken digit.  Nothing else in 1631 depends on `1/2`.

## 5. The class audit, with a certificate (F40 re-derived, stronger)

The tempting near-miss, recorded because it is the kind of step that has to be
killed by a computation rather than by a phrase: `m(-.)` looks inner.  It is
unimodular on R, it decays along the imaginary axis (`|m(-iy)| = 1/|m(iy)| -> 0`
for y > e), and all its zeros would sit in the lower half-plane.  If it *were*
inner, then `V = e^{4 pi i (log lambda) xi} m(-xi) = J Sbar^a` with `J`
meromorphic inner and `Sbar^a` the exponential, and Theorem B would decide the
base at `p = 2`.  The computation kills it:

```text
z = i(8n+1)/(4 pi)     |m(z)|              |m(-z)|            1/d
d = 1e-2               0.027                36.99              100
d = 1e-3               0.00309              323.2              1000
d = 1e-4               0.0003137            3188               10000
d = 1e-5               3.141e-05            3.184e+04          100000
d = 1e-6               3.142e-06            3.183e+05          1e+06
```

so at the same points one orientation has a **zero** (`|m| ~ 0.314 d`) and the
other a **pole** (`|m| ~ 318/d`), and on the imaginary axis
`|m(iy) m(-iy)| = 1` (checked: `806.897 x 0.00123932 = 1`, `2.445e-09 x 4.090e+08 = 1`).
The pole is in the UPPER half-plane, and an inner function is holomorphic there;
no entire factor cancels a pole.  Hence:

```text
+---------------------------------------------+-------------------------------+
| hypothesis of the only p = 2 criterion      | our symbol                    |
+---------------------------------------------+-------------------------------+
| Theorem B: J meromorphic inner, symbol      | FAILS, both orientations:     |
| J Sbar^a                                    | poles at z = i(8n+1)/(4 pi)   |
| Corollary remark: U inner                   | FAILS (same certificate)      |
| Theorem A(ii)/Cor: gamma (kappa)-almost     | in the perturbed form only,   |
| decreasing, p < 1/3                         | and p < 1/3, not p = 2        |
+---------------------------------------------+-------------------------------+
```

This is 1630's F40 with the failing mechanism named: not "m is unbounded"
(which only says m is not inner, leaving the reciprocal open) but the
**pole/zero interlacing of the Gamma-ratio on the imaginary axis**, which closes
both orientations at once.  A criterion at `p = 2` for our symbol would have to
be a genuinely new theorem about symbols with interlaced poles and zeros.

## 6. The conjugate budget (Erratum D), with the rig

1631 section 4 read the two slots off a power-tail table and concluded that a
conjugate `ht` of an `L^1(dPi)` density can carry at most exponent `beta < 1`, so
the committed phase `psi ~ 2 pi x log|x|` (exponent `1 + o(1)`) would be OUTSIDE
the density budget - "ht cannot carry it".  The primary source's quantitative
layer says otherwise.  MP 2010 section 2:

```text
Lemma 1   kappa >= 0,  h in L^1_Pi,  ht'(x) <~ x^kappa   ==>   ht(x) = o(x^{kappa+1})
Lemma 2   the same with ht'(x) + a x^{-1} ht(x) <= x^kappa (also gives ht' <= x^kappa + o(x^kappa))
Lemma 3   kappa in [-1,0),  h in L^1(|x|^{-2-kappa}),  ht' <~ x^kappa  ==>  ht = o(x^{kappa+1})
Lemma 4/5 (persistence)  f in L^1_Pi, 0 not in supp f, g = |x|^{-alpha} f, 0 <= alpha <= beta or
          0 <= beta < alpha < 2:  ht_f'(x) <= (1+o(1))|x|^beta  ==>  ht_g'(x) <= (1+o(1))|x|^{beta-alpha}
```

Lemma 1 is the answer: **the ceiling on the conjugate is set by the one-sided
Lipschitz exponent of `ht'`, not by the power of the density**, and a model
density `h ~ |x|^beta` lies in the weighted space of Lemma 3 exactly when
`beta < 1 + kappa`.  So density exponent and conjugate exponent are *different*
slots, coupled by

```text
kappa (Lipschitz)   weight |x|^{-2-kappa}   density beta <   ht ceiling
0                   |x|^-2.00               1.00             o(x^1.00)
0.25                |x|^-2.25               1.25             o(x^1.25)
0.5                 |x|^-2.50               1.50             o(x^1.50)
1.0                 |x|^-3.00               2.00             o(x^2.00)
```

The committed phase has `psi' ~ 2 pi log|x|`, hence `kappa = 0+`: it is
`<~ |x|^kappa` for EVERY `kappa > 0`, and `x log x` sits strictly below
`o(x^{1+kappa})` for every `kappa > 0`.  **The growth count does not obstruct the
representation of the phase as `ht`.**  What remains is the joint density/atoms
condition, which is where the survey's "crucial part" and MP's extremal problem
(`0 <= m_0 <= h_0`, minimise `int h_0 ht_0' + eps int |x| h_0 dPi`) live.

`scripts/conjugate_budget_1632.py`, run at 30 digits, four checks:

```text
1. RAMP  h(t) = t 1_[1,T], T = 20: h in L^1(dPi) with weighted mass ~ (1/2) log T,
   closed form  ht(x) = (1/pi)[ x log|(x-1)/(x-T)| - (arctan T - pi/4) ]
   checked against direct quadrature outside the support (rel. diff < 1e-30), and
   at the edge:
     delta      ht(T+delta)      ht - (T/pi) log(1/delta)
     1e-3       62.490390         18.514254
     1e-4       77.146051         18.511203
     1e-6       106.463061        18.510789
     1e-8       135.780479        18.510783
   the remainder is constant to 1e-5: ht(T+delta) = (T/pi) log(1/delta) + C, so
   ht' ~ (T/pi)/delta -> infinity.  L^1(dPi) membership gives no Lipschitz control;
   the hypothesis of Lemma 1 is a real restriction, not a formality.

2. SHARPNESS  h(t) = t^beta 1_[t>1]:  ht(x) = cot(pi beta) x^beta + C_beta + O(x^{beta-1}),
     beta     x        ht                cot(pi b) x^beta     deviation
     0.25     100       1.7572162         3.1622777          -1.405061
     0.25     10000     8.5974751         10                 -1.402525
     0.75     10000    -1000.6169         -1000              -0.616857
   the deviation is constant in x to 3 digits: ht = Theta(x^beta), so the ceiling
   o(x^{kappa+1}) = o(x^beta) at kappa = beta - 1 is ATTAINED and the weighted
   hypothesis of Lemma 3 is sharp (it fails marginally there: int t^beta t^{-1-beta}).
   One exceptional exponent: beta = 1/2 has cot(pi/2) = 0, the leading term vanishes
   and ht decays like x^{beta-1} = x^{-1/2} (verified: ht x^{1/2} = -0.792 constant) -
   the single exponent where the ceiling is not attained.

3. COUPLING  the table above; our phase has kappa = 0+ and no growth obstruction.

4. UPPER-DENSITY BOUNDARY  model l_n = n^s, d_n = n:
     S(kappa) = sum n^{kappa-2+2s} < infinity  <=>  s < (1-kappa)/2,
     critical scaling l ~ d^{(1-kappa)/2}, log-divergent at equality:
     kappa    s        sum              verdict            s* = (1-kappa)/2
     0        0.2      2.28139          converges          0.50
     0        0.5      10.4807          LOG DIVERGES       0.50
     0        0.8      633.426          diverges           0.50
     1        0.2      129.375          diverges           0.00
     1        0.8      4.75933e+06      diverges           0.00
```

## 7. Laws

```text
F48  the conjugate slot of the criterion is bounded by the ONE-SIDED LIPSCHITZ
     exponent, not by the density's power: h in L^1(dPi) alone gives no pointwise
     control (ramp: ht(T+d) = (T/pi) log(1/d) + C, jumps make log-spikes); with
     ht' <~ |x|^kappa (kappa >= 0) the ceiling is o(|x|^{1+kappa}) (Lemma 1), and
     for kappa in [-1,0) the weighted condition h in L^1(|x|^{-2-kappa}) is needed.
     Density exponent beta and conjugate exponent 1+kappa are DIFFERENT slots,
     coupled by beta < 1 + kappa (1632 sec 6, Erratum D).

F49  quote the exponent from the primary source: MP 2010 Theorem A(ii), the
     corollary and Theorem C give p < 1/3 (not 1/2), and the eps-gap is removed
     only in the meromorphic-inner class (Theorem B) or when U is inner
     (corollary remark) - both out of class for us.

F50  prefer the arXiv e-print LaTeX of a paper over its DVI when both exist
     (MIF2.dvi <-> math/0702497 = MIF2f.TEX); a DVI-only fallback needs a GLOBAL
     font scan, because TeX writes each fnt_def once (in practice on page 1) and
     a page parsed in isolation renders nothing while still emitting newlines.

F51  "unimodular on R + decaying along one ray" does not make a symbol inner:
     locate the poles.  The class test for Theorem B (and the corollary's all-p
     remark) is holomorphy in C_+; for our m both orientations have poles at
     z = i(8n+1)/(4 pi) (certificate: |m| ~ 318/d there against |m(-.)| ~ 0.314 d,
     and |m(iy) m(-iy)| = 1), so no entire factor can put the symbol in class.
```

## 8. Source pins

```text
MP 2010   https://arxiv.org/abs/math/0702497   (e-print: MIF2f.TEX)
          published: Invent. Math. 180 (2010) 443-480
          mirror DVI: https://people.math.wisc.edu/~poltoratski/MIF2.dvi
MP 2005   https://people.math.wisc.edu/~poltoratski/MIF.dvi  (chapter in
          Perspectives in Analysis, Math. Phys. Stud. 27, Springer 2005,
          185-252) - read via the upgraded extractor, rows stay POINTERS
survey    https://arxiv.org/abs/1511.08326  (ToeplitzKernel5.tex)
index     https://people.math.wisc.edu/~poltoratski/publications.htm
```

Scripts landed: `scripts/dvi_extract.py` (upgraded: math fonts, sub/superscript
markers, true page bounds with per-page resynchronisation, global font scan) and
`scripts/conjugate_budget_1632.py` (ramp, sharpness, coupling, density boundary).

## 9. Boundaries

```text
- no Lean brick; nothing in the Lean tree changed
- the base is NOT decided: the class route is closed with a certificate, the
  p < 1/3 lane is a true nontriviality statement one exponent short of us, and
  the perturbed forms do not transfer to d = 0
- 1631's budget table is corrected (F48), 1630 section 4's flag is closed (E),
  the p-exponent is corrected (F49) - nothing else in the record set is touched
- RH not claimed; no gap premise introduced; the carrier remains a def (F33)
```