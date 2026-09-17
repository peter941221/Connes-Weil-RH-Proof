# 1590 — the base of the carrier face is attacked head-on: the cheap triviality
# route is BLOCKED with a computable reason, record 1331 section 2.1's
# analyticity claim is CORRECTED, and the obligation is re-typed as a de Branges
# (entire-function) existence rather than a formal one (wave V CONT-14)

Date: 2026-09-17.

Status: PAPER RECORD + NUMERIC CROSS-CHECK. Zero Lean bricks, zero new
declarations, one erratum, one blocked-route law. The carrier's nonemptiness is
still OPEN: this record does not prove it and does not refute it. RH NOT
claimed.

## 1. Result first

Record 1589 filed the negative finding that the base of the 1586--1589
reduction chain is a hypothesis, never a theorem, and named the standing
analytic target `archimedeanSoninCarrier_nontrivial` /
`archimedeanScatteringToeplitzKernel_nontrivial`. This wave attacked that base
directly. The verdict is not the one the attack was aiming for, and it is worth
stating plainly: the base was NOT refuted, and it was NOT proved; what changed
is that both cheap routes are now closed for a computable reason, and the
obligation has a name in the classical literature.

```text
+----------------------------------+-----------------------------------------------+
| item                             | verdict                                       |
+----------------------------------+-----------------------------------------------+
| pole/zero structure of phi       | COMPUTED (hand + mpmath);                     |
|                                  | record 1331 section 2.1 is CORRECTED          |
| cheap triviality by H^2 rigidity | BLOCKED, with an exact reason                 |
| cheap existence by factorization | BLOCKED (already filed, doc 1003)             |
| carrier nonemptiness             | OPEN; now pinned as a de Branges              |
|                                  | (entire-function) existence, not a formal one |
| Lean bricks this wave            | NONE (the route is paper-only)                |
| RH                               | NOT claimed                                   |
+----------------------------------+-----------------------------------------------+
```

## 2. The object, verbatim from the committed source

The multiplier is pointwise multiplication by the unimodular phase

```lean
-- ConnesWeilRH/Source/CC20Concrete/CCM24HardyTitchmarsh.lean:104-106
noncomputable def ccm24ArchimedeanScatteringPhase (xi : ℝ) : ℂ :=
  ccm24ArchimedeanFactor xi / conj (ccm24ArchimedeanFactor xi)
-- :43-45
noncomputable def ccm24ArchimedeanFactor (xi : ℝ) : ℂ :=
  Complex.Gammaℝ ((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * xi : ℝ))
```

and the Hardy--Titchmarsh transform is the F-conjugate of that multiplication
(`:331-336`, with the committed readback at `:340-345`):

```lean
noncomputable def ccm24ArchimedeanHardyTitchmarsh :
    cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).trans
    (ccm24LogSpectralReflection.trans
      (ccm24ArchimedeanScatteringMultiplier.trans
        (Lp.fourierTransformₗᵢ ℝ ℂ).symm))
```

The Paley--Wiener dictionary (record 1331 section 2, re-derived here and
confirmed) converts the carrier into the classical model-space form

```text
W := { w in H^2(C+) : phi * w in H^2(C-) },
phi(z) := Gamma_R(1/2 - 2*pi*I*z) / Gamma_R(1/2 + 2*pi*I*z),  |phi| = 1 on R,
```

with the scale `lambda` entering only through a unimodular character that
commutes with the multiplier, so that the carrier is isomorphic to `W` for every
`lambda` (1331 section 2.5). The carrier's nonemptiness is therefore exactly the
statement `W != {0}`.

## 3. Erratum: the pole/zero structure of `phi` (corrects 1331 section 2.1)

Record 1331 section 2.1 states that `phi` has poles and zeros "interlaced on the
imaginary axis at `Im z = +-(m + 1/2)/(2*pi)`" and that `phi` is "ANALYTIC AND
NONVANISHING in the interior of each half-plane". The two halves of that
sentence contradict each other: a function with poles at `Im z = -1/(4*pi)` is
not analytic in the lower half-plane. The positions are right and the
analyticity claim is wrong. Computed twice, by hand and numerically:

```text
+---------------------+-----------------------+-----------------------+-----------------+
| point z             | numerator A(z)        | denominator B(z)      | phi(z)          |
+---------------------+-----------------------+-----------------------+-----------------+
| +i/(4 pi)   (in C+) | Gamma_R(1) = 1        | Gamma_R(0) = infinity | 0  (ZERO)       |
| -i/(4 pi)   (in C-) | Gamma_R(0) = infinity | Gamma_R(1) = 1        | infinity (POLE) |
| +i/(8 pi)   (in C+) | finite nonzero        | finite nonzero        | 0.2363 (finite) |
+---------------------+-----------------------+-----------------------+-----------------+
```

So `phi` is analytic in `C+` (with zeros there) and has its POLES in `C-`; the
reciprocal statement is the useful one:

```text
1/phi = B/A   is analytic in C-, because
              B = Gamma_R(1/2 + 2*pi*I*z) has all its poles in C+, and
              1/A = 1/Gamma_R(1/2 - 2*pi*I*z) is ENTIRE (Gamma_R has no zeros).
```

The erratum is local to the reason, not to the conclusion: 1331 section 2.2
derives "`w` is entire" from the false analyticity claim; the conclusion is
nonetheless correct, and the correct reason is exactly the boxed statement
above. The conclusion matters because it is the first structural fact the whole
face rests on: **every carrier element is an entire function.**

## 4. The triviality route, and why it is blocked

The cheapest refutation of `W != {0}` would be the two-sided rigidity

```text
H^2(C+) cap H^2(C-) = {0},
```

which is available in the committed model (the two half-line frequency
projections satisfy `P+ + P- = id` and `P+ P- = 0`). Applied to a hypothetical
carrier element `w` it would read: `w in H^2(C+)` by hypothesis, and
`w = (1/phi) * (phi * w)` with `1/phi` analytic in `C-`, so `w` extends to `C-`;
if that extension were in `H^2(C-)`, the rigidity would force `w = 0`. The route
dies at the last step, and the reason is quantitative:

```text
on the horizontal lines of C-, |phi(x - I*eta)| ~ (1 + |x|)^(-2*pi*eta),
so |1/phi(x - I*eta)| ~ (1 + |x|)^(+2*pi*eta)  -- POLYNOMIAL GROWTH,
```

numerically confirmed against the committed factor (ratio to the predicted
weight tends to 1):

```text
+--------+-----+--------------------+------------------+-----------+
| eta    | x   | |1/phi(x - i eta)| | (1+x)^(2 pi eta) | ratio     |
+--------+-----+--------------------+------------------+-----------+
| 0.0796 | 5   | 2.236067977        | 2.449489743      | 0.912871  |
| 0.0796 | 500 | 22.36067977        | 22.38302929      | 0.9990015 |
| 0.1592 | 5   | 5.000633217        | 6.0              | 0.8334389 |
| 0.1592 | 500 | 500.0000063        | 501.0            | 0.998004  |
+--------+-----+--------------------+------------------+-----------+
```

The weight is polynomially large but the boundary modulus is exactly `1` on the
line, so the boundary values of `W := (1/phi)(phi w)` are in `L^2` while the
horizontal-line `L^2` masses can diverge: analyticity plus `L^2` boundary values
does NOT imply `H^2` (the standard witness is `exp(-z^2)`, entire with `L^2`
boundary values and no uniform `H^2` bound). A second check was run to make sure
no Liouville-type shortcut replaces the rigidity: **entire functions CAN lie in
`H^2(C+)`** -- the example

```text
w(z) = ((sin z)/z)^2 * exp(2*I*z)
```

is entire, nonzero, has boundary modulus `(sin^2 x)/x^2` (square-integrable) and
horizontal-line mass `~ pi/(2*y^3) * (sinh^2 y * exp(-2y))^2 -> 0`, so it is in
`H^2(C+)`. Hence no argument of the form "entire plus square-integrable implies
zero" can close the question, and the two-sided rigidity cannot be upgraded
across a multiplier with polynomial horizontal growth.

```text
+----------------------------+-------------------------------+-----------------------------------+
| route                      | hypothesis it needs           | does our phi satisfy it           |
+----------------------------+-------------------------------+-----------------------------------+
| Wiener-Hopf factorization  | factor in L^2 on the line     | NO: unimodular, |phi| = 1         |
| H^2 rigidity (this record) | 1/phi analytic on C- AND      | first half YES, second half       |
|                            | |1/phi| bounded on horizontal | NO: grows like (1+|x|)^(2 pi eta) |
|                            | lines of C-                   |                                   |
+----------------------------+-------------------------------+-----------------------------------+
```

## 5. What the base obligation now is

Combining 1331 section 2 with the correction above: a nonzero carrier element is
a **nonzero entire function** `w` with

```text
w in H^2(C+)   and   (phi * w) in H^2(C-),
```

i.e. a nonzero element of the de Branges space attached to the Hermite--Biehler
function of `phi`. The two conditions are weighted `L^2` conditions against
entire functions, so the existence question is a question about zero sets and
mean types of entire functions -- de Branges' theory of Hilbert spaces of entire
functions, which is exactly the classical Sonin/Weil model space that record
1331 section 2.5 identifies and for which the classical nonzero witnesses are
products of two Weil Lambda factors (Weil, "Sur les formules explicites", 1952).

That is why the base cannot be closed inside the current tree: the missing input
is not a missing estimate on committed objects, it is a classical
entire-function existence theorem, and the productive attack is the one already
registered as T4 of `docs/proofs/1003` (construct a kernel vector from the
prolate/Sonin spectral problem; Connes--Moscovici's negative prolate
eigenfunction is the standard candidate). Every intermediate step of that
construction -- domain, spectral sign, carrier transport, window restriction --
is an independent theorem, and none of them is formalized today.

## 6. Law filed with this wave

**F34. A rigidity identity does not survive a multiplier: before using an
`H^2 cap H^2 = {0}`-type argument (or any "two-sided analyticity forces zero"
step) on a Toeplitz/model-space kernel, compute the horizontal-line growth of
the reciprocal multiplier on the shifted lines.** Polynomial growth of
`1/phi` off the real axis is enough to make the two-sided extension fail `H^2`
while its boundary values stay in `L^2`, and then the question is genuinely a
de Branges existence, not a rigidity. Equivalently: the analyticity of `1/phi`
in the right half-plane decides only that the element is entire (1331 section
2.2), never that it vanishes.

## 7. Ledger

```text
+--------------------------------------------+------------------------------------------+
| object                                     | status after this record                 |
+--------------------------------------------+------------------------------------------+
| phi analytic in C+ with zeros at           | COMPUTED (hand + mpmath); 1331 s2.1      |
| +i(4k+1)/(4 pi), poles at -i(4k+1)/(4 pi)  | CORRECTED                                |
| 1/phi analytic in C-                       | PROVED (B poles in C+, 1/A entire)       |
| carrier elements are entire                | 1331 s2.2, conclusion kept, reason fixed |
| carrier = W (lambda enters as a character) | 1331 s2.5, re-derived here               |
| triviality by two-sided rigidity           | BLOCKED (F34; weight (1+|x|)^(2 pi eta)) |
| existence by factorization                 | BLOCKED (doc 1003, already filed)        |
| W != {0} (carrier nonemptiness)            | OPEN, classical (de Branges / Sonin)     |
| T4 prolate construction (plan 1003)        | OPEN, the productive route               |
| StripDensity(Lambda) / EndpointMass(eps)   | OPEN (unchanged, record 1589)            |
| (star)/B4/rho5/R4/(OB)/W1                  | OPEN                                     |
| RH                                         | NOT claimed                              |
+--------------------------------------------+------------------------------------------+
```

## 8. Boundary

MOVED: the pole/zero structure of the scattering phase is computed and an
erratum on record 1331 section 2.1 is filed; the triviality route is closed with
a computable reason and a counterexample-backed warning; the base obligation is
re-typed as a classical de Branges existence and its productive route is named.

NOT MOVED: no proof of nonemptiness, no refutation of nonemptiness, no Lean
brick, no trace bound, no gap, no sign. Records 1586--1589 remain a CONDITIONAL
reduction, and this record does not change that; it says what the condition is.
