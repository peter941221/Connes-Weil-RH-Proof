# 1086 - the g3 carrier: closed form, the C-infinity obstruction, and the
# first direct measurement of the gate quantity

Date: 2026-09-01. Follows 1085, which reduced the historical ROOT-supported
negative-detector branch to one inequality on one explicit object. This record
tests `0 < arch h.convSq`. It does not supply the active C3 obligation
`0 <= qw(g)` for the formal orbit detector.

## 1. Where the inequality stands

Within that conditional ROOT-supported negative-detector branch, 1085 leaves:

    find ONE test h with
      supp h ⊆ (-log 2 / 2, log 2 / 2),
      lap h = 0 on {0, 1/2, 1},   lap h rho != 0,
      0 < arch h.convSq,

because every other clause of the root-supported gate is a theorem. The
1077--1079 program is the numerical blueprint; this record evaluates the Lean
gate quantity rather than its earlier surrogate.

Field observation (honest correction to the 1079 bookkeeping): the
1077-1079 quantity `fl2 = margin0 + A - P2` is the level-1 row-model
surrogate of the record-1070 dictionary, NOT `arch h.convSq`.  The Lean
gate reads

    arch F = ( (log 4 pi + gamma) * F(0)
               + int_{y>0} [ e^{y/2}(F(y) + F(-y)) - 2 F(0) ]
                           / (e^y - e^{-y})  dy ).re,
    F = h.convSq,   F(y) = int conj(h(s)) h(s+y) ds,

with NO normalization constant on the convolution square
(`convolutionSquare_apply` is the plain autocorrelation) and
`F(0) = ||h||_2^2`, `F(-y) = conj F(y)` (both Lean theorems in
`CCM25Concrete.CompactLogConvolution`), so the integrand is the REAL
function `2(e^{y/2} Re F(y) - F(0)) / (e^y - e^{-y})`.  This round
measures that number for the first time.

## 2. The C-infinity obstruction and the carrier decision

The 1079 object is `phi` hard-truncated to `[-a, a]` plus the correction
`u^m (a^2 - u^2)^2 1_{|u|<=a}`.  Neither piece is a legal `CompactLogTest`:
hard truncation is discontinuous in the first derivative at `+-a` (where
phi does not vanish), and `(a^2-u^2)^2` is only `C^1`, while
`CompactLogTest` demands `ContDiff RR oo`.  So the literal measured object
CANNOT be the Lean carrier.

DECISION (this round): the Lean carrier is the SMOOTHLY TAPERED family

    h_r(u) = chi_r(u) * phi(u)  +  sum_m c_m b_m(u),
    chi_r  = smooth cutoff, 1 on [-r a, r a], zero for |u| >= r a (r < 1),
    b_m(u) = u^m chi_r(u)   (m = 0, 1, 2),

with the coefficients c solved so that the corrected object vanishes
exactly at {0, 1/2, 1}.  For r < 1 the support sits STRICTLY inside the
open root window, so the root-support clause is legal by construction, and
every piece is `C^oo` by construction.  The price: this is a DIFFERENT
test from the 1079 one, so its sign must be (re)measured - which is
exactly what the probe does, along with the sweep over r.

## 3. The closed form: no Bromwich integral in the Lean definition

The carrier is explicit, so the Lean `def` needs no integral transform.
Write lambda = d^2 - i mu (so `Re lambda = d^2 > 0`) and
`g_3(s) = N' (z^4 - z^2/4) e^{-lambda/4} e^{lambda z^2}`, `z = s - 1/2`
(using `s(s-1) = z^2 - 1/4` and `s(1-s) = 1/4 - z^2`).  The Bromwich
inverse `phi(u) = (1/2 pi i) int g_3(s) e^{-su} ds` splits as
`e^{-u/2}` (from `e^{-su}`, `s = 1/2 + it`) times the `z`-integral; the
latter is evaluated by completing the square
(`(1/2 pi i) int e^{lambda z^2 - z u} dz = e^{-u^2/(4 lambda)} /
(2 sqrt{pi lambda})`, valid for `Re lambda > 0`) and by
`z^k e^{-z u} = d^k e^{-z u}/du^k`, so the polynomial acts as
`(d^4 - (1/4) d^2)` on the base Gaussian INVERSE `G(u) =
e^{-u^2/(4 lambda)} / (2 sqrt{pi lambda})` - the normalization constant
belongs to `G` and is EASY TO DROP when transcribing (it was, and the
pre-registered gate caught it; see the verdict section):

    phi(u) = N' e^{-lambda/4} e^{-u/2} Q(u) e^{-u^2/(4 lambda)}
             / (2 sqrt{pi lambda}),

    Q(u) = q_4(u) - (1/4) q_2(u),
    q_2(u)  = -1/(2 lambda) + u^2/(4 lambda^2),
    q_4(u)  = 3/(4 lambda^2) - 3 u^2/(4 lambda^3) + u^4/(16 lambda^4),

i.e. `Q(u) = 1/(8 lambda) + 3/(4 lambda^2)
             - (1/(16 lambda^2) + 3/(4 lambda^3)) u^2 + u^4/(16 lambda^4)`.

This is a polynomial times a chirped Gaussian - `ContDiff RR oo` is
fun_prop + `ContDiff.cexp`, compactness comes from the bump - and the
normalization `N'` is a positive-real freedom that CANNOT affect the sign
of the arch term (the arch term is quadratic in the test; only the sign
direction of `0 <` matters).  The probe verifies this closed form against
the rig's numerical Bromwich inverse BEFORE anything else runs
(anti-fabrication law (26): a reimplemented object must pass a same-point
self-consistency gate against the imported original).

## 4. The certificate stack for the arch term (decision)

`h_c` is supported in `[-r a, r a]`, so `F = h_c.convSq` is supported in
`[-2 r a, 2 r a]` with `2 r a < log 2`, and

    arch(h_c.convSq) = c0 * F(0) + int_0^{2 r a} I(y) dy
                       + F(0) log tanh(r a),
    I(y) = (e^{y/2} * 2 Re F(y) - 2 F(0)) / (e^y - e^{-y}),   c0 = log(4pi)+gamma,

For `y > 2 r a`, both `F(y)` and `F(-y)` vanish. The integrand is then
`-F(0) / sinh(y)`, because the factor two in the numerator cancels the factor
two in `e^y - e^{-y} = 2 sinh(y)`. Since
`d/dy log(tanh(y/2)) = 1/sinh(y)`, the tail equals
`F(0) log(tanh(r a))`. Also, `I(y) -> F(0)/2` as `y -> 0+`; the numerator
vanishes to first order because `Re F` is even. The gate value consists of
`F(0) = ||h_c||^2`, one compact-interval autocorrelation integral, and the
explicit tail. Directed interval integration is one possible certificate for
a fixed parameter choice. This record does not rule out an analytic sign
argument.

## 5. Lean landing shape for the historical ROOT branch

R1 (next brick if the fork fires): the carrier family as a named
`CompactLogTest` - `chirpedCarrier (d mu a r)` built from the closed form
of section 3 times a smooth cutoff, with `ContDiff`/`HasCompactSupport`
and strict in-window support (`r < 1`).  ContDiff of the product needs
nothing beyond fun_prop; the object is honest even before any sign claim.

R2 (the correction, in Lean): the tool `exists_residualWindow_correction`
SUPPLIES `w` with prescribed values at the seven nodes, so the five-clause
test is `h_c = sumTest h_0 w` with `w`'s targets equal to `-lap h_0` on
{0, 1/2, 1} and 0 on {rho, -rho, -1/2, -1} - existence is a theorem
already in the library.  The REMAINING inequality is then about an object
containing the abstract `w`, so it needs a STABILITY argument: by the 1082
exact quadratic decomposition, `arch(h_0 + w) = arch(h_0) + arch(cross) +
arch(w)`, and a Cauchy-Schwarz-type bound `|arch(crossTest f g)| <=
C(f) * ||g||` would let the measured margin on the explicit pair absorb
any SMALL correction.  The size of the available correction is exactly
the interpolation-constant question in the historical prefix-side wall. Thus
the two ROOT-branch subproblems meet here: the carrier's stability radius is
priced by the same interpolation constant. This observation does not address
the active C3/P2 inequality for the formal orbit detector.

## 6. Pre-registered fork (BEFORE any run)

Gates, all stated before the run:

    G1 (law-26 closed-form gate):
       max_u |phi_cf(u) - phi_brom(u)| / |phi_brom(u)| <= 1e-6
       over the 1078-style sample set (excluding tail noise < 1e-12 * peak).
    G2 (anchor reproduction): the 1079 pipeline (hard truncation +
       polynomial bumps) re-run in THIS script reproduces
       fl2 = -1.294 within 2e-2 (guards reuse of the rig).
    G3 (carrier legality): for each taper r/a in {0.95, 0.8, 0.6}:
       corrected node residual <= 1e-9, detection |G_c(rho_2)| >= 0.3,
       support strictly inside (-a, a) by construction.
    G4 (surrogate continuity): fl2(h_c) < 0 for at least one r.
    G5 (THE GATE): arch(h_c.convSq) > 0 with margin >= 1e-3 * c0 * F(0)
       for at least one r (relative smallness guard only; the raw number
       stands on its own either way).

    FORK:
    F-A = G1..G5 all pass at some r: proceed to the R1 Lean carrier brick.
    F-B = G1..G4 pass but G5 fails at every r: the 1077-1079 surrogate
          evidence does NOT certify the gate quantity - freeze carrier
          work and re-examine the attack line (major negative finding).
    F-C = G1 fails: the closed form is wrong; fix the derivation before
          anything else.

AMENDMENT (2026-09-01, after the run - recorded openly): G1 fired F-C
three times.  The first two firings were REAL closed-form transcription
defects the gate was built to catch (missing e^{-u/2}; missing the base
Gaussian's 1/(2 sqrt{pi lambda})).  The third firing was a REFERENCE
defect, not a math defect: the float64 Bromwich trapezoid's own
grid-convergence residual at the sample points (8.36e-5 between the
8192 and 32768 grids) exceeds the pre-registered 1e-6 threshold, so the
gate was comparing the candidate against reference noise.  G1 is split:

    G1a (round-trip, DEFINITIONAL):
        |M[phi_cf](s) - g_3(s)| / |g_3(s)| <= 1e-8
        against the IMPORTED 1077 make_g3 at s in {0.3+0.4i, rho_2}
        (the same acceptance the rig's own inverse passed in 1078).
    G1b (same-point vs the Bromwich reference):
        maxrel <= max(1e-6, 2 x the reference's own coarse-vs-fine
        grid-convergence residual).

The independent round-trip to 9 significant digits at (0.3+0.4i) -
run as a diagnostic DURING the F-C investigation - is what justified
suspecting the reference rather than the closed form; it is now a
mandatory leg.  The fork's F-C semantics are unchanged for G1a.

Diagnostics carried: arch(h_0) alone, arch(w) alone, arch(h_c) (the
stability picture of section 5), the arch pieces (c0 F(0), window
integral, tail), and an hp (mpmath) spot-check of F(0) and I(y) at three
y-values for the best r (<= 1e-6 rel).

## 7. Verdict (probe-1086h.log, 2026-09-01): tested carrier slice frozen

Gate results (cfg cd=1.5, beta=0.49, gamma_2=21.02204, mu*=0.003553,
a=0.346574, c0=3.108240; log probe-1086h.log):

    G1  PASS (amended two-leg form: round-trip rel 8.3e-11 at
        0.3+0.4i and 1.1e-15 at rho_2; G1b within the reference's
        own convergence floor 8.36e-5).
    G2  PASS (1079 anchor fl2 = -1.277542 vs -1.294, node resid 4.9e-32).
    G3  PASS only at r=0.95 (detect 0.4986); FAIL at 0.80 (0.2668)
        and 0.60 (0.0538).
    G4  FAIL at every r: fl2(h_c) = +0.0962 / +0.4515 / +0.1755 -
        the SMOOTH family's surrogate is POSITIVE where the hard-
        truncated blueprint measured -1.294.
    G5  FAIL at every r after the corrected x1 tail:
        arch(h_c.convSq) = -1.679 (r=0.95) /
        -1.004 (r=0.80) / -0.263 (r=0.60).

No pre-registered fork label matches this outcome: F-B required G1--G4 to
pass, while G3 failed at two tapers and G4 failed at all three. G5 also failed
at all three. As a post-run project decision, this record applies the same stop
action as F-B to this parameter slice: it supplies no gate witness, and work on
this carrier line is frozen.

### 7.1 The two independent negatives

Both the gate and its 1070-dictionary surrogate fail for the tested legal
C-infinity profiles:

  * G4: the surrogate sign is not robust under legal smoothing.  The
    1079 value fl2 = -1.294 belonged to the hard-truncated object with
    polynomial bumps (mass piled against the window edge, lever 3.8);
    the smooth taper at r=0.95 has lever 0.994 and the surrogate flips
    positive. The three tested tapers contain no surrogate witness.
  * G5: after correcting the tail factor described in section 8, the gate
    quantity is still negative at every tested taper:

        r       arch
        0.95   -1.679
        0.80   -1.004
        0.60   -0.263

    These are numerical values for this carrier family only. The original
    component table used the superseded x2 tail and is intentionally removed.

### 7.2 Observed mechanism in this parameter slice

The structural positive ceiling is `c0*F0 + tail`, with
`tail = F0 * log(tanh(r*a))` for taper ratio `r`. At the full window edge
this is approximately `+2.00963 * F0`. Positivity would require the window
term to exceed the negative of that ceiling. Near zero, `I(y) ~ F0/2`; in
this run `I(0.02) = -6.875`, which corresponds to a relative derivative-mass
scale near `6e2`. The chirp phase
`-u^2 mu/(4|lambda|^2) ~ -23.5 u^2` varies by about one period across the
ROOT window. This explains the loss of near-lag autocorrelation in the tested
slice. The correction `w` also had a negative archimedean value at all three
tapers. These observations do not establish the sign for other parameters.

### 7.3 What survives, and the re-examination direction

Survives: the closed form (G1, numerically cross-checked), the rig and
its anchor reproduction (G2), and the measurement method
(FFT-vs-brute-force tie 7e-17..9e-16 at every lag, F(0) against
mpmath at rel <= 7e-15, I(y) against mpmath at three y per taper).
Records 1063/1067 use a different functional. The 1084/1085 reduction still
asks whether some root-window triple-vanishing detecting test has a positive
archimedean square term, and the prefix-side wall remains. The pre-registered
decision freezes this candidate line. It is not a no-go theorem for untested
parameters, for all ROOT tests, or for active C3/P2.

The next question is spectral because `arch(h.convSq)` is a quadratic form and
triple vanishing gives three linear constraints. Record 1087 evaluates finite
compression matrices for this form on the constrained ROOT window. A positive
computed eigenvalue would exhibit a numerical candidate direction. A negative
maximum on a certified exact subspace would give only a lower bound for the
continuum supremum. The actual floating-point spaces are not certified
subspaces. Excluding all positive directions requires a validated upper bound
on the unresolved complement; record 1087 supplies no such bound.

## 8. ERRATUM (2026-09-01, added when record 1087 executed the fork)

Two corrections, neither of which changes the negative result on the three
tested tapers or the registered stop decision. The tail factor was derived
again from the source formula and numerically cross-checked
against raw-integrand quadrature in `1087_c3_roundtrip_cert.py`
(`1087_c3_roundtrip_cert.log`).

1. SECTION 4 TAIL FACTOR. The body above now uses the corrected
   beyond-support tail

       F(0) * log tanh(S/2)        (x1)

   where `[-S,S]` is the support of the square. For taper ratio `r` and
   root half-width `a`, this is `F(0) * log tanh(r*a)`, not
   `2 * F(0) log tanh(r*a)`. The numerator's "2" in
   `exp(y/2)(F(y)+F(-y)) - 2F(0)` is correct, but the denominator is
   `exp y - exp(-y) = 2 sinh y`, so the primitive `-log tanh(y/2)`
   already carries that 2; the x2 reading double-paid it.  Corrected
   section 7 G5 values for the three tapers (x1 tail at their true
   supports, F0 as measured there):

       taper r=0.95:  -2.977252  ->  -1.679
       taper r=0.80:  -1.544236  ->  -1.004
       taper r=0.60:  -0.337002  ->  -0.263

   and the section 7.2 ceiling constant is `c0 + log tanh(r*a)` per F0,
   i.e. +2.010 at the window edge (not +0.911).  Every corrected value
   is still negative. G4/G5 fail on the tested slice, the registered stop
   decision stands, and the surrogate `fl2` comparison is unaffected.

2. SECTION 7.3 FOLLOW-UP REMAINS NUMERICAL. Record 1087 evaluates finite
   compression matrices for `arch|_V` in two basis families, through `K=32`
   and six radii. Every computed largest eigenvalue is negative; the largest
   reported value is about `-0.8535`. This is evidence that the tested spaces
   contain no positive matrix eigenvector. It is not a continuum sign decision.
   A maximum on a certified exact subspace would be a lower bound for `sup_V`,
   but these floating-point spaces are not certified subspaces, and record 1087
   proves no upper bound for the unresolved complement. The historical ROOT
   negative-detector branch therefore remains mathematically unresolved by
   this scan; active C3/P2 is a different same-owner semi-local inequality.
