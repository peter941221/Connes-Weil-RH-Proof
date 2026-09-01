# 1086 - the g3 carrier: closed form, the C-infinity obstruction, and the
# first direct measurement of the gate quantity

Date: 2026-09-01.  Follows 1085 (kernel (a) = the record-1080 scalar gate,
one inequality on one explicit object).  Advances consumer 3 kernel (a):
the positive attack on `0 < arch h.convSq`.

## 1. Where the inequality stands

After 1085 the entire remaining content of consumer 3 kernel (a) is:

    find ONE test h with
      supp h ⊆ (-log 2 / 2, log 2 / 2),
      lap h = 0 on {0, 1/2, 1},   lap h rho != 0,
      0 < arch h.convSq,

because every other clause of the root-supported gate is a theorem.  The
1077-1079 program is the numeric blueprint; what this record adds is the
missing piece nobody had measured: the LEAN GATE QUANTITY ITSELF.

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

    arch(h_c.convSq) = c0 * F(0) + int_0^{2a} I(y) dy + F(0) log tanh(a),
    I(y) = (e^{y/2} * 2 Re F(y) - 2 F(0)) / (e^y - e^{-y}),   c0 = log(4pi)+gamma,

where the tail beyond `y = 2a` (where `F = 0` identically) is the CLOSED
FORM `-2 F(0) int_{2a}^oo dy/sinh y = 2 F(0) log tanh(a)` (the numerator
is `- 2 F 0` there - BOTH terms of `F(y) + F(-y)` vanish - and
`int dy/sinh y = log tanh(y/2)`; an earlier draft of this section dropped
the factor 2, caught by cross-checking against the Lean numerator before
the second probe run), and `I(y) -> F(0)/2` at `y -> 0+` (bounded: the
numerator vanishes to first order because `Re F` is even).  So the WHOLE
gate quantity is: one number `F(0) = ||h_c||^2`, one compact-interval
integral of the autocorrelation, and one explicit tail constant.  A
directed-interval certificate over finitely many boxes is therefore
sufficient in principle - no algebraic sign theorem is needed or expected
(the integrand has no closed-form sign structure).  This retires the
"algebraic sign theorem" alternative of the record-1081 notes for this
carrier.

## 5. Lean landing shape, and the coupling to kernel (b)

B1 (next brick if the fork fires): the carrier family as a named
`CompactLogTest` - `chirpedCarrier (d mu a r)` built from the closed form
of section 3 times a smooth cutoff, with `ContDiff`/`HasCompactSupport`
and strict in-window support (`r < 1`).  ContDiff of the product needs
nothing beyond fun_prop; the object is honest even before any sign claim.

B2 (the correction, in Lean): the tool `exists_residualWindow_correction`
SUPPLIES `w` with prescribed values at the seven nodes, so the five-clause
test is `h_c = sumTest h_0 w` with `w`'s targets equal to `-lap h_0` on
{0, 1/2, 1} and 0 on {rho, -rho, -1/2, -1} - existence is a theorem
already in the library.  The REMAINING inequality is then about an object
containing the abstract `w`, so it needs a STABILITY argument: by the 1082
exact quadratic decomposition, `arch(h_0 + w) = arch(h_0) + arch(cross) +
arch(w)`, and a Cauchy-Schwarz-type bound `|arch(crossTest f g)| <=
C(f) * ||g||` would let the measured margin on the explicit pair absorb
any SMALL correction.  The size of the available correction is exactly
the interpolation-constant question - kernel (b)'s prefix-side wall.  So
the two C3 kernels MEET here: the carrier's stability radius is priced by
the same constant whose uniformity is the prefix wall.  This coupling is
a structural output of this record; no theorem is claimed for it yet.

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
    F-A = G1..G5 all pass at some r: proceed to the B1 Lean carrier brick.
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

## 7. VERDICT (probe-1086h.log, 2026-09-01): F-B fired

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
    G5  FAIL at every r: arch(h_c.convSq) = -2.977252 (r=0.95) /
        -1.544236 (r=0.80) / -0.337002 (r=0.60).

By the letter of the fork this is F-B*-mixed (G3 fails at two tapers,
G4 fails everywhere, not only G5); the substantive F-B condition - G5
fails at EVERY r - holds, and F-B's prescribed consequence is applied:
this carrier family does NOT certify the Lean gate quantity; carrier
work on it is frozen; the attack line is re-examined.

### 7.1 The two independent negatives

Both the gate AND its 1070-dictionary surrogate fail for the legal
(C-infinity) object:

  * G4: the surrogate sign is not robust under legal smoothing.  The
    1079 value fl2 = -1.294 belonged to the hard-truncated object with
    polynomial bumps (mass piled against the window edge, lever 3.8);
    the smooth taper at r=0.95 has lever 0.994 and the surrogate flips
    POSITIVE.  So even a surrogate-only continuation of 1077-1079 has
    no legal witness in this family.
  * G5: the gate quantity itself is negative at every taper, with the
    pieces settling where the negativity lives:

        r      F0       c0*F0    window      tail       arch
        0.95   1.2355   +3.840   -4.1028     -2.7146    -2.9773
        0.80   0.6075   +1.888   -2.0977     -1.3348    -1.5442
        0.60   0.1203   +0.374   -0.4466     -0.2644    -0.3370

        (h_0 alone: arch -4.568 / -3.716 / -2.470; w alone: -0.841 /
        -1.381 / -1.703; h_c exceeds h_0 + w by a POSITIVE residual
        +2.43 / +3.55 / +3.84 - the form is not diagonal on this pair,
        h_0 is neither even nor odd, no 1082 decomposition applies.)

### 7.2 Mechanism (why the gate quantity is negative here)

The structural positive ceiling is c0*F0 + tail =
F0 * (log 4pi + gamma + 2 log tanh a) = +0.91102 * F0 (the tail is
2 F0 log tanh a per the corrected section 4).  Positivity therefore
requires window > -0.911 F0, i.e. the autocorrelation must retain
NEAR-LAG (in-phase) mass: I(y) ~ F0/2 near y = 0 and the deficit is
governed by the relative derivative mass omega^2 (I(0.02) = -6.875
back-solves to omega^2 ~ 6e2).  The chirped Gaussian carries phase
-u^2 mu/(4|lambda|^2) ~ -23.5 u^2 - roughly one full period across the
root window - which is precisely what kills the three Mellin nodes
cheaply in Mellin space and EXPENSIVELY in autocorrelation space: the
gate functional rewards in-phase mass and the chirp destroys it.  The
node-restoring correction w cannot repair this (its own arch is
negative at every r).

### 7.3 What survives, and the re-examination direction

Survives: the closed form (G1, now round-trip-certified), the rig and
its anchor reproduction (G2), the measurement methodology itself
(FFT-vs-brute-force tie 7e-17..9e-16 at every lag, F(0) against
mpmath at rel <= 7e-15, I(y) against mpmath at three y per taper).
UNAFFECTED: records 1063/1067 (the D-weighted F1' routes through its
own functional), the 1084/1085 reduction (kernel (a) asks for SOME
root-window triple-vanishing detecting test, and this family was one
candidate), the prefix-side wall.  RH is NOT claimed, no route death
beyond this family.

Re-examination (record 1087 candidate, to be pre-registered on its
own): arch(h.convSq) is a QUADRATIC FORM in the test h; the
triple-vanishing conditions are THREE linear constraints.  Kernel (a)
is therefore a SPECTRAL question - the top of the spectrum of the arch
form restricted to the codimension-3 subspace V = {h : lap h = 0 on
{0, 1/2, 1}}, supp h in the window - not a carrier-guessing question.
The measured signs show the form is INDEFINITE on the family (both
diagonal pieces negative, residual cross positive), so a positive
direction of arch|_V is not excluded; if the top eigenvalue of arch|_V
is positive with a rho_2-detecting eigenvector (or a generic
perturbation of one), kernel (a) has an explicit optimal witness and
the 1084/1085 gate discharges.  If the top of arch|_V is <= 0, kernel
(a) is FALSE for the log2/2 window and the route must revisit the
radius (a free parameter upstream of the 1080 transport).  Either
outcome is decisive, which is why this is the next brick.

## 8. ERRATUM (2026-09-01, added when record 1087 executed the fork)

Two corrections, neither of which changes this record's F-B verdict;
both were found by the spectral scan and certified by the raw-integrand
re-integration in `1087_c3_roundtrip_cert.py`
(`1087_c3_roundtrip_cert.log`).

1. SECTION 4 TAIL FACTOR.  The closed form's beyond-support tail is

       F(0) * log tanh(a)        (x1)

   NOT `2 * F(0) log tanh(a)` as drafted here.  The numerator's "2" in
   `exp(y/2)(F(y)+F(-y)) - 2F(0)` is correct, but the denominator is
   `exp y - exp(-y) = 2 sinh y`, so the primitive `-log tanh(y/2)`
   already carries that 2; the x2 reading double-paid it.  Corrected
   section 6 G5 values for the three tapers (x1 tail at their true
   supports, F0 as measured there):

       taper r=0.95:  -2.977252  ->  -1.679
       taper r=0.80:  -1.544236  ->  -1.004
       taper r=0.60:  -0.337002  ->  -0.263

   and the section 5 ceiling constant is `c0 + log tanh(r*a)` per F0,
   i.e. +2.010 at the window edge (not +0.911).  Every corrected value
   is still negative: G4/G5 both FAIL exactly as recorded, the F-B
   verdict and the "no legal object of this family" conclusion stand,
   and the surrogate fl2 comparison is unaffected.

2. SECTION 7.3 SPECULATION RESOLVED AGAINST IT.  "The measured signs
   show the form is INDEFINITE on the family ... so a positive direction
   of arch|_V is not excluded" - the non-exclusion was tested and lost.
   Record 1087 scans arch|_V spectrally (both basis families, K to 32,
   six radii to the window edge) and finds the top of arch|_V at
   -0.853 +/- 0.002, negative definite at every resolution, for every
   rho simultaneously.  The fork's second branch fired: kernel (a) is
   numerically FALSE for the log2/2 window, and the pre-registered
   consequence - "the route must revisit the radius" - is executed in
   1087 section 5.4 (certificate extension to the orbit window).  The
   carrier-indefiniteness observation is still true and still useless:
   it never constrained V.
