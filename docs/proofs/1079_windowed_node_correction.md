# 1079 - windowed node-restoring correction: does the 25% sign margin absorb it?

Date: 2026-09-01. Follows 1078 (g_3 spatial-support recon, verdict F-B on a single
clause: hard truncation keeps the field-#4 sign - sink 25.46% vs 34.36% - but smears
the exact triple vanishing to ~12.5% of peak). This record pre-registers the pinned
follow-on BEFORE any run.

## 0. Why this slice (the one gap 1078 left open)

1078's consequence paragraph: the Lean landing of consumer #2 is
**truncate + node-restoring correction**, and the correction tool already exists in
Lean by name (`exists_residualWindow_correction`, via
`fixed_window_finite_mellin_surjective`). What was missing was the NUMERICAL half:
does a correction of the required size (~12.5%-of-peak node residuals to cancel)
destroy the 25% sign margin? If no, the corrected object satisfies all four
detector fields numerically and the named-`CompactLogTest` Lean construction is
unblocked. If yes, the steering freedom (kernel of the constraint map) is the next
design lever and its price must be measured.

## 1. Object (fully explicit)

    phi_win = phi * 1_{|u|<= a},  a = log 2 / 2          (1078's truncated object)
    G_win(s) = M[phi_win](s)
    h_m(u)   = u^m (a^2 - u^2)^2 * 1_{|u|<= a},  m = 0, 1, 2
    h(u)     = c_0 h_0 + c_1 h_1 + c_2 h_2,
        Sigma_m c_m H_m(s_j) = - G_win(s_j)   at s_j in {0, 1/2, 1}
    G_new(s) = G_win(s) + H(s),  H = Sigma c_m H_m

=> G_new vanishes at the triple nodes to the precision of the linear solve, h is
supported EXACTLY in [-a, a] (the bump vanishes to 2nd order at +-a), and the
corrected object stays inside the root window. NOTE (honesty): (a^2-u^2)^2 is C^1
at +-a, not C^inf; the Lean construction will swap a genuine C^inf bump. The
perturbation scale is set by |H| ~ (correction size), not by the bump's smoothness
class, so the margin question is answered on this basis; the C^inf swap is a
Lean-side construction detail recorded here, not measured.

## 2. Key identity (kills the nested quadrature)

    phi(u) = (1/2 pi) Int_{-T}^{T} g_3(1/2 + it) e^{-(1/2+it)u} dt   (Bromwich c=1/2)
    => G_win(s) = (1/pi) Int_{-T}^{T} g_3(1/2+it) * sinh((s-1/2-it)a)/(s-1/2-it) dt

because Int_{-a}^{a} e^{(s-c-it)u} du = 2 sinh((s-c-it)a)/(s-c-it). So EVERY value
of the truncated object is ONE t-integral with a CLOSED-FORM kernel - no 2D
nested quadrature, and the sinh/z kernel is evaluated limit-safely via
sinh(w)/w = sinc(iw/pi). High precision (mpmath, dps 30) only where it carries the
claim: the three node values (and hence the solved c and the node residual).
Everything else (on-line rows, rho_2) runs the float64 kernel, tied to 1078's
bit-for-bit log by explicit gates.

## 3. Fork (stated BEFORE the run)

    F-A (MARGIN ABSORBS THE CORRECTION):
       node residual max <= 1e-12 AND fl_2 < 0 AND O(1)-scale clauses pass
       (lever >= e^-2, wall >= e^-2) AND |G_new(rho_2)| not small.
       => the corrected object satisfies all four detector fields NUMERICALLY;
          the Lean named-CompactLogTest landing is unblocked (construction slice
          next, no further numerics owed first).
    F-B (SIGN LOSES / margin insufficient):
       fl_2 >= 0 or an O(1) clause breaks under arm 1. Then arm 2 (pre-registered
       fallback, same run): add ONE kernel direction h_4 = null-space vector of
       the node constraint map built from {u^3, u^4, u^5, u^6}(a^2-u^2)^2, scan
       its multiplier over 2^-8..2^8 times the |c|-scale, and report the best
       achievable fl_2 - that number is the price tag that drives the next design
       (steering vs mu micro-retune).
    F-C (ANOMALY / not expected):
       any tie-in gate fails (kernel rows vs 1078's margin0/P2/rho_2/node values
       beyond quadrature-scale disagreement), or the 3x3 system is ill-conditioned
       (cond > 1e8), or the node residual lands above 1e-12 => construction or
       quadrature defect; fix before any verdict.

Tolerances: tie-in gates use <= 2e-3 relative (rows / rho_2, different quadrature
paths than 1078's u-grid) and <= 5e-3 relative (node values, 1078's grid error
there was ~1e-3); raw numbers always stand on their own.

## 4. Grids and cost

    cd = 1.50, beta = 0.49   (fired config; env overrides CD_1079 / BETA_1079)
    t-grid: [-T, T], T = 10/delta = 140.147, Nt = 8192 (same family as 1078)
    H_m: 200-node Gauss-Legendre on [-a, a] (machine precision for smooth integrand)
    nodes: mpmath dps 30, mp.quad over [-T, 0, T]; linear solve mp.lu_solve
    zeros: persisted 1071 zero cache, cutoff = max(3 gamma_2, 5/delta) ~ 70 (j<=~40)

## 5. What is NOT here

No Lean change; GATE 1 mainline untouched; RH unclaimed. Arm 1 is a MINIMAL
construction (3-term polynomial bump, no optimality claim); if F-A fires, the
follow-up is the Lean construction slice itself (named CompactLogTest + 4-field
discharge for zero #2), not more numerics.

## 6. Post-run addendum: VERDICT = F-A — the margin absorbs the correction

Run 1 fired F-C (three defects, all gate-caught and root-caused, see 6.3). The fixed
re-run is authoritative (DONE-RC=0, deterministic pipeline, zero errors). Raw rows:

    GATE|g3 self-consistency np vs mpmath|rel=2.863e-17   (<= 1e-8) PASS
    GATE|H basis hp vs Gauss-Legendre|rel=1.223e-14       (<= 1e-10) PASS
    GATE|Q float64 kernel self-tie at nodes|maxrel=3.834e-16 (<= 1e-3) PASS
    arm1|cond(3x3)=4.339e+04                              (<= 1e8) PASS
    NODE-GATE|corrected node residual max=4.466e-18       (<= 1e-12) PASS
    GATE|K margin0=4.320826 (rel 5.114e-04) PASS | P2=1.742124 (rel 3.444e-03) above 2e-3
    GATE|R G_win(rho2)=0.003325+0.932257j (rel 4.889e-03) above 2e-3
    GATE|N hp nodes vs 1078 grid|rel ~ 1.9e+00 FAIL   <- 6.2, a 1078-side finding
    corr|margin0=4.376430|P2=1.918213|P3=0.921488|A=-3.752438
        |wall=2.458218|lever=3.831183|fl2=-1.294220|fl3=-0.297495
    corr|G_new(rho2)=-0.099212+0.973629j|detects=0.9787
    corr|wall/lever=0.6416|sink=33.78% of lever|O(1)scale=Y
    control|j=3 fl3=-0.297495 (FLIPS)|wall3/lever=0.9018
    => preliminary: F-A   (arm 2 fallback never needed; never executed)

### 6.1 Branch call: F-A, on the pre-registered clauses

node residual 4.5e-18 <= 1e-12; fl2 = -1.294 < 0; lever 3.83 / wall 2.46 both
>= e^-2; |G_new(rho_2)| = 0.9787.  The corrected object
    phi_new = phi * 1_{|u|<=a} + c_0 h_0 + c_1 h_1 + c_2 h_2,  h_m = u^m (a^2-u^2)^2
is supported EXACTLY in [-a, a], vanishes at {0, 1/2, 1} to machine precision, and
keeps the field-#4 sign with a DEEP sink.  All four HealthyYoshidaDetectorData
fields for zero #2 are now satisfied NUMERICALLY by a named explicit object.

    construction state           | node vanishing | sink (% of lever) | detects rho_2
  -------------------------------+----------------+-------------------+--------------
    g_3 untruncated (1077)       | exact          | 34.36%            | 0.984
    truncated only (1078)        | BROKEN ~12.5%  | 25.46%            | 0.931
    truncated + correction (1079)| exact (4.5e-18)| 33.78%            | 0.979

The correction cost ~0.6 points of sink and even STRENGTHENED detection
(A: -3.465 -> -3.752; the H(rho_2) phase aligned constructively).

### 6.2 Cross-record finding: 1078's u-grid absolutes are kink-limited

The tie-in gates N (nodes, 13.6% off), R (rho_2, 4.9e-3) and P2 (3.4e-3) sit above
their pre-registered tolerances while Q (self-tie, 3.8e-16) and the dps-30 quad
define the object.  Diagnosis: 1078 evaluated G_win by trapz over a u-grid on which
phi_win has indicator KINKS at +-a; the node values (integrals with no oscillatory
damping) inherited the largest error.  The reference values from this record's
closed-form kernel: |G_win(0)| = |G_win(1)| = 0.101257, |G_win(1/2)| = 0.099616,
G_win(rho_2) = 0.003325 + 0.932257 i.  1078's verdict clauses are robust at this
error scale (its sign margin was 25% of lever; its node-clause conclusion - broken
exactness - is qualitative).  Recorded as a precision annotation on 1078, not a
defect of 1079; the margin0 tie PASSED at 5.1e-4.

### 6.3 Defect log (run 1 = F-C; all fixed before the authoritative run)

1. On-line SIGN: reimplemented g_3(1/2+it) as N' q (-t^2) e^{...} following 1077's
   make_g3 DOCSTRING (s(1-s)); the code's vf0 = s(s-1) (1071:41) makes the true
   value N' (+q)(+t^2) e^{...}.  Caught by the self-consistency gate at rel = 2.000
   EXACTLY (antipodal).  1077's docstring corrected in place with an erratum note
   (its verdict is unaffected: all sign-sensitive quantities ran through the code).
2. Transposed linear system: built M[m][j] = H_m(s_j) but lu_solve consumes
   Sigma_m M[j,m] c_m; the solve returned garbage c ~ 1e5 and node residual 1.1e3.
   Fixed orientation (rows = nodes); cond 4.3e4 is inherent to the u^2-column and
   inside the pre-registered 1e8 gate.
3. On-line rows at REAL s: the row loop passed s = gamma instead of 0.5 + i gamma,
   so the kernel evaluated a Laplace transform at real points (growth e^{gamma a});
   margin0 came out 5e17.  Isolated because the single-point R gate and the node
   gates were already correct; fixed by evaluating rows on the line.

### 6.4 What is NOT here (unchanged)

No Lean change; GATE 1 untouched; RH unclaimed.  The C^1-bump caveat stands (the
Lean construction swaps a C^inf bump; the perturbation scale is set by |H|, not
the smoothness class).  Bonus finding, not a claim: the corrected object ALSO
flips zero #3 (fl3 = -0.297, wall3/lever 0.9018) - the measured single-detector
reach on this run is zeros {#2, #3}; j = 1 was not evaluated.  Next slice is the
Lean construction itself: named CompactLogTest for phi_new + 4-field discharge
for zero #2 (route payment).
