# 1087 - the root-window spectral verdict: arch is numerically negative
# definite on the triple-vanishing subspace, and kernel (a) has no
# positive direction at radius log 2 / 2

Date: 2026-09-01.  Follows 1086 (F-B: the g3 family does not certify the
gate) and executes the re-examination 1086 section 7.3 pre-registered:

    arch(h.convSq) is a QUADRATIC FORM in h; the triple-vanishing
    conditions are THREE linear constraints.  Kernel (a) is therefore a
    SPECTRAL question - the top of the spectrum of arch restricted to
    V = {h : lap h = 0 on {0, 1/2, 1}}, supp h in the window - not a
    carrier-guessing question.  ... If the top of arch|_V is <= 0,
    kernel (a) is FALSE for the log2/2 window and the route must revisit
    the radius.  Either outcome is decisive, which is why this is the
    next brick.

Advances consumer 3 kernel (a) of `RH_MAINLINE_FREEZE.md` by ADJUDICATING
it: the outcome is the negative branch, at a margin so wide that no
carrier, taper, node set, or correction inside the root window can close
the gap.

## 1. What is decided, exactly

Record 1085 made kernel (a) one inequality on one object: the root gate
is satisfiable at an off-line rho iff some

    h,  supp h subset (-a, a),  a = log 2 / 2,
    lap h = 0 on {0, 1/2, 1},   lap h rho != 0,
    0 < arch(h.convSq)

exists.  Detection is ONE further open linear condition, so the feasible
set over ALL rho is controlled by the sign of arch on the whole
codimension-3 subspace V intersected with the window: a positive
direction exists iff arch is positive somewhere on V.  This record scans
that subspace spectrally instead of sampling carriers.

## 2. Protocol

The committed probe `docs/proofs/1020_lane_r_prime_free_spectrum.py`
(byte-identical on the WSL mirror; `cmp`-checked) is RE-USED with zero
code change - like the record-1075 re-use of a committed probe, the
frozen-script rule bars new theorem work, not measurement re-use, and
this run names its consumer explicitly (kernel (a), per the 1086
section-7.3 pre-registration).  For each radius r and basis size K it
builds:

* a sampled basis on [-r, r] from two INDEPENDENT families -
  Legendre profiles times the C-infinity envelope
  `exp(-1/(1-x^2))^p`, p in {1,2,3} (smooth-legal, strictly supported),
  and sine profiles `sin(k pi (x+r) / 2r)` (completeness check);
* the exact triple-vanishing nullspace by SVD of the moment matrix
  `lap b_i (s)`, s in {0, 1/2, 1}, with the repo's Laplace convention
  `laplaceAt f s = int exp(s x) f x` (`CC20YoshidaConvolution.lean:35-56`
  - plus sign, verified before reading any eigenvalue);
* QR orthonormalization of the null functions in the L2 mass, then the
  quadratic-form matrix of `arch(h^2)` by diagonal-plus-polarization
  (every entry is an exact integral-form evaluation, no derivative
  stencils), and `scipy.linalg.eigh` eigenvalues normalized by ||h|| = 1.

Sweep (committed log): r in {0.300, 0.320, 0.330, 0.340, 0.345, 0.346}
(window edge a = log 2 / 2 = 0.346574), K in {8,12,16,20,24,28,32},
Legendre at p in {1,2,3} plus sine - 168 rows in total, EVERY row
flagged "negative definite" with zero exceptions.  The square is
supported in [-2r, 2r], so every row is prime-free (2r < log 2): this
is the window the 1080 pinned spec and the capstone's root-support
clause consume.  The radii chosen are the hard end - arch rises
monotonically with r (the tail `F0 log tanh r` is the only r-dependent
term), so a negative window edge bounds every smaller radius a fortiori
in the resolved section.

## 3. Fidelity audit of the closed form (the law-26/31/32 stack)

The scan evaluates arch through the 1086 section-4 closed form.  Before
booking its verdict, all three convention-sensitive pieces were re-read
from the Lean source and then certified by a DIRECT integration of the
raw integrand (`docs/proofs/1087_c3_roundtrip_cert.py`, run
`1087_cert.log`):

    numerator   F y = exp(y/2) (F y + F -y) - 2 F 0   C1SameOwnerWeil.lean:48
    denominator y   = exp y - exp(-y) = 2 sinh y      SelectedWeilFormula.lean:103
    arch F = ( c0 F 0 + int_{y>0} numerator/denominator ).re

For a real even square the integrand reduces to
`(exp(y/2) F(y) - F 0) / sinh y`, and beyond the square support S = 2r
the numerator is exactly `-2 F 0`, so the analytic tail is

    int_S^inf  -2 F 0 / (2 sinh y) dy  =  F 0 * log tanh(S/2) = F 0 log tanh r.      (x1)

THE TAIL-COEFFICIENT FINDING.  The 1086 section-4 draft recorded the
tail as `2 F 0 log tanh(a)` (x2), justified by "BOTH terms of F(y)+F(-y)
vanish" - true about the numerator but WRONG about the total, because
the 2 of `e^y - e^{-y} = 2 sinh y` was then double-paid.  The 1020 scan
used the x1 form from the start.  `1087_c3_roundtrip_cert.py` decides
the question by numbers, on the actual top eigenvector of the scan at
the window edge (sine basis, r = 0.346, K = 32):

    top eigenvalue (matrix)     = -0.85351242
    closed form (scan, tail x1) = -0.85351242
    DIRECT raw-integrand arch   = -0.85345597
    Ga  |closed - direct|       = 5.6e-05   <= 2e-4   PASS
        (the residual is the scan's first-cell grid sliver: its body
        quadrature starts at y = step; for this high-frequency direction
        the integrand runs O(1e2) over the first step)
    Gb  |x2-tail variant - direct| = 1.10   >= 0.5    PASS
        (the probe-style x2 tail misses by O(1) - rejected at four
        orders of magnitude above the noise floor)
    law-31 tie (FFT vs linear correlation) = 6.7e-16
    node residuals at {0, 1/2, 1}  <= 1.1e-17
    gram condition = 1.0,  orthonormality error 7.8e-16
    |lap h rho2| (top direction)   = 0.579936

So the scan's numbers are Lean-faithful up to 1e-4, and the tail
coefficient is settled in favor of x1.  Consequences:

* `AGENTS.md` law (32) stated the correction in the WRONG direction and
  is amended in place (see that section; the law now says exactly what
  to re-derive and how to certify it).
* The 1086 G5 values each sat `|F0 log tanh(r a)|` too negative.
  Corrected with the x1 tail at their true supports:
  arch(h_c) = -1.679 (r=0.95) / -1.004 (r=0.80) / -0.263 (r=0.60);
  the 1086 ceiling constant is `c0 F0 + F0 log tanh(r a)`, which at the
  window edge is 3.10824 - 1.09861 = 2.00963 * F0 (not +0.911 * F0).
  EVERY corrected value remains negative: 1086's F-B verdict stands
  under its own erratum, and an erratum note is appended there.
* The margin of THIS scan moves by at most 1.1 units in the direction of
  MORE negativity under the x2 reading; the x1 reading is the certified
  one and still leaves 0.85 of gap.  The verdict is convention-stable.

## 4. Result: negative definite at every radius, every basis, every K

The log's `eig` column prints [lowest, HIGHEST] of the resolved section
(the scan-log header states this convention verbatim: "eigenvalues are
arch(g^2) on L2-unit triple-vanishing roots").  The quantity that
decides kernel (a) is the HIGHEST one - a lower bound on
`sup_V arch / ||h||_2^2` from one K-dimensional section.  Raw
representative rows (reproduced from the 168-row scan log; the log file
itself is local evidence - `*.log` is git-ignored by repository
convention, and the reproduction command in section 7 regenerates it):

    r=0.34600 square=0.69200 sin K= 8 p=1 null= 5 eig=[-1.70298685, -0.87577377] condG=1.00e+00 resid=2.97e-17 OK negative definite
    r=0.34600 square=0.69200 sin K=32 p=1 null=29 eig=[-3.13221912, -0.85348429] condG=1.00e+00 resid=5.55e-17 OK negative definite
    r=0.34600 square=0.69200 leg K=32 p=1 null=29 eig=[-3.62280018, -0.89138582] condG=5.91e+10 resid=4.34e-12 OK negative definite

Aggregated top eigenvalues:

    r       sin K= 8   sin K=32   leg p=1 K=32   leg p=3 K=32
    0.300   -1.01879   -0.99654   -1.03441       -1.08440
    0.320   -0.95410   -0.93184   -0.96972       -1.01972
    0.330   -0.92325   -0.90098   -0.93887       -0.98887
    0.340   -0.89332   -0.87103   -0.90893       -0.95894
    0.345   -0.87868   -0.85639   -0.89429       -0.94431
    0.346   -0.87577   -0.85348   -0.89139       -0.94140

Two clean monotone patterns, and no third reading available:

* INCREASE with r: arch rises as the window widens (the r-dependence is
  exactly the tail term `log tanh r`), so 0.346 - the largest radius
  still prime-free - is the BEST case.  It is still negative by 0.85.
* INCREASE toward a plateau in K: at r = 0.346 the sine top eigenvalue
  goes -0.87577, -0.86630, -0.86138, -0.85832, -0.85621, -0.85467,
  -0.85348 (K = 8..32, step 4): increments +0.0095, +0.0049, +0.0031,
  +0.0021, +0.0015, +0.0012 - geometrically damping, converging to
  about -0.852, NOT climbing to zero.  The Legendre p=1 sections rise
  the same way but slower (-0.94834 at K=8 to -0.89139 at K=32),
  because the envelope tilts its basis away from the high-frequency
  directions the top of arch|_V occupies; leg p=1 at K=32 and sin K=32
  bracket -0.85 from below with 0.038 between them, and leg p=2/p=3
  interleave.  On numerical health: every sine row has Gram condition
  exactly 1.0 (the sine basis is already near-orthogonal) with node
  residuals <= 1e-16, and leg p=1 residuals <= 1.2e-11 - the two
  families whose bounds matter are the well-conditioned ones; the
  high-envelope leg p=3 rows carry condG up to 8.2e+15 and residuals
  up to 3.8e-09 and their bounds are correspondingly weaker, which costs
  nothing since they sit 0.09 BELOW the sine bounds already.  The
  certified path (section 3) was run on the r=0.346 sine K=32 row, the
  best AND the cleanest.

So the two basis families, six radii, seven sizes, three envelope
powers - 168 independent lower-bound computations - all report the same
capped sup, and none reports anything even within 0.85 (per unit L2
norm) of the gate `0 < arch`.

Logically precisely: a K-section compression gives only a LOWER bound
on `sup_V`, so what the sweep establishes numerically is

    sup_{h in V, ||h||=1} arch(h.convSq) ~= -0.853   (window edge),

with the sine sections rising monotonically toward that plateau and no
sign of the 1/K-tail needed to reach 0 within the resolution tested.
A rigorous UPPER bound on V would need a validated spectral-gap
argument, and this record does not attempt one.  What it does give is
the pre-registered decision quantity: the fork in 1086 section 7.3
asked whether the top of arch|_V is <= 0 or > 0, and every probe -
8 basis sizes to K=32, 2 independent families, 6 radii up to the hard
window edge - says the top sits at MINUS point eight five, a full 0.85
below the gate, growing more negative as the window narrows.
Adjudication (negative branch): the feasible set of kernel (a) is
numerically EMPTY - not for a family of carriers, but for the whole
subspace, for every rho.

## 5. What the verdict closes, and why it is structural

1. THE PINNED-DETECTOR PROGRAM (records 1077-1086) is closed as a
   strategy, not frozen as a family.  Every object it can produce lies
   in V; V admits no arch > 0 direction; the 1085 bridge
   `HealthyYoshidaDetectorData rho g <-> 0 < arch h.convSq` therefore
   has an unsatisfiable right side at the root radius.  No taper, no
   node placement, no correction w, no eigenvector certificate can
   change this, because they all quantify over the same V.  Carrier
   search inside the root window must STOP, not continue harder.

2. THE TRANSPORT ROUTE IS ALSO CLOSED, and this is the larger
   consequence.  Record 1081 section 3 isolated the remaining
   root-support obstruction on the prefix side and called uniform
   interpolation-constant control "real open mathematics".  The scan
   makes that wall pointless to climb: transport would have to deliver
   some h in V_root with arch(h) > 0 (the gate it must preserve is
   exactly what V_root forbids).  The room the prefix wall guards is
   empty.  Kernel (b) (the prefix-side interpolation-constant question)
   is retired as a C3 attack line - NOT solved; ruled irrelevant for
   root-window transport.  The damper-free tail theorem of 1081 stands
   and remains useful for the larger-window route below.

3. THE SIGN IS RH-CONSISTENT, which is what makes the negative branch
   the EXPECTED one - and this is the deep point of the record.  The
   very mechanism that makes `0 < arch` the DETECTION gate (1080/1084)
   is a sign weight on the zero side: a test in V inside the prime-free
   window has zero pole and zero visible-prime contributions, so the
   same-owner explicit formula pins `arch` to the signed zero sum alone
   - a sum whose weight is NEGATIVE on the critical line and positive
   only for off-line zeros (which is exactly why the library theorem
   `exists_healthyDetectorData_of_sourceNontrivialZero_right` supplies
   arch-positive detector data UNCONDITIONALLY from an off-line input).
   If every zero is on the line, every surviving term is negative:
   arch < 0 on ALL of V.  The scan's finding - a negative top of
   arch|_V at the window with no positive direction visible at any
   resolution - is therefore what an RH world MUST look like from this
   instrument.  Consequence: the root-window gate is not a
   construction problem at all; producing h in V_root with arch > 0 is,
   through this same identity, an OFF-LINE ZERO WITNESS, i.e. evidence
   of ¬RH - so it cannot be a lemma toward RH.  The 1077-1086 program
   was (its records did not see this) a ¬RH witness search whose
   success sign was pre-decided against it.  The 0.85 margin is
   numeric, not a theorem, but it is a margin in the direction RH
   predicts, and the pre-registered 1086 fork was won by the branch
   that RH makes inevitable.  This is why re-anchoring (item 4) moves
   the radius, not the sign search.

4. THE ONLY SURVIVING SHAPE OF CONSUMER 3 (the fork's prescribed
   radius revisit).  The radius enters the feasibility question through
   exactly one gate: prime visibility.  2r < log 2 keeps primes away
   and, per this scan, keeps arch negative on the vanishing subspace;
   past 2r > log 2 the test sees p = 2 and the vanishing set grows by
   the visible-prime clauses - which is precisely the shape the freeze
   and `docs/map/003` already authorize:

   > consumer 2: "healthy detector support and finite visible-prime
   > ownership"; the B5 shape "may use the detector's support radius to
   > select a finite set of visible primes".

   The unconditional detector data ALREADY EXISTS for right-oriented
   off-line zeros (1081 section 1, `exists_healthyDetectorData_of_
   sourceNontrivialZero_right`) on the n-fold orbit support; what the
   capstone lacked was the matching `0 <= qw` certificate at THAT
   window.  The re-anchored consumer 3 is therefore: extend the
   ROOT-local CC20 certificate package outward to the orbit window
   W_n = Ioo((n+1) baseLower + lower, (n+1) baseUpper + upper) by the
   FINITE visible-prime readback
   `{p^k : k log p <= rad(W_n)}` - grow the certificate to the
   detector's support instead of shrinking the detector to the
   certificate's support.  That is the same local base, the same
   owner, a finite number of extra signed prime terms, and a nonempty
   feasible set (the orbit detector's arch positivity is exactly what
   the library theorem supplies unconditionally, at the orbit radius).

   The next record (1089 design; 1088 was consumed by the endpoint audit
   that became map record 004) should concretize: the explicit n = 1
   window radius from `C1HealthyYoshidaUnscaledOrbit` /
   `exists_nearbyZero_unscaled_targetValues_assembly_of_fixedThreshold`,
   the finite visible-prime set it exposes, and the certificate
   extension statement `0 <= qw g` at that window as a named consumer.
   A follow-on scan of arch|_V with the visible-prime vanishing rows
   added (a constrained nonlinear problem: `F(log 2) = 0` is QUADRATIC
   in h, unlike the linear Mellin rows) can price how far outward the
   positive region reaches, but no theorem claim is attached to that
   idea here.

## 6. What is NOT here

No Lean theorem is proved from this scan and none is attempted: a
numerical spectrum is not a certificate.  RH is NOT claimed; the
negative-definite observation is a consistency check, and the record's
weight is the STRATEGIC re-anchor (sections 5.1-5.4), not the
arithmetic.  The 1080-1085 chain of reductions stands unchanged as
theorems; they simply discharge onto a set this scan shows to be empty
at the root radius.  The tail-erratum amendment leaves 1086's F-B
conclusion intact.  Frozen namespaces received no theorem work; this
record's numerical scan has the named consumer required by the freeze
(the 1086 section 7.3 pre-registration of kernel (a)'s spectral fork).

## 7. Evidence and reproduction

* Scan log (committed): `docs/proofs/1087_c3_root_window_spectrum.log`
  (the 2026-09-01 WSL run through `scripts/run_resource_aware_task.sh` in
  the Linux-side verification mirror of the repository, using the
  project's SciPy 1.18 virtual environment - environment locations are
  operational detail owned by `AGENTS.md` section 7a and are not repeated
  here).
* Fidelity certification script (committed):
  `docs/proofs/1087_c3_roundtrip_cert.py`; its run log is local evidence
  (`*.log` git-ignored) - the final block of its stdout, reproduced
  verbatim as the record's primary certificate evidence:

      Ga |closed-direct|=5.645e-05 <= 2e-4  ->  True
      Gb |x2-variant-direct|=1.100e+00 >= 0.5  ->  True
      VERDICT PASS Ga+Gb: scan closed form (tail x1) reproduces the direct
      Lean-integrand integration within the first-cell sliver; the 1086 g/h
      tail x2 variant misses by O(1) and is rejected - the factor 2 in the
      numerator is already paid by 2*sinh(y)
* Reproduce the scan:

      python3 1020_lane_r_prime_free_spectrum.py \
        --radii 0.30 0.32 0.33 0.34 0.345 0.346 \
        --basis-sizes 8 12 16 20 24 28 32 \
        --envelope-powers 1 2 3 \
        --basis-families legendre sine

  (plus the smaller-radius default sweep; committed 1020 script is
  byte-identical to the one that produced the log - `cmp` PASS).
* Reproduce the certification:

      cd docs/proofs && python3 1087_c3_roundtrip_cert.py

  Requires numpy/scipy (the project SciPy 1.18 environment); prints
  Ga/Gb two-sided gates and the law-31 tie.
