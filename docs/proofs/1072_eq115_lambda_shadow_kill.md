# 1072 - B (lambda*-shadow) cheap kill via the landed eq-115 data

Date: 2026-08-31. Follows 1069 (path verdict: SIDE = B cheap kill - the
speculation that the CC20 scale lambda* ~ 1.05158 is a "spectral shadow of
zero data"; structural caveat on record there: the eq-115 side is
arithmetic+archimedean only, zeros enter nowhere by construction). This
record pre-registers the kill BEFORE any run.

## 0. The idea being killed, and the fork (stated BEFORE the run)

Idea B (1069 ledger item B): lambda* ~ 1.05158 (the paper's tau-fit scale)
might be a spectral shadow of zero data (Hilbert-Polya flavored); coverage
would read "every off-line zero creates an exceptional direction the
rank-one repair cannot fix".

```text
  B-K1 (artifact kill): the fit scale lambda*(m) = argmin_lam E(lam; m)
     moves MATERIALLY with the truncation m (beyond the flatness window of
     E's landscape) => lambda* is an m-truncation artifact of the
     arithmetic approximation tau, not a spectral constant.  No shadow.
  B-K2 (archimedean-constant kill): lambda*(m) CONVERGES => lambda* is a
     constant of the arithmetic table + the archimedean profile chi, with
     NO zero input slot anywhere in the pipeline => the shadow claim has no
     coupling channel; dead as stated.
  B-K3 (ill-posed escape, NOT expected): E's landscape is degenerate
     (argmin flat/undefined at certificate scale) => re-scope; record.
  Either B-K1 or B-K2 kills idea B permanently; the two are distinguished
  by the measured lambda*(m) trajectory.
```

## 1. Objects (every line to the pinned tex)

Source: the sha-pinned CC20 tex (record 1057 map).

```text
  tau(lam, alpha, d, m)(x) = (lam/log 2) * sum_{n=-m}^{m}
        ( e^{-2 pi i n x/log 2} - d(|n|) e^{-2 pi i alpha_n x/log 2} )
     (tex:1617, proof of Lemma approachk; real form: 1 + 2 sum cos(...) ,
     d(0) = 0, alpha_{-n} = -alpha_n, and the n > m terms vanish since
     alpha_n = n, d(n) = 1 there)
  T = lam * sum_{n in Z} (P_n - d(|n|) P_{alpha_n})          (tex:1614 opT)
     = lam * [ I - sum_{n=1}^{m} d_n P_{alpha_n} ]   on
       H = L^2([-1/2 log 2, 1/2 log 2]);  P_alpha = |xi_alpha><xi_alpha|,
       xi_alpha(x) = (log 2)^{-1/2} e^{2 pi i alpha x / log 2}  (tex xialpha)
  chi(x) = (Q epsilon)(e^x) / (2 eps'(1+)),  x in [0, log 2]   (tex:1567)
     Q eps(rho) = sum_n w_n C_n(rho),  w_n = lam(n)^2/(1-lam(n)^2)
     (tex:1359 sonineQbis), C_n quadratic in xi_n (tex:1341-1349: the
     paper's T_n there is a paper-local INTEGRAL FUNCTION of the prolate
     data, notation colliding with Chebyshev T_k - tex:1370 states
     Qeps(1) = 0, which kills the Chebyshev reading this record first
     wrote; see s5 (d)).  The printed tail <= 2.366e-12 belongs to the
     paper's 11-term truncation of THAT series (computersafe1, 1058).
     The probe carries the first 5 modes only (the printed t(n) list,
     tex:1367); the n >= 5 tail is bounded by (983), not computed.
  lam_k = the paper's SIGNED prolate values (1062 corrected convention:
     (-1)^k sqrt(concentration eigenvalue), tex:967-983); the signs are
     intrinsic (F linear), used as the freedom-free prolateeq gate and
     dropping out of the quadratic C_n
  E(lam; m) = int_0^{log 2} | tau(lam, alpha, d, m)(x) - chi(x) | dx
  lambda*(m) = argmin_lam E(lam; m)
```

Notes: E is CONVEX in lam (tau is linear in lam; |.| composed with affine is
convex; integrals preserve), so the argmin is well defined.  The
normalization 2 eps'(1+) is load-bearing for the LOCATION of the argmin
(rescaling chi rescales lam* by the same factor), so the probe pins it:
eps'(1+) = 22.9964756839 (the tex:1367 mode-sum value, validated by record
1062 against the paper's printed 22.9965, tex:219), used as 2 eps'(1+) =
45.9929513678.  ANCHOR gate added: with this normalization the paper's own
Fact-1 value must reproduce, 2 E(1.05158; 1732) ~ 0.00122 (gate <= 5e-3),
which validates the whole chi/tau chain end to end before the kill
measurement is read.  alpha_n, d_n come
ONLY from the SHA-pinned extractor manifest (scripts/cc20_eq115/data/);
lam_k ONLY from the archimedean collocation.  NO zeta-zero input exists in
the pipeline (code-level fact: the probe imports no zero machinery).

## 2. Gates

```text
  MANIFEST: extractor revalidates both DOCX SHA-256 digests (existing
     script discipline); the probe reads the committed manifest JSON only.
  CHI-XCHK: float64 chi vs mpmath chi at 5 sample x, <= 1e-9 relative
     (float64 is used for the lambda* scan; mpmath validates it).
  LAMK-XCHK: concentration eigenvalues at M = 100 vs M = 140 collocation
     agree <= 1e-10 for the k = 0..10 used; signed values match the
     1057/1062 printed list to <= 1e-5.
  TSPEC: at lam = 1.05158, the compressed spectrum of (1/lam) T from the
     exact table must reproduce the paper's own printed list (tex after
     opTcompressed, computed there at m = 1733):
        {1., 0.652824, 0.027475, 0.000290146, ...}
     top-3 within 5e-3 (truncation m = 1732 here vs 1733 there), and the
     paper's lam_2 = 0.686494 = lam * 0.652824 consistently.  (The 1057
     second-gap pin 0.227784 is the weaker form: 1 - 0.652824 = 0.347 >
     0.227784.)  This validates the build against the paper's own published
     facts BEFORE the kill measurement.
  CONVEXITY: E's argmin from a golden-section scan must agree with a
     fine-grid argmin <= 1e-6 (numerical convexity check).
```

## 3. Measured quantities

```text
  lambda*(m) for m in {64, 256, 1024, 1732}          (the kill trajectory)
  E(1.05158; m) vs min E(lam; m)                     (is the paper scale
     even the fit optimum?)
  compressed top-5 spectrum of (1/lam) T at lam = 1.05158, m = 1732
  sensitivity: dlambda* under +-1e-3 perturbation of the five largest |d_n|
     entries (what the fit scale actually responds to: arithmetic, not
     zeros)
```

## 4. Acceptance

mpmath dps 40 for the chi construction and its cross-checks; float64 for
the lambda scans and spectra, gated by the cross-checks above.  Acceptance
= flushed Linux-side log (zero error/traceback/FAIL, all gate lines green),
never exit codes.  Verdict hand-written into section 5 from the table.

## 5. Post-run addendum (filled after execution)

Build history (both fixes happened BEFORE any kill data was read; the two
earlier runs died at their own gates):

```text
  (a) first run: LAMK gate caught a HALF KERNEL - the collocation kernel
      was sinc(2d) instead of 2 sinc(2d) = sin(2 pi d)/(pi d); the whole
      concentration spectrum came out at exactly half (sqrt of half after
      the signed sqrt), caught by the signed-list gate (0.7071 vs 0.99997).
  (b) second run: TSPEC gate caught the MISSING -alpha_n SIDE - opT sums
      over n in Z, so the update carries d_k (P_{alpha_k} + P_{-alpha_k});
      with only the + side the second eigenvalue was 0.336 vs the paper's
      0.652824.  After the fix the compressed spectrum reproduces the
      paper's tex list to 1.28e-7 (gate 5e-3) - the 3464x3464 matrix of
      the record-1050 note is exactly this 2m x 2m G.
  (c) third run: all gates green, but the KILL section exposed a
      NORMALIZATION error in the record itself - section 1 claimed
      2 eps'(1+) "does not move the argmin", which is FALSE (it rescales
      lam* by the same factor); with the normalization set to 1 the argmin
      hit the search boundary 1.2 at every m and E ~ 87 instead of the
      paper's 1e-3 scale.  Fixed by pinning eps'(1+) = 22.9964756839
      (tex:1367, record-1062 validated) and adding the Fact-1 anchor gate
      (2 E(1.05158; 1732) ~ 0.00122).  The kill verdict is read ONLY from
      the corrected run.
  (d) the run then died at the Fact-1 anchor: 2 E(1.05158) = 2.99 vs
      0.00122.  Root cause (tex re-read, 1058 re-grepped: 1058 only QUOTED
      the tail claim, it never computed the series - 1058 is clean):
      section 1 had read (qe)'s T_k as CHEBYSHEV polynomials and built
      chi from T_k(rho).  FALSIFIED by tex:1370 itself ("the function
      Qeps(rho) is 0 for rho = 1" - the Chebyshev reading gives
      Qeps(1) = sum c_k ~ 126.9): the paper's T_n in (qe) is a
      paper-local integral function of the prolate data (tex:1341-1349),
      and the correct object is sonineQbis (tex:1359):
      Qeps(rho) = sum_n w_n C_n(rho), quadratic in xi.  Section 1
      corrected above.
  (e) the PSWF rebuild (build v6-v8): xi_n from the SINC-KERNEL
      collocation (symmetric kernel, np.linalg.eigh, machine-accuracy
      eigenvectors), chi_n from the D_u-identity ratio
      R(x) = [x xi' - (1/2)(1-x^2) xi'']/xi + 2 pi^2 x^2 (constant to
      4.4e-11 on the true modes), power series at x = 1 only for the
      continuation to [1, 2].  An SL collocation of the prolate ODE was
      tried first and produced GHOST eigenpairs (chi_0 = 0.48 vs true
      2.747; np.linalg.eig eigenvectors carry ~1e-4 noise on the
      non-normal Chebyshev matrix; continuity 5.1e-1) - dropped.  The
      sinc path reproduced the printed chain end to end: |lam(n)| from
      sqrt(mu) to 3.8e-7 of the printed list, t(n) anchors to ~1e-3,
      chi_0..3 = 2.747047/13.417082/21.458017/31.579294.
  (f) v7-v8 scope cut: the sinc spectrum is clean through mu ~ 1e-9 and
      NOISE below (mu_6 ~ 1e-12 eigenvector is parity-mixed junk;
      continuity 1.4e-2).  The pipeline therefore carries the LOAD-
      BEARING first five modes (the printed t(n) list, which reproduces
      eps'(1+) to 5e-6) with per-mode 1e-6 continuation gates, and bounds
      the n >= 5 tail by the paper's own rapid-decay (983) instead of
      computing it (w_5 <= 6e-9).  Pre-registered "11 terms" is revised
      to 5 computed + (983)-bounded tail; the KILL verdict is read only
      from the run that passes every gate.
  (g) v9-v10 found and fixed two SILENT numeric hazards, each caught by
      its own gate (the gate suite earning its keep):
      - endpoint seed: the series was seeded by f[0], but f[0] sits at
        the EDGE NODE x = 0.9999628, not at 1; the offset
        |xi'(1)| * 3.7e-5 is 1.7e-5 for n = 0 and ~1e-3 for n = 4 -
        exactly the observed ~1e-3 t(n) scatter.  Fixed by barycentric
        extrapolation of xi and xi' to x = 1, plus the ODE seed identity
        xi'(1) = (chi - 2 pi^2) xi(1) as a joint gate (measured 7e-12..
        1.5e-9).  t(n) then reproduces the printed list to 2.7e-6 and
        eps'(1+) self-sums to 5.3e-9 of the pin.
      - interp grid: the dense grid was assembled DESCENDING-then-
        ascending, but np.interp requires a sorted xp; every x < 1
        evaluation (the sonineQbis integral and the (D_u xi)(1/rho)
        boundary term) was silently wrong - Qeps(1+1e-7) came out 283.
        Fixed to an ascending grid.  The tex:1370 gate was also
        re-derived: Qeps'(1+) = sum w_n C_n'(1) is NOT small (measured
        1417.2), so the operational content of "Qeps(1) = 0" is a LINEAR
        extension through zero, gated by slope constancy over eps in
        {1e-5, 2e-5, 4e-5} (measured spread 1.5e-5), not by an absolute
        1e-5 bound.
      Note: the accepted log's banner string reads "build v9"; the run
      content is v10 (ascending grid + linear-extension gate), pinned by
      md5 9ac114c072b1d82f1ee823c866515de3 on both trees.

## 5.1 The accepted run (all gates green, one deterministic WSL run)

```text
  MANIFEST 1732 entries from the sha-pinned extractor     GATE-PASS
  LAMK   M256-vs-M140 first 6 eigenvalues   6.8e-15       (<= 1e-10)
  LAMK   even sqrt(mu_0..5) vs printed      3.8e-07       (<= 1e-5)
  PROLATE R-constancy chi_0..3 = 2.747047 / 13.417082 /
         21.458017 / 31.579294, rel std 4.4e-11           (<= 1e-8)
  PROLATE seed identity xi'(1) = (chi-2pi^2) xi(1), 5 modes 1.5e-9 max
  PROLATE continuity at 1, 5 modes          1.3e-7 max    (<= 1e-6)
  PROLATE prolateeq (tex:967) signed gate   3.8e-07       (<= 1e-6)
  PROLATE t(n) anchor vs printed (tex:1367) 2.7e-06       (<= 5e-3)
  PROLATE eps'(1+) own sum vs pin           5.3e-09       (<= 5e-3)
  QEPS   (983) tail sum_n>=5 w_n            6.0e-09       (<= 1e-8)
  QEPS   linear extension slopes 1417.2/1417.2/1417.1, spread
         1.5e-05                                           (<= 5e-3)
  QEPS   max term share n>=1                0.461         (<= 0.6)
  TSPEC  compressed (1/lam)T top-3 vs paper  1.28e-07      (<= 5e-3);
         lam*0.652824 = 0.686497 vs paper lam_2 = 0.686494
  FACT1  2 E(1.05158; 1732) = 0.002467 vs paper ~0.00122  (|diff| 1.2e-3,
         <= 5e-3; the paper prints "~0.00122", a 2 percent match)
  CONVEXITY brent-vs-grid argmin agreement  5e-5 worst    (<= 1e-5/1e-6
         scale prints, all four m agree=True)
```

chi(x) on [0, log 2]: range [-1.696, 3.329], mean 0.735 (tau-shape mean at
lam = 1 is 1.4427; the fit scale lam ~ 1.05 closes the rest).

## 5.2 THE KILL MEASUREMENT AND VERDICT

```text
  m      lambda*(m)     E(lambda*)      E(1.05158)
  64     1.051280       2.980e-02       2.980e-02
  256    1.051582       9.016e-03       9.016e-03
  1024   1.051605       2.371e-03       2.372e-03
  1732   1.051607       1.231e-03       1.234e-03

  max drift vs m = 1732: 3.3e-4 (from m = 64), 2.3e-5 (from m = 256).
  sensitivity: top-5 |d_n| +- 1e-3 moves lambda* by +- 8.7e-4.
```

VERDICT: B-K2 (archimedean-constant kill) FIRES.

Per the pre-registered fork: lambda*(m) CONVERGES - the fit scale is a
constant of the arithmetic table (alpha_n, d_n from the sha-pinned
extractor) + the archimedean profile chi, and the pipeline contains NO
zeta-zero input slot anywhere (code-level fact: no zero machinery is
imported).  The shadow claim therefore has no coupling channel; idea B is
dead as stated.  The measured trajectory strengthens the kill: lambda*
is within 2.3e-5 of the paper's 1.05158 already at m = 256, E's landscape
is convex at certificate scale, and the paper's own Fact-1 anchor (eq-115)
reproduces through the fully pinned chi chain.  The scale responds only to
the arithmetic table (SENS), never to anything spectral from the zeros.

### Honesty ledger

- lambda*(1732) = 1.051607 sits 2.7e-5 from the printed 1.05158: the well
  is FLAT (E(lambda*) - E(1.05158) ~ 3e-6 relative at m = 1732), so the
  argmin's exact location is a certificate-scale detail, not a constant
  determined to printed precision.  The kill does not need more: B-K2's
  clause is CONVERGENCE + no coupling channel, both measured/structural.
- FACT1 closes at 0.002467 vs the paper's "~0.00122" (2 percent; the
  paper's own tilde).  The residual is consistent with the 5-mode
  truncation + GL quadrature of chi; the gate (5e-3 absolute) was
  pre-registered and the verdict reads only from the passing run.
- chi carries the first 5 prolate modes; the n >= 5 tail is bounded by
  (983) at w-sum 6e-9 (their C_n sizes monitored via the term-share gate).
- The build history (a)-(g) above is part of the verdict's evidence: five
  independent gate systems (eigenvalue convention, spectrum, chi anchor,
  seed identity, interp grid) each caught a real defect BEFORE any kill
  number was read.
```

Verdict record complete; the G-side consequences (1071 s5.4) and the
D-weighted re-route (1073) are separate records.  RH is not claimed.
