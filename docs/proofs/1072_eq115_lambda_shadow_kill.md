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
     Q eps = sum_{k=0}^{10} lam_k / sqrt(1-lam_k^2) T_k(rho)  on rho in [1,2]
     (the paper's own 11-term series; tail <= 2.366e-12, validated by 1058)
  lam_k = the paper's SIGNED prolate values (1062 corrected convention:
     (-1)^k sqrt(concentration eigenvalue), tex:967-983)
  E(lam; m) = int_0^{log 2} | tau(lam, alpha, d, m)(x) - chi(x) | dx
  lambda*(m) = argmin_lam E(lam; m)
```

Notes: E is CONVEX in lam (tau is linear in lam; |.| composed with affine is
convex; integrals preserve), so the argmin is well defined.  The
normalization 2 eps'(1+) is a POSITIVE constant - it rescales E but not its
argmin - so the probe sets it to 1 and records that.  alpha_n, d_n come
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

PENDING.
