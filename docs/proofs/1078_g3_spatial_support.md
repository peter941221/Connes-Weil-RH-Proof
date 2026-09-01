# 1078 - g_3 spatial-support recon: does the pinned detector have a genuine compact radius?

Date: 2026-09-01. Follows 1077 (consumer #2 PINNED for zero #2 numerically: field #4
sign FIRED F-A with a deep sink). This record pre-registers the support recon BEFORE any run.

## 0. Why this slice (the gap under "explicit support radius")

Record 1076 consumer #2 demands *a genuine compact-log detector with explicit support
radius and finite visible-prime set*. Record 1077 delivered an EXPLICIT named closed form,
but it was built in **Mellin space**: `g_3(s) = N' s(1-s)(s-1/2)^2 exp((-d^2+i mu)s(1-s))`
is the *value* of a test at Mellin argument s. The Lean owner, however, is spatial:

```lean
-- ConnesWeilRH/Source/CC20YoshidaConvolution.lean:55
noncomputable def laplaceAt (f : CompactLogTest) (s : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f.test x   -- bilateral Laplace of the spatial φ
```

So `g_3` is only a `CompactLogTest` if its **spatial inverse**

    phi(u) = (1/2 pi i) ∫_{c-iT}^{c+iT} g_3(s) e^{-s u} ds,   c = 1/2,
             = e^{-u/2} (1/2 pi) ∫_{-T}^{T} g_3(1/2 + i t) e^{-i u t} dt

is COMPACTLY supported in the log window `[-log 2 / 2, log 2 / 2]` (and smooth).
On the line s = 1/2+it we have s(1-s) = 1/4+t^2, so g_3(1/2+it) is a polynomial in t times
e^{-d^2 t^2}: its inverse in u is therefore a Gaussian of width sigma ~ sqrt(2)*delta
(modulated by e^{-u/2} and a polynomial) - **Schwartz-decaying, not compact**. This record
measures how much mass sits outside the window and whether truncating to it preserves the
field #4 sign. RH remains unclaimed; this is recon, not yet a Lean route payment.

## 1. What is measured (the deliverable of this slice)

At the fired configuration for zero #2 (cd = 1.50, beta = 0.49 - deepest flip in 1077),
the probe:

1. reconstructs g_3(s) and its spatial inverse phi(u) on a u-grid;
2. profiles |phi|: peak location/width, values at the window edge +-a (a = log 2 / 2) and beyond;
3. reports the L^2 energy OUTSIDE [-a, a] as a fraction of total;
4. ROUND-TRIP self-checks that M[phi](s) = ∫ e^{su} phi(u) du reproduces g_3(s) at the nodes
   {0, 1/2, 1} and interior sample points (guards an inverse-convention bug);
5. TRUNCATES: phi_win(u) = phi(u) * 1_{|u| <= a}, recomputes its Mellin values G(s), and
   re-evaluates the three load-bearing clauses for zero #2 with G in place of g_3:
     - triple-vanishing residual at {0, 1/2, 1};
     - detects-rho: |G(rho_2)| != 0;
     - field #4 sign fl = margin + A - P < 0 (same definition as 1075/1077).

## 2. Fork (stated BEFORE the run)

    F-A (COMPACT ENOUGH / lands cleanly):
       round-trip self-check green AND energy outside [-a,a] is small (say <= ~5%) AND the
       truncated test keeps triple-vanishing within a tight tolerance, detects rho_2, and
       fl < 0 with O(1)-scale clauses still passing.
       => g_3 truncates to a genuine CompactLogTest with explicit support radius a = log 2/2;
          consumer #2's "explicit support radius" is satisfied on the spatial side and the Lean
          named-test landing (the follow-on slice) has a clean, compact object to discharge.

    F-B (SWARTZ ONLY / support genuinely leaks):
       phi carries significant mass outside [-a,a] OR truncation breaks triple-vanishing beyond
       tolerance OR flips the field #4 sign.
       => our pinned g_3 is genuinely non-compact; landing needs either a compactified variant
          (Mellin-space bump multiply = spatial convolution, or residualWindow_correction to patch
          the three nodes) or relaxing the owner to Schwartz tests. Record measured mass + perturbation
          as the price tag that drives the follow-on construction.

    F-C (ANOMALY / not expected):
       round-trip M[phi](s) != g_3(s) at sample points beyond inverse-precision => Bromwich kernel
       or sign convention is wrong; fix before any support claim. Checked first because every other
       reading presumes a sound inverse.

Tolerances: "small mass" and "within tolerance" are reported as raw numbers in the verdict; the fork
branching uses energy-outside <= 5% and node-residual <= 1e-2 * peak |G| as the operational cut, but
the recorded numbers always stand on their own.

## 3. Grids and cost

    cd = 1.50, beta = 0.49   (fired config from 1077; env overrides CD_1078 / BETA_1078)
    delta = cd / gamma_2 ; d^2 = delta^2 ; mu = mu_3*(delta, beta, gamma_2); N' from normalize_family3
    Bromwich t in [-T, T], T ~ 12/delta (e^{-d^2 t^2} decay sets the cutoff), dense grid
    u-grid over [-u_max, u_max], u_max large enough to see several sigma past a
    round-trip + truncation re-eval at j = 2 only (recon, not a scan)

## 4. Gates and acceptance

- Round-trip: |M[phi](s) - g_3(s)| / |g_3(s)| small at s in {0, 1/2, 1} (expect ~0 by construction)
  AND at interior sample points; the node values must agree to inverse precision.
- Energy accounting: inside + outside = total (partition of unity check).
- Acceptance: flushed Linux-side log, zero error/traceback/FAIL, all gate lines green; verdict
  hand-written into section 5 from the printed profile rows.

## 5. What is NOT here

No Lean change yet; GATE 1 mainline untouched; RH unclaimed. The follow-on slice (the actual named
`CompactLogTest` + 4-field discharge) takes its shape from this verdict: F-A -> truncate-and-land;
F-B -> build a compactified variant first.

## 6. Post-run addendum: VERDICT = F-B (literal branch) — sign survives, exact nodes do not

Authoritative log: WSL run, DONE-RC=0, deterministic (re-run reproduced every row bit-for-bit).
Raw rows, verbatim:

    cfg|cd=1.5|beta=0.49|gamma2=21.02204|delta=0.071354|d2=5.091348e-03|N'=4.791613e-05|mu*=0.003553|a=log2/2=0.346574
    GATE|self-consistency|np vs mpmath g_3(1/2+it)|maxrel=9.91e-15  (<= 1e-8)
    profile|peak=3.356384@u=-0.1642
    profile|u=+-a: rel_to_peak = 2.693e-01 (u=+a), 3.844e-01 (u=-a)
    profile|u=1.5a: 1.266e-02 | u=3a: 4.301e-13 | u=6a: 2.165e-17
    energy|total=3.980517|inside[-a,a]=3.846822|outside=0.133695|frac_outside=3.359%
    energy|r95_span=0.3558|a=0.3466|r95/a=1.027
    roundtrip|s=0.3+0.4i|rel_err=5.462e-05 ; s=rho2|rel_err=1.284e-13
    roundtrip|s=0|abs_resid=2.402e-03 ; s=1|abs_resid=3.198e-03 (node residual = grid error of the inverse)
    trunc|margin0=4.318617|P2=1.736144|A=-3.464711|wall=2.582473|lever=3.464718|fl=-0.882238
    trunc|G(rho2)=-0.000946+0.930687j|detects=0.9307 (!= 0)
    trunc|G(0)=1.173e-01|G(1/2)=1.152e-01|G(1)=1.173e-01|rel_to_peakG ~ 1.26e-01
    trunc|wall/lever=0.7454|sink=25.46% of lever|O(1)scale=Y
    => preliminary: F-B   (node clause failed; hand-written verdict follows)

### 6.1 Branch call: F-B, and precisely which clause failed

The operational cut needed energy <= 5% (PASSED: 3.359%) AND node residual <= 1e-2 * peak |G|
(FAILED: 1.26e-01) AND fl < 0 (PASSED: -0.882). So F-B fires on ONE clause: **hard truncation
destroys the exact triple-vanishing**. Mechanism is the uncertainty principle, not a defect:
compactly-supported phi has an ENTIRE Mellin transform, and multiplying phi by 1_{|u|<=a}
smears the three prescribed zeros of g_3 into ~12.5%-of-peak residuals at {0, 1/2, 1}.
Consequence for the reduction: `qw = -archimedeanTerm` REQUIRES exact triple vanishing, so
`fl(truncated) = -0.882` is a ROBUSTNESS datum, not a valid field-#4 evaluation of a detector.

### 6.2 What the run positively established (the load-bearing half)

    quantity                          | value      | reading
  -----------------------------------+------------+------------------------------------------
    energy outside [-a,a]            | 3.359%     | quasi-compact (clause: <= 5%)  PASSED
    effective support r95 / a        | 1.027      | 95%-energy radius overshoots a by 2.7% only
    tail decay                       | Gaussian   | 4e-13 by u=3a — leak confined to [a,1.5a]
    round-trip at rho_2              | 1.3e-13    | inverse convention SOUND (F-C excluded)
    fl after truncation              | -0.882     | sign SURVIVES the 3.4% energy cut
    sink after truncation            | 25.46%     | vs 34.36% untruncated — deep margin remains
    detects rho_2 after truncation   | 0.9307     | detection preserved

So the fear behind F-B's strong form — "truncation flips the sign" — is FALSE. The pinned
detector's positivity has >25%-of-lever slack against a perturbation of the size truncation
actually causes.

### 6.3 Consequence for the route (what consumer #2's landing now looks like)

The construction is **truncate + node-restoring correction**, not truncate alone. The Lean side
already owns the tool for the second step by name: `exists_residualWindow_correction` (via
`fixed_window_finite_mellin_surjective`) proves values at finitely many Mellin points are
prescribable inside the fixed window. The numerical follow-on (1079) is therefore pinned: build
the explicit small windowed correction h supported in [-a,a] that cancels G_win at the three
nodes, and check the 25% sign margin absorbs it (perturbation of rows/A bounded by h's size).
No relaxation of the owner to Schwartz tests is needed on current evidence.

### 6.4 Defect log (all fixed before the authoritative run)

1. `mpf("log(2)")` — mpmath `mpf` parses numeric literals, not expressions -> AttributeError;
   fixed to `mlog(mpf(2))` with `log as mlog` imported.
2. `.im` as ATTRIBUTE on mpmath `mpc` (6 sites) — context method `mp.im(z)` is the proven 1077
   form; fixed via uniform replace.
3. `np.exp(s * ugrid)` with s an mpmath `mpc` — numpy cannot consume mpc; fixed by converting
   to Python complex at the `mellin` entry (the whole truncation pipeline is float64).
4. Unused binding `_tb` renamed `_`. Remaining Pyright note on the `_trapz` shim fallback is
   noise: `getattr(np, "trapezoid", None) or np.trapz` short-circuits on numpy >= 2 and the
   fallback exists exactly where it is needed (numpy < 2).

## 7. What is NOT here (unchanged)

No Lean change; GATE 1 mainline untouched; RH unclaimed. 1078 is support recon + price tag;
the named-`CompactLogTest` landing waits on 1079's corrected object.
