# Record 2041 — Route A one-copy G8-H: health screen from committed data + interval certificate chain pre-registration

Date: 2026-09-27.

Status: PART 1 = instrument-free reading of committed artifacts (health
screen PASSES, no new measurement). PART 2 = PRE-REGISTRATION of the
four-link interval certificate chain; not executed in this record. No
theorem, no RH claim.

Owner throughout: rho = 0.6 + 40.9187190121475 i (delta = 0.10 at gamma_8),
scale 0.88, K = 30, one-copy G8-H basis of record 2037
(`results/2037_route_a_g8h_basis_comparison.json`), support radius 9.504,
visible prime-power count 1647.

## Part 1 — 1931 health screen (C > 0) from committed artifacts

### 1.1 Family identification (why no new run is needed)

`routea_health_cone_2006.two_copy_family(nodes, scale, gamma)` returns
`(doubled_family, base)` where `base = r94.family_for_ext(nodes, scale,
gamma)` — the exact family the 1994/1996 gates were computed on. Record
2037's one-copy rows use `base_fam`. Therefore the 2037 one-copy owner IS
the 1996 EXT owner class at (gamma_8, 0.88), and the committed 1996 sweep
rows are readings for it.

### 1.2 Committed gate rows (results/1996_gamma78_full_sweep.json, tag G8, scale 0.88)

```text
delta = 0.10:  C = +664.3518622617412   D = -1.111261609813454e+20
                det = -7.669186711873433e+22   spread_C = 2.40e-05
                spread_D = 1.31e-05   n_primes = 1647   routes {A, Ap, B}
                face WIRE1
delta = 0.20:  C = +141.88822142776553  D = -2.4213200677120274e+19
                det < 0, spreads ~2.4e-05, np 1647, {A, Ap, B}
delta = 0.30:  C = +59.789769495595465  D = -1.028560044574353e+19
                det < 0, spreads ~2.4e-05, np 1647, {A, Ap, B}
```

Cross-check against 2037: the D-coordinate at delta = 0.10 reads
-1.11126e+20 (1996, dxi = 0.004 pipeline) against the 2037 one-copy
q_h1 = -1.11119e20 (dxi = 0.004, direct quadratic-form pipeline): agreement
to 6.3e-05 relative, inside the registered refinement spread 8.6e-05. The
two pipelines read the same underlying grouped ICgate(g.square) form.

### 1.3 Verdict

```text
HEALTH SCREEN PASS: C > 0 at all three deltas, D < 0, det < 0, spreads
at 1e-05, three certified routes, np = 1647 <= 4000 (1994 instrument law
satisfied; spread is genuine three-route agreement, not the F52
single-route shape).
```

The 1931 precondition for entering Lean/producer work on this selector is
discharged by committed data. This is a reading, not core progress.

## Part 2 — interval certificate chain (pre-registration)

### 2.1 Target

```text
strict full-line interval upper bound:

    Q(full line) = grouped ICgate(g.square) over all xi in R  <  0

for the one-copy G8-H owner above, with the exact support-derived
visible-prime set (1647 prime powers) and the exact base/correction
coefficient solve of the committed pipeline.
```

This removes record 2038's named premise ("no named interval mechanism"),
converting A-DEAD-CURRENT-CERTIFICATE into either a certified negative
margin or a registered per-link failure. Named hypotheses changed versus
2038 (per AGENTS.md Section 2 reopen rule): new selector basis (2037
one-copy) + this named chain.

### 2.2 Margin accounting (why the chain is plausible)

```text
|Q|              ~ 1.11e20   (both dxi readings)
float spread      = 8.63e-05 relative = 9.6e15 absolute
required          : interval TOTAL width < |Q| = 1.11e20
headroom          : > 4 orders of magnitude

The enclosure does not need to be tight; it needs to be rigorous. The
dominant width contributors to book: the |2 + f| amplification of the
cancelled coordinate (f up to the 1.6e6 class at this family's masses,
record 2014 Section 5 / 2020) must be carried INSIDE the panel widths.
```

### 2.3 The four links, in execution order

```text
L2  SIGNED KERNEL PANEL ENCLOSURE.
    ker(xi) = sigma_arch(2 pi xi)
              + sum_{k in book} 2 Lambda(k)/sqrt(k) cos(2 pi xi log k).
    Prime part: finite sum, 1647 exact-vonMangoldt interval-cosine terms,
    trivially rigorous. Arch part: sigma needs an interval-capable
    representation (elementary-function series with directed rounding;
    sub-task S1 — the arch channel is resolution-stable per record 2029,
    so a validated per-panel series is feasible). Deliverable: per-panel
    interval enclosures of ker over xi in [-40, 40].
    Kill: no interval-capable sigma representation meets the width budget
    (then the chain dies at its cheapest link and the failure is the
    registered no-go).

L3  FINITE-WINDOW QUADRATURE ERROR.
    Per-panel mean-value/FTC bounds with the straddle rule of AGENTS.md
    Section 5 (panels whose enclosure straddles zero get the rigorous
    envelope (q - p) sup|f|, never recursion). Precedent: record 2033 P6
    (20000 panels, 19728 sign-certified, 272 enveloped). Deliverable:
    certified interval for the [-40, 40] window integral.
    Kill: envelope mass exceeds the 9.6e15-class width budget after the
    |2 + f| booking.

L1  SOURCE TRANSFORM + H1 SOLVE, DIRECTED ROUNDING.
    17-dimensional complex solve, gram condition 1.3e6 (committed); mpmath
    interval arithmetic at working precision 40+ digits with iterative
    tightening; the ivmpf endpoint rule of AGENTS.md Section 5 applies.
    Deliverable: interval coefficients feeding L2/L3 enclosures.
    Kill: tightening does not converge below the width budget at feasible
    working precision.

L4  FULL-LINE TAIL, |xi| > 40.
    Assemble the LANDED Gevrey constants (records 1986-1988: explicit
    1/||w||^k decay bounds for this family class) into a per-xi tail bound
    for the actual weight |lb|^{2(N+1)}, N = 0. Uniformity needs k >= 3
    (node-product degree 26; record 2031 law). Deliverable: certified
    interval for the tail contribution.
    Kill: the assembled constant exceeds the width budget (price error in
    the 1986-1988 constants for THIS family — would require a re-derivation
    wave, not a patch).
```

Execution order rationale: L2 + L3 dominate the width; they are also the
links with in-repo precedent (2033 P6 machine). L1 is mechanical. L4
consumes only landed constants.

### 2.4 Instrument obligations (registered, binding)

```text
- Nyquist print: the oscillatory sum resolves log k <= 1/(2 dxi); the
  book needs log k <= 9.504, so dxi <= 0.0526; the chain runs dxi in
  {0.008, 0.004, 0.002} and exhibits the convergence spread (0.008/0.004
  pair already committed at 8.6e-05; the 0.002 pass must agree).
- Interval endpoints through mpf(...) before mpf arithmetic (ivmpf rule).
- Lookup grids must RAISE outside their argument range (soundness rule).
- Acceptance is the log, not the exit code; rows artifact dumped before
  the reading runs; --resume-from must re-measure nothing.
```

### 2.5 Honest scope

```text
- single owner: rho = 0.6 + gamma_8 i, scale 0.88 — a milestone
  certificate (first rigorous full-line signed margin on an actual
  selector), NOT quantifier closure; COVER (uniformity in the
  hypothetical rho) is untouched and stays gated per map 107.
- the owner's zero lists remain the committed known-zero sets
  (under-approximation caveat inherited from the 1980-era owner design);
  completeness is a separate named premise, not claimed here.
- success converts 2038's no-go into a certified premise-removal; failure
  at a named link is a registered no-go with its price. Both outcomes are
  admissible ends under map 006.
```

## Evidence

- `results/1996_gamma78_full_sweep.json` (gate rows; verdict
  gamma_8 HOST_CONFIRMED)
- `results/2037_route_a_g8h_basis_comparison.json` (one-copy rows)
- `results/2038_route_a_one_copy_interval_certificate_audit.json`
- `scripts/routea_g8h_basis_comparison_2037.py`,
  `scripts/routea_health_cone_2006.py` (family identification),
  `scripts/routea_gamma78_full_sweep_1996.py`
- `scripts/fourpoint_interval_mass_2033.py` (L3 precedent machine)

No RH claim.

## Outcome (added 2026-09-27, record 2043)

Part 2 of this preregistration is settled NEGATIVE at its first link:
L2 reads **L2-WIDTH-FAIL** (kernel-side projected total width 1.54e22 /
6.90e21 / 3.51e21 at dxi 0.05/0.02/0.01 = 139x / 62x / 32x of |Q|;
width linear in dxi with constant ~1.29e4, the independent-sum
oscillatory-book coefficient).  The S1 sub-task settled POSITIVELY
(interval sigma, 4/4 anchors contained at width ~2.5e-14).  Links L3/L1/L4
were not reached.  The uniform-panel chain as preregistered here is dead;
the only registered reopen is a certificate-type change (panel-local
quadrature by parts, or adaptive clustering on g), unpriced.  Part 1
(health screen PASS on committed 1996 data) stands.  Full readings and
instrument notes: `docs/proofs/2043_route_a_interval_kernel_width_outcome.md`,
artifact `results/2043_interval_kernel_width.json`.
