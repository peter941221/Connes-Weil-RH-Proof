# 1398 — Preregistration: rung-3 joint-witness rig (A(g) on the route-alpha owner at (J1)-PASS cells; MODEL evidence, one-sided)

Date: 2026-09-13. Law 42: committed BEFORE any rung-3 digit; a model,
grid, gate, or tolerance change after the first run costs a NEW prereg.
Law 65: every number this rig produces is MODEL — an evaluation of the
transcribed pipeline, never a Lean digit.

**Lineage.** Follows [1397](1397_rung3_archimedean_sign_recon.md) (the
source-only recon: gate form, owner shape, 1080-1087 inventory, the
sup-lower-bound law that makes negative scans non-falsifying) and
[1395](1395_009_contract_closed_ledger_state.md) section 3 (the six-rung
table; this rig attacks rung 3). The (J1) input is the committed
[1393](1393_component5_route_A_prereg_v3_instrument_fix.md) model re-decoded
from the [1394](1394_component5_rig_v3_valid_j1_realizable.md) artifact. The
owner is the 1391 `C1RouteAlphaOwner` pipeline.

## 0. What this rig decides, and what it does not

```text
DECIDES (one-sided)  JOINT WITNESS: does any tested owner geometry
   (Rf, Ru, eps, eps', rho) carry BOTH
     (i)  at least one (J1)-PASS cell in the committed 1393/1394 grid
          (rung 2, MODEL band), and
     (ii) A(g) > 0 under the locked model of sections 1-3 (rung 3, MODEL)?
   A POSITIVE is constructive MODEL evidence that rungs 2 and 3 are
   simultaneously satisfiable on ONE explicit route-alpha owner.

KILLS NOTHING        A negative or absent witness does NOT falsify route
   alpha, the archimedean gate, rung 3, or anything else: the tested set
   is a finite deterministic shortlist and, per the 1087 law quoted in
   1397 section 3, "a negative value cannot prove that the full supremum
   is nonpositive." Section 6 carries this in full.

DOES NOT             discharge `0 < archimedeanTerm g.convolutionSquare`
   in Lean (rung 3 needs a PROOF, this is arithmetic); produce detector
   data (rung 4 consumes the FORMAL term, not a model formula); touch
   the Weil criterion (rung 5, the wall, B0b-iff-SourceRH); or certify
   RH in any direction. Every rho is a HYPOTHETICAL off-line zero.
```

## 1. Locked model — the route-alpha owner pipeline, transcribed from source

### 1.1 Register (verbatim 1393 sections 1.1-1.2, same alignment)

```text
nodes rho  = healthyDetectorNodeSet rho = {0, 1/2, 1, rho}      (4 nodes)
             (C1HealthyYoshidaMinimalInterpolation.lean:27-28)
ordered list  s = (0, 1/2, 1, rho);  u (window (-Ru, Ru)): p_u = (1,1,1,1)
f (window (-Rf, Rf)): p_f = (0,0,0,-1)   (healthyDetectorNodeTarget, ibid.:32:
             -1 at the rho entry, 0 elsewhere — per-node, not per-position)
laplaceAt h z = integral x, exp(z*x) * h.test x      (CC20YoshidaConvolution
             .lean:55-56: NO conjugation on z)
value law   laplaceAt g rho = laplaceAt u rho * laplaceAt f rho = 1 * -1
hard support  Rg = Ru + Rf <= log 2 / 2 = 0.34657...; every candidate
             geometry satisfies Rf, Ru in the locked RADII (1393 section 2),
             so Rg <= 0.3464 and supp F = supp(g~ * g) lies in (-2Rg, 2Rg)
             with 2*Rg <= 0.6928 < log 2: the finite-prime sum is EMPTY
             (1397 section 1) and A(g) alone decides the sign of qw.
Re rho >= 0.55, Im rho > 0 by grid construction.
```

### 1.2 Per-factor solve (f: R = Rf, eps, p = p_f; u: R = Ru, eps', p = p_u)

All steps are the `exists_windowTaperCorrection_cost_le_one_plus_eps`
construction re-read this session; the rig must emit every intermediate
named here.

```text
(a) G = windowExpGramMatrix (-R) R nodes:
      G_ij = 2*sinh(A*R)/A,  A = s_i + conj(s_j);  branch A = 0 -> 2R
      (C1WindowMellinGram.lean:47-53; branch discipline per 1393 section 1.3)
(b) alpha := lambda_min(G) — G is Hermitian and the formal gap constant of
      Lift.lean:239-266 is the minimum of the unit-sphere energy, i.e.
      lambda_min. LOCKED CONVENTION: the model takes alpha = lambda_min
      (the maximal admissible gap constant). Sensitivity variant (section 3,
      GT): tier-1 re-run with alpha -> alpha/2, reported, no verdict weight.
(c) TB := windowTaperBound (-R) R nodes = sum_i exp(|s_i| * R)
      (C1WindowTaperLift.lean:141-143; |s_i| the COMPLEX modulus — at
      Im rho = 1054, R = 0.02 this is exp(21.08) ~ 1.4e9: TB is huge and
      feeds (d) squared)
(d) Delta := eps * alpha / (4 * (1 + eps) * TB^2)         (Lift.lean:700)
    delta  := min(R/2, Delta)                              (Lift.lean:705)
    rIn    := R - delta;  rOut := R - delta/2              (Lift.lean:711-712)
    (m = 0 for symmetric windows; Lift.lean:695-696)
(e) tapered Gram, LOCKED REDUCTION (see 1.3 for S, J):
      T_ij = 2*sinh(A*rIn)/A  +  (delta/2) * ( exp( A*rIn) * J( A*delta/2)
                                             + exp(-A*rIn) * J(-A*delta/2) )
      with A = s_i + conj(s_j), branch A = 0 -> 2*rIn + delta/2
      (each sliver carries (delta/2)*J(0) = delta/4)
      (identity of the formal T_ij = integral_{-R}^{R} tau*e^{A x}: plateau
      + two transition slivers; derived in 1385's shape layer, re-derived
      numerically here to make delta ~ 1e-24 EVALUABLE — section 1.4)
(f) coeff := T^{-1} p   (exact mp 200-bit Cramer solve; formal coeff :=
      mulVec hT.unit^{-1} y, Lift.lean:763-769)
(g) factor(x) = tau(x) * sum_i coeff_i * exp(conj(s_i) * x)
      (windowTaperComb Core.lean:50-52; windowTaperCorrection_apply
      Lift.lean:419-423)
```

### 1.3 The taper in closed form (Mathlib pointwise chain, transcribed this session)

```text
S(t) := Real.smoothTransition t = e(t) / (e(t) + e(1 - t))     (Mathlib
        Analysis/SpecialFunctions/SmoothTransition.lean:146-147)
e(t) := expNegInvGlue t = if t <= 0 then 0 else exp(-1/t)      (ibid.:40-41)
S(t) = 0 (t <= 0);  S(t) = 1 (1 <= t);  S(1-t) = 1 - S(t)      (zero_iff_
        nonpos:165, one_of_one_le:161, from the 146 ratio — the last is a
        one-line algebra check the rig makes a gate on, section 3 GT)

ContDiffBump (c = 0) with fields rIn, rOut evaluates to   (Basic.lean
:117-118 toFun = someContDiffBumpBase.toFun (rOut/rIn) o (rIn^{-1} • x);
ofInnerProductSpace base = smoothTransition((R - |x|)/(R - 1)),
InnerProduct.lean:34; composing R = rOut/rIn, x -> x/rIn and cancelling
rIn — the algebra step the rig re-verifies at tier-1):

  tau(x) = S( (rOut - |x|) / (rOut - rIn) ) = S( (rOut - |x|) / (delta/2) )

properties used downstream: tau = 1 on |x| <= rIn, tau > 0 on |x| < rOut,
tau = 0 on |x| >= rOut, tau even, 0 <= tau <= 1.
```

### 1.4 Degeneracy handling (the F10-class trap, locked UP FRONT)

At high `|Im rho|` and small radii, `delta ~ Delta ~ 1e-24` while `rIn`
lives at `2e-2`: float64 cannot resolve `rOut - rIn` in ABSOLUTE
coordinates, and naive evaluation gives `0/0` inside `S` or
zero-width/absurd-width slivers. LOCKED: no floating subtraction of
`delta` from `R` ever enters an `S`-argument or a sliver length. Every
`delta`-dependent quantity is evaluated through the reductions:

```text
master integral   J(beta) := integral_0^1 S(1 - v) * exp(beta * v) dv
                        (mpmath 200-bit, 64-node Gauss-Legendre on [0,1];
                         J(0) = 1/2 EXACTLY by the S symmetry — gate GT;
                         |beta| <= 1e-14 at tier-1, where
                         |J(beta) - 1/2| <= 1e-12 is asserted)
plateau piece     2*sinh(A*rIn)/A  evaluated with float64 rIn := R - delta
                  (the float64 rounding of rIn is below every locked
                  tolerance: relative effect ~ |A|*delta ~ 1e-21)
sliver piece      (delta/2) * [exp(A*rIn) J(A*delta/2)
                        + exp(-A*rIn) J(-A*delta/2)]   (the formula 1.2(e))
pointwise tau(x)  only ever needed at plateaus (tau = 1), outside (tau = 0),
                  or inside slivers of width delta/2, where it enters
                  exclusively through J-type integrals above; the g/F
                  quadrature (section 3) partitions at the sliver edges
                  (x - rOut_f, x - rIn_f, +-rIn_u, +-rOut_u as x-dependent
                  pairs) and uses the closed K-form below, never raw tau.
```

The closed K-form: for `K_ij(x) = integral tau_u(t) tau_f(x - t) e^{w_ij t}
dt`, `w_ij = conj(t_j) - conj(s_i)`: the domain `(max(-rOut_u, x - rOut_f),
min(rOut_u, x + rOut_f))` is split at the ≤ 6 moving/fixed breakpoints; each
subinterval is PLAT×PLAT (closed form `[e^{w t}] / w`, branch `w = 0`), or
touches one sliver of width ≤ `delta/2` (reduced to
`length * endpoint-factor * J(beta)` with the SAME `J`), or touches two
(sliver×sliver overlap: 24-node GL on the subinterval in scaled
coordinates, mp-safe because the interval is evaluated relatively).
`g(x) = sum_{i,j} (b_j c_i) e^{conj(s_i) x} K_ij(x)` — an exact
float64-evaluable expression at any `x` given the solves.

### 1.5 Assembly, autocorrelation, functional

```text
g(x) = integral u(t) f(x - t) dt            (convolution_apply,
       CCM25Concrete/CompactLogConvolution.lean:108-112; assembly theorem
       C1WindowTaperAssembly.lean:417-432: g = u.convolution f)
F(x) = integral star(g(-t)) * g(x - t) dt   (convolutionSquare_apply,
       ibid.:114-120; Hermitian law F(-x) = conj F(x), :123)
A(g) = ( (log(4 pi) + gamma) * F(0)
         + integral_0^{c} [ e^{y/2} * (F(y) + F(-y)) - 2 F(0) ]
                            / (e^y - e^{-y})  dy
         + F(0) * ln(tanh(Rg)) ).re
with c = 2 Rg; tail identity integral_c^inf -2F(0)/(2 sinh y) dy
   = F(0) * ln tanh(c/2), c/2 = Rg (1397 section 1; denominator
   e^y - e^{-y} = 2 sinh y, CCM25Concrete/SelectedWeilFormula.lean:103)
formula source: C1SameOwnerWeil.lean:48-64 (archimedeanTerm, verbatim
   numerator/denominator/re-cast)
verdict quantity: the REAL scalar A(g); band in section 3 GV.
```

## 2. Locked cells — the (J1) PASS region of the committed artifact

The 1393 cells table was written in the fixed nested loop order
`d → delta → Rf → Ru → eps → eps' → Re rho → Im rho` (the loops quoted
from `scripts/run_1393_rig.py:136-152`; `RERE_GRID × IMRI_GRID` product at
lines 99, 30-31), so row index `k` of
`docs/proofs/1393_component5_rig_cells.tsv.gz` decodes as
`k = ((((( di*6 + δi)*5 + Rfi)*5 + Rui)*2 + ei)*2 + epi)*20 + ρi` with
`ρi` over `(RERE_GRID × IMRI_GRID)` in product order. The columns
themselves (d, delta, Rf, Ru, Rg, ..., ratio, band) pin everything except
`eps, eps', ρ`, which the decode supplies.

```text
candidate geometry = (Rf, Ru, eps, eps', rr, im) appearing in >= 1 decoded
    row with band == PASS
order              = descending (max decoded ratio over its PASS rows),
                     ties lexicographic ascending in (im, rr, Rf, Ru, eps,
                     eps') — fixed, A-blind
tier 1             = the 1394 section 4 witness geometry
                     (Rf = Ru = 0.02, eps = eps' = 0.01, rho = 0.99 + 1054 I)
                     — ALWAYS evaluated, first, alone (its gates G1-3, 5, 6
                     below must pass before any tier-2 cell is touched)
tier 2             = the first 40 candidate geometries in the order,
                     excluding tier 1; remaining candidates reported as
                     UNTESTED with counts
no geometry outside the decoded PASS set is ever evaluated; no grid
   formula moves from 1393 sections 1-2 (reused VERBATIM — auditable joint
   condition, 1397 section 5 item 2)
```

## 3. Locked instrument and gates (F10 precision class; F11 bug-ownable)

Arithmetic: numpy float64 for the grid/quadrature layer; mpmath 200-bit
(the 1393 G3 class) for the 4×4 layer `G → alpha → Delta → delta → T →
coeff → J(beta)`; mp→float64 casts at the printed interface.
Quadrature: composite Gauss-Legendre 16-point panels, at most 2 periods
of the local frequency per panel (`npw = 32`), plus the exact closed-form
pieces of 1.4 (no oscillatory quadrature is used where a closed form
exists). Edge bookkeeping: every `S`-flatness is analytically pre-
integrated into `K` via `J`, so the `g`-function is, between its fixed
critical points `C_g` (all sums/differences of `+-rIn_., +-rOut_.` of both
factors, ~25 points), a finite exponential polynomial; the `F`/`A`
quadratures therefore partition every inner `t`-interval at `-C_g` and
`y - C_g`, every outer `y`-interval at `C_g/2`-class critical points and
the integrable-origin interval `(0, y0 = 1e-3)` handled as one panel
(the `0/0` at `y = 0` is removable and never evaluated: numerator and
denominator are taken at GL nodes only, `re`-projected, and the
`Im F(0)` leak cannot enter the real part). Consequence: every open
panel sees a pure exponential-polynomial integrand, GL-16 at 2 periods
per panel with error class `1e-11`. Merge guard: panels of float64
length `< 1e-12` (from `delta`-scale coincidences) are merged; skipped
mass `<= 1e-12 * sup |g|^2`, far below every locked tolerance.

```text
G0 ADMISSIBILITY    every evaluated geometry: Rf + Ru <= log2/2 and its
                    PASS rows obey 1393 G0/G5 already; violation is
                    INVALID-INSTRUMENT (impossible by construction —
                    the check is for the decode, not the geometry)
GI ARTIFACT INTEGRITY (decode breaker): for ALL candidate geometries'
                    PASS rows and every 1000th row overall, recompute
                    K_loc_f, K_loc_u, ceiling, C_min, ratio, band in mp
                    200-bit from the decoded (d, delta, Rf, Ru, eps,
                    eps', rho) via the VERBATIM 1393 section 1 formulas
                    and compare to the tsv columns: relative difference
                    <= 1e-9 per column, band strings equal, decoded row
                    count == 96000; the decoded witness row must carry
                    the 1394 section 4 ratio (0.9999979741, 1e-9).
                    Any violation: VOID (mis-decode would silently test
                    the wrong cells — the mpmath-zero-fill lesson, 1394
                    section 1, generalized)
GS SOLVE CLASS      at every geometry, per factor: mp residual
                    |T*coeff - p|_inf <= 1e-30 (1393 G3 language)
GT TAPER SANITY     mp pointwise: S(t) + S(1 - t) == 1 within 1e-40 at
                    101 rational probes (the symmetry IS the J(0) = 1/2
                    identity — no quadrature is trusted for it);
                    pairing identity |J(b) + J2(b) - (exp(b) - 1)/b| <=
                    1e-10 at every tier-1 `beta` used, J2(b) :=
                    integral_0^1 S(v) exp(b v) dv (same 64-node rule);
                    mp plateau/exterior probe at arguments t = 3, -1
                    (tau == 1, tau == 0 exactly by 1.3); tier-1 only:
                    alpha -> alpha/2 sensitivity variant REPORTED
                    (delta grows ~2x: informational, no verdict weight)
GF POSITIVITY       F(0) = integral |g|^2 > 0 strictly at every evaluated
                    cell AND |Im F(0)| <= 1e-6 * |F(0)| AND an
                    independent recomputation of F(0) at npw = 24 panel
                    density agrees to 1e-8 relative (two passes of the
                    instrument at different resolution — this is the
                    gate that catches a dead g)
GD DETECTOR         end-to-end: |laplaceAt g rho + 1| <= 1e-6 by direct
                    quadrature of integral g(x) e^{rho x} over (-Rg, Rg)
                    with the 1.4 partition (independent of T: catches
                    node/pattern misalignment that the internal solves
                    cannot see)
GR REFINEMENT       tier-1 only: full A recomputed at npw = 64:
                    |A_64 - A_32| <= 1e-8 * |A_32|; violation: VOID
GQ QUADRATIC WIRING tier-1 only: rerun the WHOLE instrument with
                    p_u -> 2 * p_u: assert |A' - 4 A| <= 1e-9 * |4 A|
                    (A is a real-quadratic functional of the solved
                    owner; a scale leak in g, F, or the kernel breaks it)
GV VERDICT BAND     per evaluated cell, scale S := |(log4pi+gamma) F(0)|
                    + integral_0^{2Rg} |2 F(0)|/(e^y - e^{-y}) dy:
                    POS if A > 1e-6 * S;  NEG if A < -1e-6 * S;  TIE
                    otherwise (TIE cells report, no verdict content)
```

Violation of G0/GI/GS/GF/GD/GR/GQ: INVALID-INSTRUMENT → run VOID
(outcome record must say so; no cell verdicts propagate). GV is the
verdict channel, not a validity gate.

## 4. Outputs

Per-cell table (geometry, decode stats: PASS-row count + max ratio,
`alpha, TB, Delta, delta` per factor, `F(0)`, kernel pieces, `A`,
`S`, band); tier-1 sensitivity/refinement/scale triple as separate
labeled blocks; candidate census (count, tested, UNTESTED list); all
validity gates + GV census; second-to-last line

```text
VERDICT jointWitness=<geometry or NONE> cells=POS:<n>,NEG:<n>,TIE:<n>
```

and final line

```text
DONE gates=G0:PASS,GI:PASS,GS:PASS,GT:PASS,GF:PASS,GD:PASS,GR:PASS,GQ:PASS
```

(any validity gate that failed prints FAIL there and the VERDICT line
must read `cells=VOID`). Acceptance is log-based; exit codes prove
nothing (A2x). Artifacts:
`docs/proofs/1398_rig_run.log`, `docs/proofs/1398_rig_results.json`,
`docs/proofs/1398_rig_cells.tsv.gz`; sha256s recorded in the outcome
record 1399.

## 5. Run precondition

MET at commit time: the instrument needs no Lean-side event (the 1391
green leaf already established the formal side; this rig is pure model
arithmetic over committed artifacts). Python 3.12 + numpy 2.5.3 +
mpmath 1.4.1 on the WSL2 ext4 mirror (the 1393 stack).

## 6. Kill scope — pre-committed, stated with 1393 section 6 verbosity

```text
A NEGATIVE (all tested cells NEG, or TIE, or no joint witness on the
shortlist) kills NOTHING: not route alpha, not the (J1) region, not the
archimedean gate, not rung 3, not the 4-node family in general, not
route beta, not any support window beyond the tested geometries — the
sup-lower-bound law (1087, quoted in 1397 section 3) makes a finite
negative scan non-falsifying BY CONSTRUCTION, and the shortlist is 41
geometries of >= 2000. The outcome record must lead with this.

A POSITIVE joint witness certifies ONLY: at one committed cell, the
transcribed deterministic pipeline of sections 1.2-1.5, evaluated in the
instrument of section 3, has (J1) PASS-band and positive A(g). It
certifies NOTHING about the FORMAL term (harch in Lean is still open),
detector data (rung 4), the Weil criterion (rung 5), hJ1/hfit, the
1393 grid beyond the decoded rows, or RH. Residual doubt channels the
positive does NOT close: transcription of sections 1.2-1.5 (shrunk, not
closed, by GI/GS/GT/GD), quadrature class (shrunk by GR; the tie window
GV keeps sign claims honest), and the model-vs-formal lane (law 65).
```

## 7. Environment and protocol

`scripts/run_1398_rig.py` executed through
`scripts/run_resource_aware_task.sh --class normal --workspace PATH --log
PATH -- cmd` on the WSL2 ext4 mirror; literal paths only, no shell
variables inside `wsl.exe` one-liners (SILENT FAKE-EMPTY law); rename
existing `1398_rig_run.*` artifacts to `*.invN.*` before ANY rerun (7j —
the 1393 inv1 destruction must not repeat; if a VOID run is followed by a
rerun, both logs are preserved); log-not-exit-code acceptance. Law 42:
after this commit, no cell rule, formula, gate, tolerance, or tie window
may move.

## 8. Boundary of this document

Zero rung-3 digits: no `A`, no `F(0)`, no sign, no smoke value at any
geometry — the 1373 protocol (designing grids around peeked signs) is
exactly what section 2's A-blind ordering prevents. All quoted numbers
here are ledger facts (committed grids, 1393/1394 artifact structure,
tolerances chosen now) or the degenerate-scale arithmetic (delta ~ 1e-24,
TB ~ 1.4e9 at the witness geometry) transcribed from source formulas —
they are instrument-design facts, not measurements of the gate quantity.
RH not claimed.
