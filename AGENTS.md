# AGENTS.MD


最重要的几条规则：
1. 禁止无实质作用的数值实验，要打数学证明。
2. 多个实质推进之后统一批量构建验收、记录。
3. `coverage root` 已在 Lean 中证明与 RH 等价，禁止把它写成普通密度引理。


Working rules for the Connes-Weil RH formalization. Compressed 2026-08-27:
this file holds only rules that matter to the live route or to day-to-day
engineering. Dead-route chronology, per-milestone ledgers, and superseded
detail live in git history, `docs/proofs/`, and
`_precompress_backup_2026-08-27/`. Update sections in place; do not append
another "current root" paragraph.

## [1] Project Overview

Lean 4 / Mathlib v4.30.0 formalization attacking RH via Weil positivity:
prove `0 <= qw g` on triple-vanishing tests. RH is NOT claimed. No hidden
gaps: no `sorry`, `admit`, new axioms, `True`/`Set.univ` producer fields, or
stored conclusions disguised as source data. Audited leaves must print exactly
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

Active route = C1 same-owner mainline, ROOT form landing target (window
`[-log 2/2, log 2/2]`). Design record: `docs/proofs/1043_first_cut_window_architecture.md`.
Freeze rules: `RH_MAINLINE_FREEZE.md` (run
`pwsh -File scripts/check_rh_mainline_freeze.ps1` before touching frozen route
namespaces). Current phase states: README "Status dashboard" (top).

Route position (2026-08-29, commit 39f0f81 + pending proof-1050 correction):
the CC20 finite-rank chain is wired through the concrete eq-(115) table, but
the paper-scale audit found two corrections.  Equation (119) includes the
central `n = 0` term, and the published scale is about `lam = 1.05158 > 1`;
the landed Bessel lower bound is therefore only a valid `lam < 1` side branch.
Next bricks, in order:

1. Paper-scale finite-section/Toeplitz certificate: exceptional direction,
   complement spectral bound, and rank-one repair producing positive
   coercivity near `lam > 1`.
2. Concrete prolate owner plus Appendix-F uniform tail, exact Fact-1 L1
   certificate, and equation-(100) slope identity.
3. Theorem-7 same-owner trace identity and the resulting ROOT-window endpoint
   positivity theorem.
4. Detector-selected semi-local positivity for each constructed detector and
   its finite visible prime set, then `SourceRH` and Mathlib RH.  The existing
   coverage root is the final RH-equivalent statement, not an intermediate
   density lemma; design judgment: `docs/proofs/1050_one_shot_rh_route_verdict.md`.

GATE 2 (Titchmarsh square-form bridge) is deliberately deferred: classical
proofs need Paley-Wiener / Cartwright entire-function theory absent from
Mathlib (~2000+ lines estimate).

Standing authorization: normal engineering procedures run without asking,
including broad architecture-level changes and genuinely new mathematics,
and - granted 2026-08-27 - routine commits and pushes of mainline progress
to this repository's origin.  Still requires Peter: public GitHub payloads
beyond routine mainline pushes (new repos, PR/issue bodies, comments),
dependency or CI changes, destructive ops, and any step violating the
integrity or RH guards.
No-stop rule: a path is dead ONLY with a named guard, counterexample, or
route ruling that says so.

## [2] Commands That Actually Work

Windows tree is the single source of truth (`git` lives here only). Build
natively on the WSL2 ext4 mirror `/home/peter/rh` (build-only copy, NO `.git`;
never `/mnt/c` - drvfs is ~5x slower). Sync changed files Windows -> WSL, build
there, port reviewed edits back; never copy a WSL worktree back wholesale.

Canonical one-command builds from this Git-Bash harness (direct exec, ONE
command per call, full paths - see gotchas below):

```bash
MSYS_NO_PATHCONV=1 wsl.exe --cd /home/peter/rh flock -w 3600 \
  /tmp/connes-weil-rh-lake.lock /home/peter/.elan/bin/lake build \
  ConnesWeilRH.Dev.<Module> ConnesWeilRH.Dev.<Module>Audit
```

Verification ladder: owning module -> import-facing probe -> focused
`#print axioms` -> route/Dev batch -> full-root aggregate at milestones only.
Acceptance evidence is the LOG, not exit codes: require the footer
"Build completed successfully (N jobs)" AND zero lines matching `^error:`.

Audit checks per brick: read back each declaration's `#print axioms`
(= the three standard axioms), grep audit logs for `sorryAx` (= none).
Keep every Dev leaf paired with a `...Audit` module containing the focused
axiom prints.

Numeric probes run WSL-side via `uv run --with numpy --with scipy`.

## [3] Project Structure

```text
ConnesWeilRH/
  Source/          imported tree; covered by bare `lake build ConnesWeilRH`
    CC20Concrete/  kernels, traces, endpoint formulas, GlobalLogKernel
    CCM25Concrete/ selected squares/crossings/prime terms, CompactLogConvolution
  Route/           conditional route composition (CC20RouteRealization)
  Dev/             research frontier leaves + paired ...Audit modules;
                   NOT covered by the root aggregate - explicit targeting only
docs/proofs/       numbered design records (1043 = active)
scripts/yoshida_intervals/  exact-Fraction LDL^T/digamma certificate engine
```

Owner landmarks: `CompactLogTest` structure lives in
`CCM25Concrete.CompactLogConvolution`; its laws (`laplaceAt`,
`laplaceAt_convolution`) live in `CC20YoshidaConvolution` - open BOTH
namespaces. Project oleans sit under `.lake/build/lib/lean/ConnesWeilRH/<Path>/`;
mathlib oleans under `.lake/packages/mathlib/.lake/build/`.

## [4] Coding Conventions & Review Expectations

Follow existing namespaces/naming/layout; end every `.lean` file with a final
`end ...` and exactly one terminating newline.  Do not add an empty EOF line:
`git diff --check` rejects it.
Data-bearing owners beat separate propositions when several facts must refer
to one object (test + square, operator + kernel, kernel + HS norm). Keep
support parameter and operator cutoff distinct. A legal cyclic trace move
needs two HS factors or trace-class x bounded; ordinary positive trace is kept
separate from any regularized Connes trace. For nontrivial changes: name the
old weak path, add lower data/API, prove projection/compatibility, rewire the
real consumer, prove the old path inactive, add negative guards.

Per-brick protocol: build the ladder above, then log one dated line per change
in `MEMORY.md` (`<date> <file> : <what+why>`), collapse related edits, and put
a design record in `docs/proofs/` only when a proof judgment changes. Log the
change, not the journey.

## [5] Git, Branching & PR Norms

Routine work lands directly on `main`; branch only for isolated experiments.
Imperative subjects <=72 chars. Before commit/push: `git status --short`,
staged-name ownership check, `git diff --cached --check`, scan staged content
for local paths/mojibake/private artifacts. Staging discipline: AGENTS.md /
MEMORY.md are repo-owned here, but never sweep UNRELATED dirty files into a
commit; stage by explicit path. Commit/push and all public GitHub payloads
require Peter's authorization per execution; after publishing public text,
read it back upstream.

## [6] Environment, Secrets & Deployment

Toolchain pinned by `lean-toolchain` (v4.30.0); dependency/CI changes need
Peter. No secrets in the repo. Numeric provenance is mandatory: generated
interval/certificate data must carry per-node source strings (anti-fabrication
mechanics from `scripts/yoshida_intervals/`); floats may generate, Lean
verifies exact identities.

## [7] Known Pitfalls / Gotchas

### 7a. WSL / Git-Bash toolbox (globally reusable)

- MSYS rewrites POSIX-looking args: prefix every `wsl.exe` call with
  `MSYS_NO_PATHCONV=1`. Use `/c/Windows/System32/wsl.exe` if bare `wsl` is off PATH.
- WSL NAT does NOT mirror the Windows localhost proxy: direct `curl`/`pip`
  from inside WSL hang or write 0-byte files silently. Route through the
  default gateway: `GW=$(ip route show default | awk '{print $3}');
  https_proxy="http://${GW}:<port>"` (see `scripts/fetch_cc20.sh`).
- System `python3` is PEP 668 externally managed (pip --user fails silently);
  probes use the Linux-side venv with mpmath/numpy/scipy (currently
  `/home/peter/venv-46937-py312`; locate with `ls -d /home/peter/venv-*`).
- Direct exec sources NO login profile: absolute paths required, e.g.
  `/home/peter/.elan/bin/lake`, distro is `-d Ubuntu-24.04`.
- `bash -lc '<script>'` through wsl.exe mangles quoting: `$var` expands empty
  inside loops/compounds; only a bare `$?` survives. One command per call; do
  multi-step logic in separate calls or script files (nested quotes in
  `sh -c` compounds break Git-Bash eval too).
- Redirect build logs ON THE LINUX SIDE inside a single command (a Git-Bash-side
  redirect onto an ext4 target fails "No such file"); long runs write to a file,
  not `| tail` (tail buffers until EOF reads empty while running - poll with
  `pgrep -f 'lake build'` instead).
- Exit codes lie twice over: a failed log can still report EXIT=0, and warm
  rebuilds can EXIT nonzero on pre-existing lint warnings while error-free.
  Ground truth = zero `error:` lines + success footer.
- Incrementality lies: unchanged files re-run nothing ("no errors" may mean
  "not rebuilt"). To prove re-elaboration of an edited file, delete its
  `.olean` first and expect a real `Built` line.
- All Lake commands take the lock AND issue an explicit `cd` to the mirror
  root inside the Linux shell; do not rely on `wsl.exe --cd` alone.  Without
  the shell-level `cd`, Lake can resolve the caller cwd and pollute the
  Windows `.lake/build` (kill it and delete same-day artifacts there if that
  happens).
- Dual-mirror cache divergence: `wsl.exe` inherits the Windows caller cwd, so
  an un-cd'd build silently runs against the NTFS copy and its `.lake`. The
  two mirrors' oleans can be days apart (observed 2026-08-31: ext4 mirror 5
  days stale while `/mnt/c/.lake` was fresh). Before judging incremental vs
  full wave, compare olean mtimes on BOTH sides (`ls -la .lake/build/lib/lean/...`).
  A warm NTFS cache is a legitimate ~10-min fast path mid-campaign IF you know
  which mirror each build used (check `/proc/<pid>/cwd` of the lake process if
  in doubt). An un-planned full wave costs ~1.5 h on NTFS.
- Cost model (warm ext4 mirror): no-op root build ~3 s; the real cost per edit
  is re-elaborating the one edited file (~12 s per big Dev leaf). Never judge
  progress by job counts; keep the persistent mirror warm.
- Foreground `sleep N; check` compounds get SIGTERM-killed at tool timeout
  (exit 143, nothing persists). Run builds as blocking calls with an explicit
  large timeout, or in background tasks.
- WSL `/tmp` tmpfs content does not survive across invocations reliably:
  persist logs outside tmpfs (e.g. under `/home/...`).
- Do not background a multi-step WSL `sh -c` chain with `&`: after `wsl.exe`
  returns, WSL can reclaim the entire chain before its first copy or build.
  Keep the invocation attached to the host task, or use a durable supervisor.
- A nested-shell `$?` can be expanded at the wrong boundary.  Never use a
  reported `LAKE_EXIT` as acceptance evidence; inspect the WSL-side log for
  zero `error:` lines and its success footer.
- A bare binary in a non-interactive `wsl.exe bash -c` chain is NOT on PATH
  (no login profile sourced): `flock <lock> lake ...` then prints "flock:
  failed to execute lake: No such file or directory" while the shell still
  echoed EXIT=0 and NO build ran at all - only log-evidence acceptance caught
  it. Use the canonical one-command template verbatim (absolute
  `/home/peter/.elan/bin/lake`, dedicated lock, explicit `cd` inside the Linux
  shell); do not launch a second instance against the same log file in
  parallel - bash truncates the log at setup time even while blocked on flock.
- `uv` shares that bare-binary trap (record 1067): probes run through absolute
  `/home/peter/.local/bin/uv run --with numpy --with scipy python ...`.
- Long Python probes redirected to a file are BLOCK-buffered: on SIGKILL the
  whole log is lost, and on normal exit the final flush rewrites from byte 0,
  silently overwriting any fragment a concurrent duplicate launch wrote. Run
  with `python -u`; treat a background task's "completed (exit code 0)" as
  unverified until `pgrep -f <script>` is empty AND the log shows its end
  banner; two pythons on one grid thrash OpenBLAS thread pools (record 1067:
  a duplicate launch stalled the real run for ~1 h before PID-kill).
- WSLg X-server noise ("your ... screen size is bogus") can interleave into
  wsl.exe stdout and swallow command output; redirect the command's own output
  to a /tmp file inside WSL and cat it in the SAME invocation (tmpfs does not
  survive across calls).
- Even correctly single-quoted, a plain `$var` assigned inside `bash -c '...'`
  can arrive empty across the Git-Bash -> wsl.exe boundary (record 1067: "f=...;
  wc < $f" died with "ambiguous redirect"); hardcode paths in the bash -c string.

### 7b. Lean / Mathlib v4.30 recurring hazards

- `ring` treats plain defs as opaque atoms - `unfold <def>` before arithmetic.
- `show T from e` needs a TERM; tactic-position math needs `by ring` etc.
- Rewriting an iff BACKWARDS fails on exponent/spelling mismatches: push the
  forward `.mp` into a `have`, rewrite inside, close with `exact`.
- `rw` cannot bridge star spellings (`Star.star z` vs `(starRingEnd C) z`) -
  simp crosses, rw does not. Probe tactics before committing to rw chains.
- Sign goals over `(cast * X).re`: first prove X equals the real cast
  (`Complex.ext` + simp/ring), then rewrite once; decomposing `.re`/`.im`
  separately starves later rewrites. `zero_mul` is root-namespace.
- Series splits: use `Summable.indicator` + `(h1.hasSum.add h2.hasSum).tsum_eq`
  (no bare `tsum_add`); parenthesize `tsum` summands containing binary ops.
- ENNReal/MemLp bridge: after rewriting extended norms, explicitly apply
  `ENNReal.toReal_ofReal`; prefer `T` over the infinity glyph; keep rpow forms
  until the Bochner bridge converts `rpow_two`. The token `ℝ≥0∞` lexes badly
  outside its notation scope - write `ENNReal`.
- Prop-valued structures cannot carry analytic data ("failed to generate
  projection"): data payloads belong in `Type` structures; conversely a decl
  returning a data structure must be a `def` (`noncomputable def` when it
  mentions Real.log etc.). `#print axioms` audits defs fine.
- Small explicit matrices: avoid leftover `Fin` false branches (decide/omega
  choke on literal atoms); define entries via `Matrix.of fun i j => if ...`,
  discharge triangularity with `simp [def]`. PosDef goals over R carry
  `star x`: peel with `show` (TrivialStar R makes it rfl).
- `x != y` is Boolean; `ne y x`/`≠` is propositional - match the expected type,
  do not replace tokens mechanically.
- An `Lp` value is an a.e.-quotient: reach raw representatives via
  `MemLp.coeFn_toLp`; windowed operators need their own action identity
  (`K_I f = 1_I * K(1_I * f)`), the bare global kernel is not an L2( plane )
  kernel and must not be fed to `applyKernelLp`.
- `open` is NOT transitive: import gives access, visibility needs explicit
  open per namespace/sibling namespace. Beware ASCII-vs-Unicode identifier
  twins (`nu` vs ν) creating silent implicit variables. Global `rw [hxi]` can
  rewrite into nested subterms and swap owners: `change` to atomic coordinates
  first. When Complex.re rewrites stall, use `inner_self_eq_norm_mul_norm`.
- Mathlib names: `Set.indicator_of_notMem` (camelCase); post-deprecation
  `mul_le_mul_left`; `sq_pos_of_ne_zero` single-arg.
- Term-level `mod_cast` preserves strictness and needs an expected target.  To
  derive a nonstrict real inequality from a strict rational one, first
  `apply le_of_lt`, then use `exact mod_cast h`.
- Annotating `have h : f (f _) = f _ := by intro x; ...` leaves the `_` placeholders as
  un-synthesized metavariables ("don't know how to synthesize placeholder"). Derive an
  idempotence equality with a CONCRETE target via `simpa only [mul_apply] using congrArg
  (fun T => T v) hstar.isIdempotentElem`, then close with `exact congrArg g hidem`.
- `rw [h]` replaces ALL occurrences of h's LHS in ONE step; a repeated `[h]`
  in the same list fails ("did not find an occurrence") when exactly two
  matches existed. Write one `rw [h]`. Conversely, `let`-bound names are NOT
  unfolded inside hypotheses - run `dsimp only [<name>] at h` before rewriting
  with it (goal-side lets do unfold).
- On Hilbert endomaps `E →L[ℂ] E`, `f * g ≡ f.comp g` is DEFQ (rfl), and so
  are chains (`f ∘L g ∘L h ≡ (f * g) * h`). The printer shows inferred-sigma
  composition as `∘SL`, but it stays defeq to pure `*`: a two-sided `change`
  from comp-chain form to pure-`*` form succeeds even though the display
  differs. Verify such shape claims in a probe file, not by eyeballing.
- `noncomm_ring` on endomaps works only with PURE-`*` terms: inferred-sigma
  composition subterms stall it ("simp lemmas don't apply; try abel"). It
  takes NO positional hypothesis arguments (`noncomm_ring ha` is a parse
  error in v4.30) and does not consume local ring relations like `h : a * a =
  1` - rewrite with `rw [h]` first, then call it. It DOES know the unit laws
  internally (closes residuals like `x * 1 - 1 * x = x - x`).
- Bare `simp` does NOT strip identity factors (`x * 1`, `1 * x`) on `→L[ℂ]`
  endomaps: `mul_one`/`one_mul` exist but are not simp-marked for that type.
  Use an explicit `rw [mul_one, one_mul]` or let `noncomm_ring` finish.
- Cheap tactic-shape iteration: a standalone probe .lean plus direct
  `lake env lean <file>` (~30-60 s) settles defeq/tactic questions before
  burning full module builds; accept on LOG content, never exit code (see 7a).
- Implicit dot notation on a parenthesized applied receiver inside def bodies
  can fail to resolve ("Function expected at <receiver> ... being applied to
  the argument .method") even when the identical pattern is green elsewhere:
  every repo-green `.smulRight (-1)` usage keeps `).method` on ONE line. Safe
  forms: pipe-forward (`a b c |>.method ...`) or a fully-qualified explicit
  call; never start `.method` on a new line after `(receiver)`.
- Named defs are NOT auto-unfolded by bare `simp only`: list them explicitly in
  the simp set, e.g. `cc20Commutator` (noncomputable def at
  ThreeBranchCommutatorLedger.lean:27-29), exactly as
  CCM24FiniteSCommonBoundaryPair.lean:1751 does - otherwise it stays an opaque
  atom and a signed-difference close leaves a residual goal.
- Identifiers do NOT continue across source-line breaks: a long theorem name
  split over two lines parses as the complete first line (an identifier ending
  in `_`) followed by application of the second line - "Unknown identifier
  `..._`" at the call site. Keep names on one line or use the fully qualified
  path; observed when calling record-1065's two-contract corollary from brick
  1066.

### 7c. Numeric-probe fidelity laws (docs/proofs probes)

- (10) CC20 equation numbers are pinned to the raw tex source by proof 1057
  (170 numbered equations; eq-(115) = `computerverif`, eq-(119) = `opT`,
  eq-(121) = `opTbound`).  Cite 1057's map, not HTML sweeps.  The intro and
  final theorems have DIFFERENT vanishing-condition sets (1057 s5) - match
  exactly one at each consumer.
- (11) Prolate concentration eigenvalues decay per-step ~ (C/n)^2: at
  c = 2pi the float64 Gauss-Legendre collocation floor hits at index ~11
  (lambda_10 ~ 1e-22).  Any validated computation of lambda_n or the modes
  for n >= 7 must be mpmath/ARB; float64 eigenvalue ratios below the floor
  are noise, not physics.
- (12) A module-level mpmath constant (e.g. `OMEGA = 2*mp.pi` at import)
  freezes that value at the dps in effect at IMPORT time and silently caps
  every later evaluation (1061 first run: dps-15 freeze faked a 5e-18
  eigenvalue plateau for n >= 6).  Recompute inside the `workdps` at the
  call site.
- (13) Sparse-operator tables (multiplication by x, x^2, ... in the
  Legendre basis) must come from PRODUCTS of the exact recurrence
  matrices (X @ X), never from hand-derived closed-form coefficients -
  one mis-signed beta_0 in 1061 turned a positive operator's ground
  eigenvalue negative (chi_0 = -13.4).  Positivity of a positive operator
  is a hard assertion gate in every probe.
- (14) A collocation kernel that is a COMPOSITION of two operators gives
  the SQUARED spectrum, not the spectrum.  The sinc kernel
  sin(2 pi (x-y))/(pi (x-y)) on [-1,1] is P_1 F P_1 F (concentration), so
  its eigenvalues are lambda(n)^2; the paper's lambda(n) is the SINGLE
  windowed-Fourier eigenvalue (prolateeq/cosalphan, tex:967-983), with
  ALTERNATING sign (-1)^n.  1059 s4 mispinned the concentration table as
  lambda(n) and only 1062's anchor test caught it.  Also verify the
  inner-product normalization: L^2(R)_ev uses <eta|xi> = 1/2 int_R (tex
  innerltwoeven), a sqrt(2) factor versus standard L2, and squared
  quantities carry a factor 2.  Before booking ANY convention pin, wire
  the contract identity to the paper's published derived number (here
  eps'(1+) ~ 22.9965) and require the match.
- (15) To separate a candidate continuum spectral-tail divergence from an
  under-resolution artifact, compare at CONSTANT frequency window while
  QUARTERING dt.  In 1063, the finite-grid `{2,3,5}` statistic was 20.8779
  versus 20.8784 at xi_max=51.2 under a dt-quarter pair.  This validates the
  probe's interval-growth observation; it does NOT prove a continuum
  trace-class negation. Odd-N grids are mandatory (even N drops Nyquist,
  breaks m(-xi)=conj m(xi), destroys the involution).
- (16) A finite-grid D-WEIGHTED statistic can plateau while the raw statistic
  grows.  This is evidence to study smoothing, not a proof of
  `IsTraceClassAlong basis (D oL K)`: that predicate is a named-basis series
  and `D oL K` can be non-self-adjoint.  With `K = A† A` and `D = C† C`, use
  the Lean-proved active-order identity
  `D K = (A C)†(A C) + C†[C,K]`; then require (a) a continuum
  Hilbert--Schmidt proof for `A C` and (b) a legal pair owner for the signed
  root-commutator.  `C†[C,K]` expands as the `E/Q/R` four-branch ledger; the
  existing detector-level half-line pair for `C† C` does not close a
  root-level branch.  The three 1063 Gaussian scales are reconnaissance only.

Before trusting any probe number: (1) reproduce a Lean-proven identity first;
(2) restrict Grams/inverses to the carrier span BEFORE inverting; (3) make the
carrier real (dpss/Slepian for prolate claims, not smooth bumps); (4) sweep
resolution AND interval - plateau vs decay separates fact from grid artifact;
(5) re-check suspicious zeros against box growth; (6) cross-check FFT legs
against direct quadrature (origin placement!), get closed-form tails from the
right antiderivative, and remember np.expm1(y) = e^y - 1; (7) for narrow
zero-mean tests, expect O(1)/F(0) cancellations making "small" terms O(1);
leggauss nodes already live on [-1,1]; (8) cyclic-vector -> Jacobi-coefficient
recovery amplifies deep-coordinate vector noise by prod_(j<k) a_j ~ k!/k^(1/4):
for a_k ~ k, a dense float64 start vector is decodable only to depth ~15-20
(verified in 1055: 1e-15 start error gives a_5 = 1070 > ||J|| at M=1952); the
exact-coordinate start e_0 is the sole exception because its deep noise is
exactly zero; Stieltjes/Gram-Schmidt coefficient recovery for exponential
weights is hopeless for the same reason; (9) in Euler-log channel bookkeeping,
the delta_f term is the FIRST variation along exp(2 t f) dm, not a second
derivative of that path (mixing them flips the 1054 control sign).

### 7d. CC20 owner landmines (live)

- Paper equation (119) sums over all integers and explicitly sets `d(0)=0`.
  A paired `+/-1,...,+/-m` owner is the truncated operator
  `T - lam * e_0`; the full finite owner must carry a fixed central index.
- Bessel gives `q_T >= (1-lam)||xi||^2`.  It is coercive only for `lam < 1`,
  while CC20 reports the exceptional scale near `1.05158 > 1`.  Never mark
  paper-scale gamma closed from this branch; use the exceptional vector,
  complement bound, and rank-one repair.
- Fact 1 describes its `~0.00122` L1 value as a computer calculation.  The
  decimal and plot are reconnaissance only; Lean needs a directed interval
  certificate for the profile and its absolute-value integral.
- `cc20RegularKernel` has strictly positive pointwise diagonal; paper's raw
  `K_I` has `Qepsilon(1)=0` diagonal zero. A diagonal mismatch rejects literal
  identification only - a.e./operator-level bridging is its own obligation.
- `EndpointKernelFormula` totals its tsum unconditionally; eq-(99)/(104)
  formula level does NOT establish convergence vs analytic Qepsilon away from
  rho=1, nor MemLp/kernel-mass premises - prove those before L2 bridges.
- Spectral containment `spec T subset {lambdaMax} U [-2, lambda2]` is NOT a
  usable form bound in Lean without the decomposition facts: exceptional-vector
  split, complement invariance, complement Rayleigh bound. Keep concrete
  numerical enclosures as explicit caller premises until producers exist.
- ROOT-local zero extension may jump at its two boundary points.  A certificate
  whose downstream use is confined to the ROOT displacement window should
  require `ContinuousOn` that window, never an artificial global `Continuous`
  premise.
- The active C1 `projectionResponse` is exactly the old endpoint metric
  difference `R_0 - R_S`, with `R_S = A (A^* A)^(-1) A^*`. The canonical
  positive-kernel cutoff bridge has a Lean-proved `D2` obstruction: for every
  nonzero test its real trace cannot tend to zero, so that closure is dead.
  See `docs/proofs/1052_c1_projection_square_canonical_cutoff_no_go.md`.
  The `p^2` factor-two calculation in proof 1051 remains a diagnostic
  conditional on a source-Sonin principal-channel readback not yet formalized;
  do not cite it as an independent formal no-go.
- The semilocal prolate cross-spectral family is CLOSED by record 1055: P2b
  was unprovable (no P0/P1 realization, no cancellation mechanism, 1054 exact
  counterexample) AND unfalsifiable by computation (the gate observable has no
  fixed-precision decodable content - 7c law (8) applies to the whole
  lambda-scaling regime). No new probe, table, or conditional Lean owner may
  reference `W_(lambda,S)` / prolate asymptotics unless and until a proved
  self-adjoint realization plus an analytic one-crossing identity exists
  (revival conditions, docs/proofs/1055_semilocal_p2b_verdict.md section 5).
  Its earlier P2a-iterate warning remains true for any hypothetical revival:
  a correct first Szego-phase variation is not an Euler-log proof; the `p^2`
  coefficient also carries the iterated first-harmonic second variation.
- Proof 1056 Ruling 2 (anti-conflation): the historical raw F1 crux is retired
  by 1063's numerical guard.  Its replacement F1' contract and the fixed-scale
  symmetric-sandwich analysis, like any alpha-profile trace work, concern OUR
  fixed-scale concrete model operators; they are outside the freeze above, but
  they do NOT supply the 1055-P0/P1 revival conditions. Never bookkeep a proof
  of F1', the sandwich, or an `hchi` enclosure as a "revival payment" for the
  asymptotic family.
- Alpha is de-risked in shape by 1057/1058/1061/1062: CC20's own eq-(170)
  truncates `Q epsilon` to 11 terms with a published remainder <= 2.366e-12
  on [1,2] (tail arithmetic reproduced exactly by `docs/proofs/
  1058_alpha_chi_reconnaissance_probe.py`).  The alpha brick is an 11-mode
  validated-ODE campaign, NOT an open-ended spectral realization, and 1062
  showed the "analytic continuation across x = 1" is not a hard target at
  all: the bandlimited integral representation
  `xi^an(x) = (1/lambda) int_{-1}^{1} sinc(2 pi (x-y)) xi(y) dy` has
  ENTIRE x-dependence, so the same quadrature gives the mode on all of
  [0,2] (ODE residual 1e-33 at x = 0.5, 1.5, 2 validates it).
- The lambda(n) convention is CORRECTED (1062; supersedes the 1059 s4 pin):
  the paper's `lambda(n)` is the eigenvalue of the SINGLE windowed Fourier
  operator `P_1 F P_1` (tex prolateeq/cosalphan), with ALTERNATING sign,
  and it equals `(-1)^n * sqrt(concentration eigenvalue)`.  The collocation
  kernel `sin(2 pi (x-y))/(pi (x-y)) = P_1 F P_1 F` gives the SQUARED
  spectrum, so the 1061 table `[0.99994, 0.95939, 0.27467, ...]` is
  `lambda(n)^2`; the paper's actual `lambda(n)` list (tex:972-975) is
  `[0.999971, -0.979485, 0.524086, -0.0589766, ...]`.  The contract's
  `eigenvalue` field is the SIGNED `lambda(n)`.  The paper's inner product
  on `L^2(R)_ev` is `1/2 int_R` (tex innerltwoeven), so a unit-norm
  `analyticMode(1)` is sqrt(2) x the standard-L2 value the probes compute
  (factor 2 on every squared term).  With those, the endpointSlope identity
  reproduces the paper's printed `t(n)` list and the 22.9965 anchor to
  <= 2.7e-6 relative (1062 s1).  Landmines kept from 1059: the repo
  `unitAdditiveFourierKernel` (omega = 1) scale is a DIFFERENT spectrum and
  the 1058 probe's original "c = 2 pi" row was mislabeled (omega = pi).
- Alpha T1 is a SPLIT obligation (1061, corrected by 1062): for the contract
  field `eigenvalue_sq_lt_one`, n >= 2 follows from the paper's own (983)
  bound on `|lambda(n)|` alone (bound(2) = 0.75394 < 1 and decreasing), so
  only modes 0-1 need validated enclosures - and their margins
  (`1 - lambda(0)^2 = 5.7247e-5`, `1 - lambda(1)^2 = 4.0610e-2`, the
  SQUARE-ROOT-scaled values, not the 1.14e-4/7.96e-2 concentration margins
  1061 first printed) sit 24+ orders above the 1e-30 cross-truncation noise.
  Do not schedule an 11-mode enclosure campaign; schedule {0,1} plus the
  (983) monotone-arithmetic lemma (brick B1) and the innerltwoeven sqrt(2)
  normalization identity.
- F1 brick-2b (1056) is REVOKED by its own pre-flight (1059): the target
  prolate-factor angle strictness is NOT obtainable by perturbing the
  source angle bound through the Euler transport - `kappa(T_2) = 5.828`
  demands `delta > 0.9852` while `unitLeakageLowerBound` is only
  qualitatively bounded (`0 < delta <= 1`), and the visible-prime pool
  `{p : 1 < p}` is unbounded.  Also: `prolateFactor U` is a composition of
  two orthogonal projections, so `‖prolateFactor U‖ <= 1` is AUTOMATIC -
  never count that inequality as progress; strictness is the whole claim.
  Current posture: F1 stays the Dev leaf's named conditional premise (R2),
  2a Gram-corrected reduction proceeds as algebra, R1 (target-side angle
  lemma via additive-kernel geometry, shifts log p >= log 2 moving the
  window off itself) is deferred to its own design record.
- GATE 1 delta is CONTRACT-WIRED by 1060 (leaf
  `Dev/C1CC20ArchimedeanComparisonWiring.lean`): the paper's (141)-(143) +
  E(f) chain is the structure `CC20ArchimedeanComparison` (fields
  h142/hEchain/h143/trace_nonnegative), consumed into
  `CC20EndpointTraceCertificate` and onward to `0 <= qw g`.  Coordinate
  landmine, do not lose: the CHAIN rank coordinate is `laplaceAt` s = 1/2
  (paper `rho = 0`), the CERTIFICATE rank coordinate is `laplaceAt` s = 0
  (paper `rho = i/2`); they are never identified - the wiring closes
  because the triple vanishing set {0, 1/2, 1} zeroes BOTH.  If any future
  consumer weakens the vanishing set, this leaf must be revisited first.
  The 1057 s5 intro-vs-final vanishing flag is resolved on this safe side.
### 7e. v4.30 cast/spelling hazards (Bessel-repair round)

- `(e : ℂ)` + `^ 2` elaborates the power OUTSIDE the cast (`(↑e) ^ 2`).
  Cast-folds (`← ofReal_mul/sub/sum`) need `← Complex.ofReal_pow` first,
  and `rw` folds only the FIRST matched occurrence class — repeat the item
  per side.
- `star` ↔ `conj` spelling: bridge inside rw chains with
  `starRingEnd_apply`; `Complex.norm_conj` clears conj under a norm.
  `simp only [Complex.star_def]` can recursion-bomb in this state.
- `inner_sum` = sum in the RIGHT slot; `sum_inner` = LEFT slot — check the
  body, not the name.  CLM sum application: use
  `ContinuousLinearMap.sum_apply` (`rfl` and `simp` both fail).
- `ite` conditions must match the goal's argument ORDER: bridge with
  `if_pos h.symm` / `if_neg (Ne.symm h)`.
- omega treats `((an, false)).1` and `an` as distinct atoms: derive
  `have hn := by omega` on plain casts first, transport with
  `Int.ofNat_inj.mp hn`.  Bool `cases` order is false-then-true.
- Feeding a term into a slot with an implicit FUNCTION argument (e.g.
  `{ell : H -> ℝ}`): instantiate the implicit FIRST with a named argument
  `(ell := fun _ => (0 : ℝ))`, then pass the term.  Higher-order unification
  will not infer a constant function from the beta-reduced filler and dies
  with a misleading `0 has type ℝ ... expected Prop` mismatch.
- Structure-instance projections reduce by `rfl`, but arithmetic on the
  projected literals (`x * 1 = x` over ℝ) does NOT: close readback lemmas
  with `show` (unfold the projection) + `rw [rfl-projections]` + `norm_num`,
  not bare `rfl`/`rw [defName]`.

### 7f. v4.30 hazards (1060 delta-wiring round)

- `Source.CC20YoshidaConvolution.CompactLogTest` is only the DEF prefix of
  `laplaceAt` - the TYPE is `CCM25Concrete.CompactLogConvolution.CompactLogTest`
  (via `open CCM25Concrete.CompactLogConvolution`, use the bare name in type
  positions).  Writing the def prefix as a type gives a cascade:
  `Unknown identifier` + error-recovery `sorry` binders that make unrelated
  downstream `linarith` failures LOOK real.  Fix the binder first.
- A "certificate" structure with Real data fields is Type-valued: its
  producer must be `noncomputable def` (Real.log division also blocks
  plain `def`), never `theorem`.
- `rw [...] at H.field` fails on structure projections
  ("expected single reference to variable"): use a `calc` chain against the
  projection instead, and `rw [eqHypothesis]; linarith` to consume an
  additive identification like `trace = W + e`.
