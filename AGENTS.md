# AGENTS.MD


最重要的几条规则：
1. 禁止无实质作用的数值实验，要打数学证明。
2. 多个实质推进之后统一批量构建验收、记录。
3. `coverage root` 已在 Lean 中证明与 RH 等价，禁止把它写成普通密度引理。
4. 唯一 RH 主线是健康 `CompactLog` 载体上的 B5 形态：只为选定探测器及其
   有限可见素数集证明半局部正性。禁止把 ROOT 窗口正性写成 B1 已闭合。


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

Active route = healthy-`CompactLog`, B5-shaped, detector-selected semi-local
mainline.  The ROOT form on `[-log 2/2, log 2/2]` is a shared local CC20 base,
not an RH exit and not the universal B1 criterion.  The mathematical exit is
detector-specific semi-local positivity on the same healthy owner, followed by
`SourceRH` and Mathlib RH.  Design records:
`docs/proofs/1043_first_cut_window_architecture.md` and
`docs/proofs/1076_b1_b5_minimal_exit_route_selection.md`.
Freeze rules: `RH_MAINLINE_FREEZE.md` (run
`pwsh -File scripts/check_rh_mainline_freeze.ps1` before touching frozen route
namespaces). Current phase states: README "Status dashboard" (top).

Route selection (2026-08-31, record 1076): the output audit has two singleton
logical cuts, B1 and B5, and each cut is RH-equivalent.  B1's executable
producer would require positivity for all compactly supported vanishing tests;
B5 asks only for the detectors selected against hypothetical off-line zeros.
The B1-only universal globalization is frozen.  The literal normalized B5
socket remains an audit interface, not a producer target: its underlying
`normalizedCC20TestSpace` uses the rejected additive convolution model.

Current local-base position: the CC20 finite-rank chain is wired through the
concrete eq-(115) table, but
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
   its finite visible prime set on the healthy `CompactLog` owner, then
   `SourceRH` and Mathlib RH.  The existing normalized coverage root is an
   RH-equivalent audit socket, not an intermediate density lemma and not the
   mathematical owner for new work; design judgments:
   `docs/proofs/1050_one_shot_rh_route_verdict.md` and record 1076.

Do not schedule a parallel B1 campaign.  `gamma + alpha/beta + delta` may
advance as the shared ROOT-local base only when the proposed theorem names a
consumer in the healthy detector-specific semi-local chain.  A density lift,
an all-test sign theorem, or new producer work on the normalized additive B5
owner is frozen.

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
MSYS_NO_PATHCONV=1 wsl.exe -d Ubuntu-24.04 -- \
  /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/run_resource_aware_task.sh \
  --workspace /home/peter/rh --log /home/peter/rh/build-logs/<name>.log -- \
  /home/peter/.elan/bin/lake build \
  ConnesWeilRH.Dev.<Module> ConnesWeilRH.Dev.<Module>Audit
```

The runner gives focused warm builds a shared global resource lock, gives
full/numeric/cold/unknown tasks an exclusive lock, and serializes writes to
each mirror. Live memory or CPU pressure upgrades a normal task to heavy.
`RESOURCE_SCHEDULING.md` is the complete policy and override contract.

Verification ladder: owning module -> import-facing probe -> focused
`#print axioms` -> route/Dev batch -> full-root aggregate at milestones only.
Acceptance evidence is the LOG, not exit codes: require the footer
"Build completed successfully (N jobs)" AND zero lines matching `^error:`.

Audit checks per brick: read back each declaration's `#print axioms`
(= the three standard axioms), grep audit logs for `sorryAx` (= none).
Keep every Dev leaf paired with a `...Audit` module containing the focused
axiom prints.

Numeric probes run WSL-side through the same resource runner via absolute
`/home/peter/.local/bin/uv run --with numpy --with scipy`; auto mode classifies
them as heavy.

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
scripts/run_resource_aware_task.sh  shared/exclusive WSL resource admission
RESOURCE_SCHEDULING.md  classifier, lock order, overrides, and test contract
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
- All Lake builds and numeric probes go through
  `scripts/run_resource_aware_task.sh`. The runner acquires the global
  shared/exclusive lock, the per-mirror exclusive lock, and then `cd`s to the
  mirror. A raw `flock` protects only its own lock file and bypasses cross-
  mirror resource admission. Do not rely on `wsl.exe --cd` alone; Lake can
  otherwise resolve the caller cwd and pollute the Windows `.lake/build`.
- TWO-TREE SOURCE SYNC: edits land in the Windows tree; WSL runs the
  /home/peter clone. Before EVERY WSL probe run, `cp` the edited file
  through /mnt/c into the clone and verify md5sum on BOTH sides (a stale
  clone re-runs the old build and prints its old banner - observed twice
  in the 1072 round). Commit the byte-exact run version: post-run comment
  polish changes the md5 and breaks the evidence pin.
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
  it. Use the canonical resource-runner template with absolute executable
  paths. Pass a unique `--log` path per invocation; the runner opens it only
  after admission, so a queued task cannot truncate the active task's log.
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
- Env-assignment VALUES with metacharacters do not survive either: after
  wsl.exe re-parsing the quotes are gone and `;` splits the command
  (record 1068: `env SLIST_1068='[];[2]'` executed `[2]` as a command).
  Put such assignments INSIDE `sh -c '...'` with hardcoded paths, or pick
  metacharacter-free values; and redirect probe logs inside the `sh -c`
  string - a Git-Bash-side `> /home/peter/...` aborts before wsl.exe runs.
- `pgrep -f <pattern>` inside a `wsl.exe sh -c '...'` wrapper matches the
  WRAPPER's own command line whenever the plain pattern appears anywhere in
  it (even in a `cp` line elsewhere in the same command) - the char-class
  trick `1070_weil_q_huntin[g]` only works if the plain string appears
  NOWHERE else in that invocation.  Split guard-check and launch into two
  separate calls.

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
- (17) A fixed-grid parameter sweep cannot see a continuum blowup: at fixed
  window the observable saturates (e.g. `D_k -> I` as `k -> 0` is FINITE on
  any finite grid), so a blowup-vs-bounded fork about the continuum limit is
  INVISIBLE to it (1069 first design error, caught pre-registration).  The
  discriminating design is the constant-product ray `k*Xi = kappa0` with
  `kappa0 >> 1`: detector cutoff and window march together, and along the
  ray H-blowup predicts growth `~Xi^alpha` while H-bounded predicts
  flatness.  Same family as law (15) (constant window, quarter dt) with the
  two knobs' roles exchanged; pool points with `k*Xi >= kappa0_min` for the
  log-log exponent, and always keep the unweighted/low-order anchor whose
  continuum behavior is already committed (1067/1068) on the same code path.

- (18) Weil-test dictionary (1070): for the Weil test `f = g * g^sharp`
  (multiplicative convolution) the Mellin image is `f~(s) = g~(s) g~(1-s)`
  (Mellin convolution theorem + `(g^sharp)~(s) = g~(1-s)`), NOT any shifted
  product.  On the critical line `f~(rho) = |g~(rho)|^2` TERMWISE, so the
  zero side is a sum of squares; `f~(1) = g~(1)g~(0)` and `f~(0) = g~(0)g~(1)`
  vanish exactly when `g~` vanishes at {0,1}.  A wrong dictionary passes all
  quadrature checks (each piece is internally consistent) and only a
  derivation catches it - derive the dictionary, then pin it, before scanning.
- (19) Explicit-formula anchor traps (1070): (a) `f = f^sharp` pointwise does
  NOT merge the trivial side: `int f^sharp = f~(0) = int f dx/x`, a different
  Mellin value from `f~(1)` (evenness of f~ as a function says f~(-1) = f~(1),
  nothing about s = 0).  (b) bombieriexplicit2's subtraction term
  `-2e^{-u}f(1)/(1-e^{-2u})` has an EXPONENTIAL TAIL beyond the test's
  support - integrate W_R's u-quadrature to ~40, not to the support edge.
  (c) Cross-validate ANY W_R implementation against bombieriexplicit3
  (the f~/digamma form) - the two closed forms agreeing to 1e-10 plus the
  mpmath zero list is a three-point anchor; do not trust a single-form closure.

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
derivative of that path (mixing them flips the 1054 control sign); (20) port
paper-local symbols VERBATIM and check name collisions with standard
notation: (qe)'s T_n is an integral function of prolate data (tex:1341-1349),
NOT Chebyshev - tex:1370 ("Qeps(1) = 0") falsifies the standard-name reading
(1072 (d); same family as law (14)); read the definition region plus one
falsifiable property line before coding any printed series; (21) np.interp
requires ASCENDING xp and never checks: a [b->a]+[b->c] concatenation
poisons every query below b with binary-search garbage (1072 (g): Qeps came
out 283 instead of ~1e-4); (22) never seed a continuation series with an
edge-NODE value: GL's last node sits 1-O(N^-2) from the endpoint and the
offset times |f'(endpoint)| is 1e-5..1e-3 per mode (1072 (g)); extrapolate
barycentrically to the endpoint and gate with an independent identity (the
ODE seed relation caught it); (23) eigenvector reliability of a symmetric
eigh ends where mu ~ noise/gap: below mu ~ 1e-9 the sinc-kernel modes are
parity-mixed junk while their eigenvalues still print fine - compute only
the load-bearing modes and bound the rest by the paper's own rapid-decay
(983) instead of carrying junk rows (1072 (f)); (24) before naming the
variable of a fitted growth law, divide the table ROW-WISE by every
candidate variable and check which ratio is the stable one - 1071 printed
"0.66 * gamma_j" but the stable ratio was per zero INDEX j (0.64-0.68 per
j vs 0.06-0.19 per gamma_j); j vs gamma_j ~ j log j is a log-factor that
silently misprices every extrapolation (1075 s4.3 erratum).
- (25) mpmath/numpy boundary traps (1078): `mpf` parses NUMERIC LITERALS only
  (`mpf("log(2)")` throws - use `mlog(mpf(2))`); `mpc` has no `.im` attribute -
  use the context method `mp.im(z)`; `np.exp` cannot consume `mpc` - convert
  `complex(s)` at the numpy pipeline entry.
- (26) Prose-over-code sign hazard (1079 run 1): reimplementing a family from a
  docstring while the code disagrees flips the sign EXACTLY (self-consistency
  rel = 2.000, antipodal fingerprint) - 1077's make_g3 docstring said `s(1-s)`
  while its code uses vf0 = s(s-1) (1071:41).  Any reimplementation must pass a
  same-point self-consistency gate against the imported original BEFORE use.
- (27) Linear-system orientation (1079 run 1): `lu_solve` consumes
  `Sum_m M[j,m] c_m`; building the matrix as `[unknown][constraint]` silently
  solves the transpose - symptom: garbage solution magnitudes (~1e5) and a
  post-solve residual failing by orders of magnitude.
- (28) On-line row placement (1079 run 1): Weil rows live at `s = 1/2 + i*gamma`;
  passing bare real `gamma` evaluates a Laplace transform at real points (growth
  `e^{gamma a}` across the window) - symptom: single-point and node checks green
  while row sums are astronomical (margin0 ~ 5e17).

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

### 7g. B1/B5 route boundary (record 1076)

- In this section `B1` and `B5` mean the output-audit logical cuts.  Record
  1074's historical label "GATE 1 alpha B1" is only a local work-package
  label; call that brick `alpha-(983)-tail` in new plans.  It is not the B1
  exit and does not unfreeze universal B1 work.
- `gamma + alpha/beta + delta` ends at ROOT-window `qw` nonnegativity.  CC20
  Theorem 1 has that fixed support; Appendix C equation (155) quantifies over
  all compactly supported tests and all places.  No density or partition
  argument crosses this quantifier gap because it must control mixed quadratic
  terms and newly visible prime powers.
- B1 and B5 are singleton logical exits in the output audit, but they are not
  equal work packages.  A natural B1 producer needs the universal all-test
  sign.  The selected-detector B5-shaped producer needs only one healthy
  semi-local certificate per hypothetical off-line zero and its finite visible
  prime set.  Freeze the B1-only universal generalization.
- The literal `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot`
  remains useful as an RH-equivalent audit socket.  Do not build its producer
  on `normalizedCC20TestSpace`: `not_normalizedCC20MellinConvolutionLaw` proves
  that owner's alleged square doubles Mellin values instead of multiplying
  them.  New detector work uses genuine `CompactLogTest` convolution and exits
  through a healthy-owner `SourceRH` theorem.
