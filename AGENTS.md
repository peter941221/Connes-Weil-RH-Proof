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

### 7c. Numeric-probe fidelity laws (docs/proofs probes)

Before trusting any probe number: (1) reproduce a Lean-proven identity first;
(2) restrict Grams/inverses to the carrier span BEFORE inverting; (3) make the
carrier real (dpss/Slepian for prolate claims, not smooth bumps); (4) sweep
resolution AND interval - plateau vs decay separates fact from grid artifact;
(5) re-check suspicious zeros against box growth; (6) cross-check FFT legs
against direct quadrature (origin placement!), get closed-form tails from the
right antiderivative, and remember np.expm1(y) = e^y - 1; (7) for narrow
zero-mean tests, expect O(1)/F(0) cancellations making "small" terms O(1);
leggauss nodes already live on [-1,1].

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
- A future semilocal prolate cross-spectral owner must not treat a correct
  first Szego-phase variation (P2a) as an Euler-log proof. Its `p^2`
  coefficient also contains an iterated first-harmonic second variation.
  Prove the P2b cancellation on the same one-crossing readback before adding a
  conditional Lean producer; proof 1054 gives an exact finite cyclic-pair
  counterexample to any general QR/Toda cancellation claim.
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
