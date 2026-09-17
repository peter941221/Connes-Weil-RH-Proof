# AGENTS.MD


最重要的几条规则：
1. 禁止无实质作用的数值实验，要打数学证明。
2. 多个实质推进之后统一批量构建验收、记录。
3. `coverage root` 已在 Lean 中证明与 RH 等价，禁止把它写成普通密度引理。
4. 唯一 RH 主线是健康 `CompactLog` 载体上的 B5 形态：只为选定探测器及其
   有限可见素数集证明半局部正性。禁止把 ROOT 窗口正性写成 B1 已闭合。
5. 每次开始新的实质性数学砖块前，必须先阅读 `docs/map/README.md` 和里面的所有文档。
   没有健康 `CompactLog` B5 主线消费者（consumer）的工作不得开打。
6. 打的过程中，任何改变路线选择、砖块状态、owner/量词/消费者、no-go 判定
   或端点供应者的发现，都可以立即更新对应 `docs/map/` 文档，不必等待战役
   结束；写明证据和状态。若改变绑定路线或当前状态，同次同步 `README.md` 与
   本文件。未定论的原始数值现象留在 `docs/proofs/`，不得直接改写地图结论。


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
`docs/map/001_first_cut_window_architecture.md` and
`docs/map/003_b1_b5_minimal_exit_route_selection.md`.
Freeze rules: `RH_MAINLINE_FREEZE.md` (run
`pwsh -File scripts/check_rh_mainline_freeze.ps1` before touching frozen route
namespaces). Current phase states: README "Status" (top).

Route-map preflight (mandatory): before beginning a new substantive proof
brick, Lean theorem, carrier family, or numerical investigation, always read
`docs/map/README.md` and binding route ruling `003`. Read `004` when the work
touches C3, endpoint certificates, or an external endpoint source. Read
`001` and `002` when it uses the ROOT-window local base, the
`gamma + alpha/beta + delta` chain, paper-scale Toeplitz work, or a quantifier
boundary. Read `001` through `004` in order when opening a new proof campaign
or after any map update. State the healthy-`CompactLog` B5 consumer that the
work serves before opening the new thread; without one, do not start the work.

Route-map maintenance (live): during work, update the affected `docs/map/`
record immediately when new evidence changes a route selection, brick status,
owner, quantifier, consumer, no-go ruling, or endpoint supplier. Do not wait
for a campaign or batched build to end. Each update must cite its evidence and
label the result as formal, literature-backed, or a project candidate. If it
changes binding route authority or the current status, synchronize `README.md`
and this file in the same change. Raw or unresolved numerical observations
belong in `docs/proofs/` and cannot alone change a map conclusion. Use the next
sequential `00N_` filename for a new route-level record.

Route selection (2026-08-31, record 1076): the output audit has two singleton
logical cuts, B1 and B5, and each cut is RH-equivalent.  B1's executable
producer would require positivity for all compactly supported vanishing tests;
B5 asks only for the detectors selected against hypothetical off-line zeros.
The B1-only universal globalization is frozen.  The literal normalized B5
socket remains an audit interface, not a producer target: its underlying
`normalizedCC20TestSpace` uses the rejected additive convolution model.

Current branch status: the right-oriented convolution-orbit construction now
formally supplies `HealthyYoshidaDetectorData`, hence `qw(g) < 0`, for every
hypothetical off-line zero. The minimal same-detector contradiction to
`SourceRH` is also formal. C3 is still open because no theorem proves
`0 <= qw(g)` for that same orbit-supported detector and its finite visible
prime-power set. The actual doubled-shift alternating product now also has a
  formal no-gap strong-power limit to its intersection projection on the
  `finiteSCarrier`; this uses self-adjoint dense-range/telescoping and does not
  assume a Friedrichs gap. ROOT positivity can feed this branch only after a
  matching support theorem or a genuine semi-local extension; there is no
  automatic arrow from the ROOT window to the orbit detector. The unit-scale
  prolate-range completed detector leg now also has a formal square-summable
  column witness and strong-limit energy readback; the band-minus-prolate
leakage leg and common-right finite-Euler leg remain open. The leakage leg
now has a formal same-carrier doubled-shift normal form as the selected root
conjugated against `p_b - T_b`; this is not yet an HS, trace, or sign
estimate.  The shifted-Hardy reduction now has an exact zero-scale anchor,
exact additive-carrier transport, an exact bundled even-Schwartz dilation
  readback, a formal Schwartz-core readback of the explicit scaled compact
  kernel, a formal bundled bump-Schwartz actual/model equality, and its
  full-carrier extension through the interval density/projection-image bridge,
  and the resulting actual interior Hilbert--Schmidt square-sum transfer.  The
  moving-scale relative prolate strict angle, actual-factor HS square-sum, and
  same-basis positive-composition trace class are now formal (proof record
  1463); G8 cutoff/readback and the R3 detector sign remain open. The map-042
  bridge audit (2026-09-16) proves from committed definitions that every
  actual G8 metric coframe factors as `ambient ∘L sourceInclusion ∘L
  sourceSide`; record 1497 therefore supplies neither diagonal energy, the
  survivor obligation reduces exactly to the in-Sonin square-sum
  `sum ||J† C J s_S e_i||^2` (its out-of-Sonin half is already dominated),
  and the boundary obligation reduces to per-output IN/OUT estimates; the
  two work orders WO-S/WO-B with stop rules live in `docs/map/042`.
  Records 1502 and 1504 now formally discharge the endpoint-limit conditional
  and the ρ5 aggregate-limit iff normal form; record 1505 adds a Route-W
  window/tail decomposition. These are conditional reductions only: S3 and
  B3/B4 remain the analytic energy obligations.
  Record 1506 additionally assembles the already-controlled range leg with
  the Fourier-leakage leg, so S3's remaining estimate is now exactly the
  square-summability of that leakage leg.

The CC20 finite-rank chain is wired through the concrete eq-(115) table, but the
paper-scale audit found two corrections. Equation (119) includes the central
`n = 0` term, and the published scale is about `lam = 1.05158 > 1`; the landed
Bessel lower bound is therefore only a valid `lam < 1` side branch. Open bricks:

1. Paper-scale finite-section/Toeplitz certificate: exceptional direction,
   complement spectral bound, and rank-one repair producing positive
   coercivity near `lam > 1`.
2. Concrete prolate owner plus Appendix-F uniform tail, exact Fact-1 L1
   certificate, and equation-(100) slope identity.
3. Theorem-7 same-owner trace identity and the resulting ROOT-window endpoint
   positivity theorem.
4. The formal no-gap alternating-power limit now discharges the existence
   half of the R3 endpoint on the actual carrier. The remaining producer bone
   is an explicit support/visible-prime description of the formal orbit
   detector, followed by detector-selected semi-local `qw >= 0` on that same
   healthy `CompactLog` owner. The contradiction to `SourceRH` is already
   wired.
5. The remaining exact detector-root square-sum (the doubled-shift leakage
   defect and common-right legs), root-side same-basis trace witness, and G8
   cutoff/readback reconnection. The relative prolate factor's own strict
   angle, HS square-sum, and positive-composition trace class are formal, but
   do not supply that detector-root readback. The existing normalized
   coverage root is an RH-equivalent audit socket, not an intermediate density
   lemma and not the mathematical owner for new work; design judgments:
   `docs/map/002_one_shot_rh_route_verdict.md` and record 1076.

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
New-mathematics rule: when a genuinely new mathematical obstacle is
encountered, do not mark the work `blocked` merely because the route is hard
or unfamiliar.  Actively invent, formalize, and test a new mathematical
route or reduction, and continue attacking it.  `blocked` is reserved for the
repeated, rule-defined impasse after the required alternatives have been
exhausted.

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
docs/map/          route architecture, selection, and interface-audit records;
                   use sequential `001_`, `002_`, ... reading-order prefixes
docs/proofs/       numbered proof and research records
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

README change guard: do not modify, reorder, rename, or cosmetically rewrite
the root `README.md` without Peter's explicit prior approval. A requested
README change must stay scoped to the approved wording, layout, or evidence
links; unrelated README cleanup is out of scope.

- GitHub's browser math renderer rejects `\operatorname` in README display
  blocks and can render `\!` as a visible character. Use `\mathrm{...}` for
  function identifiers and `\text{...}` for labels; avoid spacing macros,
  then inspect the rendered GitHub page after pushing. The Markdown API only
  confirms block parsing (the API HTML embeds raw LaTeX inside
  `math-renderer` elements without rendering it), AND it is not a proxy for
  the browser engine either: GitHub's client renderer is NOT the npm `katex`
  package — local KaTeX 0.18.5 parsed `\\[0.5em]` perfectly while the live
  GitHub page flattened the `aligned` rows and leaked the tag as visible
  text (f1032ad, reverted by 6808c58, 2026-09-03). The ONLY acceptance for
  any math macro change is visual inspection of the live rendered page.
- DEAD END (2026-09-03, verified broken on live GitHub): row-break size
  arguments `\\[0.5em]` / `\\[10pt]` inside `aligned`. Never re-attempt via
  that route. Untried candidate class for in-block breathing: no-bracket
  struts (`\vphantom{\frac11}` at row heads) — must be piloted on ONE block
  with live readback before any batch application.
- Escaping trap for scripted math edits: a bash heredoc fed to python halves
  `\\\\` to `\\` once through each shell/JSON layer, so `\\` can silently land
  as `\[0.5em]` (single backslash = ParseError). Never trust inline escaping
  for backslash payloads; write the script with the Write tool or build
  backslashes via chr(92), and byte-verify (`od -c`) one edited line.
- GFM parses Markdown before handing content to its math renderer: a source
  line inside `$$` that begins with `-` becomes a Markdown list and drops the
  display block. In multiline equations, keep subtraction after a non-list
  TeX token such as an `aligned` `&=` row. Accept only when source display
  delimiters and Markdown-API `js-display-math` counts agree.
- A README math panel carries one theorem-level proof node. Keep prose and a
  blank line on each side of a boxed display; consolidate a premise-to-result
  chain instead of stacking formulas that repeat the same transition.
- GitHub collapses repeated blank lines, so source blank lines cannot widen
  rendered math spacing. The README carries one standalone `<br>` line
  (blank line on each side) before and after every `$$` display block
  (51 groups, one shared between adjacent blocks); never strip or reorder
  these spacers. Accept when Markdown-API `<br>` and `js-display-math`
  counts match the source.
- An added README display needs adjacent evidence: a paper, proof record, or
  Lean declaration. When it states a repository claim, link the corresponding
  Lean theorem and name the mathematical owner.

## [6] Environment, Secrets & Deployment

Toolchain pinned by `lean-toolchain` (v4.30.0); dependency/CI changes need
Peter. No secrets in the repo. Numeric provenance is mandatory: generated
interval/certificate data must carry per-node source strings (anti-fabrication
mechanics from `scripts/yoshida_intervals/`); floats may generate, Lean
verifies exact identities.

## [7] Known Pitfalls / Gotchas

### 7c. Chat output rendering (global workspace rule)

- Do not emit TeX/LaTeX display math or raw TeX commands in Codex chat
  responses. The chat renderer is not an accepted TeX target and can expose
  commands as mojibake/source text. Use short plain-language statements, or
  ASCII-only code blocks for exact formulas, e.g.
  `L2_cost(g) <= (1 + eps) * y* Gamma^-1 y`.
- This applies even when the same mathematical content has a valid TeX form
  in repository Markdown. README-specific GitHub-rendering rules remain
  separate and apply only when editing that file.

### 7a. WSL / Git-Bash toolbox (globally reusable)

- Importing a committed probe script by file path
  (`importlib.util.module_from_spec` + `exec_module`) fails inside
  `@dataclass` processing with
  `AttributeError: 'NoneType' object has no attribute '__dict__'` unless
  you first register it: `sys.modules["name"] = module` BEFORE
  `exec_module` (dataclasses look the defining module up there; 1087 cert).
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
- Multi-line `git commit -m "..."` with STRAIGHT double quotes inside the
  message closes the shell string early and git then treats the remainder as
  pathspecs (re-burned 2026-09-17: `error: pathspec 'committed' ...`, commit
  silently not made). For any message containing quotes or non-ASCII glyphs,
  write the message to a temp file OUTSIDE the repo and use
  `git commit -F <file>`; replace `★`-class glyphs with `(star)` in commit
  text to avoid Windows-console mojibake.
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
- A BARE Git-Bash `cp <winfile> /home/peter/...` fails "No such file or
  directory": that ext4 target lives inside the VM and is invisible to the
  Windows-side cp (same root as the redirect trap above). Run the copy INSIDE
  wsl.exe sourcing from /mnt/c, e.g. `wsl.exe bash -lc 'cp /mnt/c/... /home/peter/...'`
  -- a Git-Bash-side cp target or `> /home/peter/x.log` aborts before WSL runs.
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
- SILENT FAKE-ZERO readings (record 1121, 2026-09-04): a compound one-liner
  `bash -c 'L=/path/log; wc -c $L; grep -c "^error:" $L'` splits at the
  semicolons on the WSL default shell - `bash -c` receives ONLY the
  assignment, the greps run with `$L` EMPTY and read STDIN, printing a bare
  `0`.  This manufactured three rounds of "0-byte log / 0 errors" false
  evidence while the real log held 90 KB and 3 errors.  NEVER use shell
  variables in wsl.exe one-liners; spell the literal path in EVERY single
  command of the compound.
- The sanctioned build invocation is documented (see s7b header block):
  runner payload after `--` is the ABSOLUTE path
  `/home/peter/.elan/bin/lake build <Targets>`.  A bare `lake` payload exits
  127 (the runner execs the payload directly, no login shell, no elan PATH);
  a `bash -lc` wrapper payload is REFUSED by the runner's payload inspector
  ("shell payload cannot be inspected safely").  Read the documented
  invocation BEFORE inventing launch plumbing (cost in 1121: four launches
  instead of one).
- Repo LEAN sources live under `ConnesWeilRH/Source/` (imported tree) AND
  `ConnesWeilRH/Dev/` (frontier leaves + paired `...Audit` modules, explicit
  targeting only; the C1Spectral*/C1WeilCriterion* family is in Dev/).
  The ext4 mirror `/home/peter/rh/` carries the same layout. They do NOT
  live in a `src/` directory. Cost in the 1350-wave: two WSL greps over
  `/home/peter/rh/src` and `.lake/packages/mathlib` returned empty for
  `exponentialWeight` before the Windows-side Grep found it in one shot at
  `ConnesWeilRH/Source/CC20YoshidaConvolution.lean:35`. Before any symbol
  hunt, `ls` the repo layout once; a wrong-directory grep loop costs more
  than the listing.
- `/tmp` does NOT survive between wsl.exe invocations anymore (record 1381,
  2026-09-13): the WSL VM recycles after the last console session exits and
  the tmpfs log is gone — a background launch showed the log existing
  (38 bytes), and a poll 90 s later found it deleted.  Build logs now go to
  the persistent ext4 home: `/home/peter/buildlogs/<NNNN>_tryK.log`.  The
  working pattern is (a) foreground `cp`+`cmp` sync call, then (b) a
  separate FOREGROUND `flock /tmp/connes-weil-rh-lake.lock bash -lc
  'timeout 560 lake build <targets>' > log 2>&1` call that also greps the
  errors in the SAME invocation — no background launch, no cross-call log
  lifetime.
- TWO PERSISTENT LOG HOMES (clarified record 1387, 2026-09-13): the
  record-1381 series lives at `/home/peter/buildlogs/<NNNN>_tryK.log`, while
  the whole 009 campaign lives at `/home/peter/rh/build-logs/009_*.log` (the
  mirror's own `build-logs/`, which also holds the legacy `NNNN_buildK.log`
  series). Searching only the first home reports the 009 acceptance logs as
  MISSING when they are present — check both before declaring evidence lost.
- SILENT FAKE-EMPTY RE-CONFIRMED (record 1387, 2026-09-13, self-inflicted):
  a `for L in a b c; do grep ... /path/$L.log; done` loop passed through
  `wsl.exe -- /bin/bash -c "..."` printed EMPTY for every iteration — `$L`
  dies at the Git-Bash → wsl.exe boundary, so each `grep` read a literal
  `/path/.log`. The reading looked like "the acceptance logs do not exist",
  which would have been recorded as missing evidence for three green
  components. Spelling the literal path in every command of the compound
  worked on the first retry. This is the loop form of the record-1121
  fake-zero law, and it is MORE dangerous: it manufactures ABSENCE evidence,
  which prompts a wrong conclusion instead of a re-check. LAW: never iterate
  a variable over paths in a wsl.exe one-liner; repeat the literal path, one
  `grep` per log.
- Acceptance readback is four greps on the log, never the reported exit
  status: `grep -a 'Build completed successfully'`, `grep -ac '^error:'`,
  `grep -ac sorryAx`, and `grep -ac 'Quot.sound'` — the last must equal the
  number of `#print axioms` lines in the paired Audit leaf. Axiom prints WRAP
  across log lines (record 1375 s11), so count `Quot.sound]` occurrences
  rather than matching a single-line axiom set.
- FAKE-EMPTY THIRD RE-CONFIRMED (record 1391, 2026-09-13): a `\$L` log-path
  variable inside the nested `wsl.exe -- /bin/bash -c "..."` compound expanded
  to EMPTY, and the four-marker readback printed bare `0`s for a 96 KB log —
  a healthy-looking result built on a MISSING file. Distinguish by shape: a
  real `wc -l file` prints `count<TAB>filename`, an empty-expansion run prints
  a BARE `0`. LAW: the four-marker readback must inline the literal log path
  four times; a bare number with no filename suffix means the argument list
  silently collapsed.
- FOREGROUND `wsl.exe` CALLS DO NOT SURVIVE THEIR OWN SESSION (record 1391,
  try4): the build itself was fine; the readback command's WSL instance got
  localhost-proxy-flaked mid-build, and lake died with SIGHUP leaving a
  truncated log with NO completion marker and NO error — indistinguishable
  from a slow build except by `pgrep`. LAW: any lake build expected to exceed
  a few minutes goes through the detached pattern: (1) one foreground call
  writes the build script (`printf '%s\n' ... > run_try.sh; cat run_try.sh`
  to verify), (2) a second call launches
  `setsid nohup bash run_try.sh > /dev/null 2>&1 < /dev/null &` + `sleep 12`
  + confirm the log file now exists, (3) poll for the sentinel file, (4)
  four-marker readback on the finished log.

### 7b-numeric. Numerics probe hazards (1212/1213 lessons)

- Gamma-quotient phases overflow at fine grids: Gamma(1/2-2 pi i xi)/conj
  underflows 0/0 for |2 pi xi| >~ 400 (e^{-400}).  Use exp(2i arg(gamma));
  angle(0)=0 -> phase 1, inert where the spectral weight is e^{-400}.
  Smoke grids (coarse dt) HIDE this — S0 gates must run at official dt.
- Discretized sandwich traces carry TWO dt factors: tr_cont = tr_disc*dt^2
  (one for the trace sum, one for the kernel integral inside W[i,i]).
  Verified identity: bulk*dt^2 = 2 Rn f0 (1.3e-4).  A single-dt
  normalization silently rescales every readout by ~1/dt (~190x at the
  1212 grids) and mimics physics.
- Rank-deficient Grams: a regularized inverse (G+reg)^{-1} is NOT a
  projector; use eigh + spectral threshold (Moore-Penrose).  Check the
  G_C gap explicitly; 1212 measured 1e8-1e9 (kept 2.4e-3 vs dropped 1.5e-9).
- Reflected multipliers on centered FFT grids: reflection is
  np.roll(a[::-1], 1) (off-by-one without the roll); the adjoint of a
  reflected multiplier d is conj(d(-xi)) = conj(np.roll(d[::-1],1)).
- "Loop over pair (coarse, fine)" bugs silently run only one grade:
  the first 1212 official invocation iterated `for tag, N in pairs` over
  [(8192,16384)] and ran N=16384 only.  Always assert both grades are
  present in the results JSON before verdict analysis.
- Detector aliasing paranoia (RESOLVED for the 1116 twin): gamma_9 = 48.01,
  Nyquist dt <= pi/gamma = 0.065; every ladder grid dt <= 0.0121 resolves
  it; f0d*dt = f0 to 6 digits is the quick sampler health check.
- mpmath `mp.matrix(m, n, X)`: the THIRD argument is a callable (i, j) ->
  entry, NOT an entry list — passing a list SILENTLY zero-fills the matrix
  (1393 invocation 1: every K_loc read 0.0, all 96,000 cells spuriously
  "PASS", and only the G3 positivity gate caught it; RE-INFLICTED 1398
  inv1 by an instrument rewrite that did not consult this entry — see
  law F13: the fix below is the documented-correct idiom, copy it). Build
  columns as
  `mp.matrix([[v] for v in col])`, and before any table loop, probe ONE
  constructed vector by printing `z[k, 0]` against the expected pattern;
  prefer explicit `[i, j]` indexing everywhere over linear `z[k]`.
- Float64 is a SILENT instrument choice: a prereg that locks formulas but no
  precision class defaults to float64, and at oscillatory registers
  (cond(G) ~ 1e13 at R = 0.02) a model-guaranteed-real quantity leaked ~294
  of spurious imaginary part (1390 G3 void). Rule: every MODEL/analysis
  prereg states its precision class and its residual/imag tolerance
  numerically (1393 s3 G3: 200-bit, 1e-30 classes).
- A re-run onto the SAME prereg'd artifact paths destroys the previous
  invocation's evidence (7j law, RE-INFLICTED at 1393: invocation-1 log/json
  overwritten; survived only because the sentinel + all-zero telemetry were
  quoted into the record at the time). Rename to `*.invN.*` BEFORE any
  rerun, even when invocation N is "just a crashed script".
- MODEL digit -> exact-rational certificate template (1396, reusable):
  transcendental atoms ONLY on exact rationals (mpmath dps>=100, pad +-1e-80,
  mpf -> Fraction via `z._mpf_` (sign, man, exp) — `Fraction(mpf)` is a
  TypeError and `Fraction(str(mpf))` may round INWARD); everything after is
  a hand-rolled Fraction RI/CI layer with exact outward rounding; K-type
  quantities by Cramer/Leibniz with zero-free-norm asserts; final answer as
  a dyadic pair compared over `Fraction` (zero float at the comparison
  layer). mpmath's own `iv` is NOT usable for complex data: no complex
  intervals, no `iv.conj`, and `x + 1j*iv.mpf(...)` coerces through float.

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
- Writing Lean source through the tool pipeline can silently DROP glyphs: in
  record 1588 an inner-product statement lost the opening bracket U+27EA in
  four places and the field glyph U+2102 in one, surfacing as "unexpected
  token" and as a stuck `InnerProductSpace ?m H` typeclass problem - neither
  is a proof failure, both cost a build round. Mitigation: state new
  inner-product facts as `inner ℂ x y` instead of bracket notation, and
  before syncing COUNT that U+27EA and U+27EB occur equally often and that no
  `inner` token is followed by two spaces.
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
- G8 source-carrier names are spread across sibling namespaces: the abbrev
  `sourceSoninCarrier` lives in `CCM24FiniteSGramResponse`, `rootConvolution`
  in `CCM24FiniteSBandTrace`, `finiteEulerPulledObliqueShear` in
  `CCM24FiniteSGatePhysicalObliqueShearReduction`; a new G8 leaf must open the
  union of the sibling leaves' open lists, not a guessed subset (1567 try1).
  Likewise `(SelectedWeilSquareOwner.ofCompactLogTest g).sourceTest = g` is
  provable by `rfl` yet simp will not rewrite it unprompted - name the equation
  explicitly in the simp set when comparing owner-computed sums (1567 try2).
- v4.30 has NO `ContinuousLinearMap.adjoint_sub` / `adjoint_neg` simp lemmas
  and `neg_eq_neg_one_smul` may be unresolvable at Dev import depth: prove
  `(A - B)† = A† - B†` with the committed local idiom (`ext_inner_right` +
  `adjoint_inner_left` + `inner_sub_left/right`, precedents at
  `C1G8R5AggregateExpansion.lean:134` and `C1G8P1MetricChannels.lean:204`),
  and close `(-1 : ℂ) • x = -x` residuals with a trailing `simp` (1569 try3).
- Declaration modifiers bind BEFORE docstrings: `set_option maxHeartbeats N
  in` must come above the `/-- ... -/`, otherwise the parser dies with
  "unexpected token 'set_option'; expected 'lemma'" (1569 try1).
- When restating a proven `Tendsto` with a rewritten limit point, rewrite the
  GOAL with the trace-split equation (`rw [← hsplit]` then `exact h`);
  `rw [← hsplit] at h` fails because the hypothesis contains the
  definition-unfolded literal and the split's LHS is the named def (1569
  try2/try3 lesson; defeq match works goal-side, not hypothesis-side).
- A pair with a `WithLp 2 (X x Y)` factor carrier can be avoided when
  sandwiching: sandwich the two plain-factor pairs separately (each plain
  basis is already in the bundle) and recombine by
  `isTraceClassAlong_add` - `boundedSandwich` then never needs a WithLp
  Hilbert basis (1569 design).
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
- 1111 additions (matrix quadratic-form API, v4.30): the PSD predicate is
  `Matrix.PosSemidef` (NOT IsPosSemidef); the quadratic-form bridge is
  `posSemidef_iff_dotProduct_mulVec` and `PosSemidef.dotProduct_mulVec_nonneg`
  carries `star x` which `simpa` strips on R (TrivialStar).  `mulVec_mulVec`
  FOLDS (`M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`) - splitting a product needs the arrow
  reversed (`← mulVec_mulVec`); `dotProduct_mulVec` rewrites
  `v ⬝ᵥ (M *ᵥ w)` into the vecMul atom `v ᵥ* M ⬝ᵥ w` - if your goal/atoms want
  the mulVec spelling, DO NOT leave it in the simp set (atom mismatch starves
  linarith).  Design rule that ended three RED iterations: expand pencil
  identities IN PLACE in the working hypothesis (simp only [sub_mulVec,
  add_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul]
  at h1; then rw the pairing identities and hc), never as a separate proved
  equation whose RHS must be guessed to match a simp-normalized form; smul on
  a SCALAR atom needs `smul_eq_mul` at the end.
- (record 1115 additions) v4.30 matrix instance diamond: numeral smuls on
  matrices (`2 • M`, `U • G - M`) elaborate through DIFFERENT SMul instances
  at different positions of the same file (pp.all showed `instSMulOfMul` on
  one side); `rw` then refuses to match visually identical terms. Architecture
  rule: elaborate the smul-bearing term ONCE inside a hypothesis
  (`hD : D = U • G - M`) and let every other site speak of the free variable;
  keep `•` out of all other statements (use additive identities).
  Related path facts: the notation import is `Mathlib.LinearAlgebra.Matrix.Notation`
  (`Mathlib.Data.Matrix.Notation` does NOT exist); Fraction-division literals
  `a/b : ℝ` force every dependent `def` to be `noncomputable`
  (Real.instDivInvMonoid); the scalar ℝ action `U • x = U * x` closes by plain
  `simp` but NOT by `simp only [smul_eq_mul]` (not Mul.toSMul); and
  `norm_num [big list]` preprocessing omits the beta/Fin clean-up that
  fin_cases residues need - use `all_goals simp [defs] <;> norm_num` with the
  GLOBAL simp set first.
  Resource options: `set_option maxHeartbeats N` at FILE scope is rejected for
  resource options (warning, unscoped-not-allowed); the sanctioned form is
  `set_option maxHeartbeats N in` immediately above the declaration, and
  `linter.style.maxHeartbeats` wants a `-- reason` line right after it.
- (record 1117 additions) v4.30 rw discipline + scope bookkeeping, all hit on
  the Stage-B domination module: (a) `ext x` on an equality of TestFunctions
  does NOT unfold reducible projection defs - `(ICdefect ...).test` stays
  FOLDED under ext; forward-rewrite with the definitional lemma first (`rw
  [ICdefect_test, ...]`) to expand it. (b) `rw [h1, h2, ...]` applies rules
  SEQUENTIALLY and stops at the first failure; its error shows the failed
  rule's pattern plus the CURRENT mid-progress state as "target expression" -
  diagnose list failures by reading which position that displayed target
  corresponds to. (c) v4.30 `rw` AUTO-CLOSES goals that become defeq-true
  after rewriting (deleting an explicit trailing `rfl` then yields "No goals
  to be solved"). (d) `rw` does NOT eta-expand: a have whose LHS is
  `(fun y => f y)` will not match a goal subterm `f`; state such equalities at
  the bare-function level (`have h : I F = fun y => ...`) so the LHS matches
  the goal verbatim. (e) A syntax error in an upstream by-block cascades:
  later `have`s vanish from context and produce phantom "unsolved goals"
  errors at unrelated anchors - fix the parse first, do not chase downstream
  messages. (f) A named `end Name` requires the innermost open scope to be a
  namespace of that name; an unclosed `noncomputable section` (anonymous
  scope) needs its own bare `end` before the named ends, else "Unexpected
  name ... after 'end': The current section is unnamed" fires once per dotted
  end-name segment.
- (record 1117 cleanup-batch additions, probe-verified) `show P from e` parses in
  TERM position only (e.g. inside `rw [h, show Q from t]`); as a by-block
  ITEM it never parses - all three item shapes fail with "unexpected token
  'from'; expected command". An item-position bare `show P` is itself a
  pattern/defeq check against the current goal ("'show' tactic failed,
  pattern" on mismatch), so it does real work even when P looks like a
  restatement. The show-readability linter (runs under lake, NOT bare lean)
  fires only when the shown P is defeq to the current goal - then delete the
  show and close directly instead of folding to `show P from tac`.
- (record 1117 cleanup-batch additions) `simp only []` does NOT delta-reduce plain
  top-level defs: listing the def in the simp set (`simp only [ICdefect, ...]`)
  or `change P; simp` is required. Probe before deleting a show whose stated
  purpose was "readability" - it may have been silently doing the unfold.
- (record 1118 additions) v4.30 Finset.sum parser trap, hit 4x on the
  T-box kernel: a BARE `fun` as the summed function swallows a following
  relation - `s.sum fun i => A i j * x i * x j = RHS` parses the `=` INSIDE
  the lambda, the summand becomes a Prop, and the elaborator reports
  "type mismatch ... AddCommMonoid Prop". Parenthesize the summand
  (`s.sum (fun i => ...) = RHS`) or name the function in a `have`. The same
  swallow hits `<=` and `<`.
- (record 1118 additions) v4.30 `pow_two` is stated `a ^ 2 = a * a`
  (Mathlib/Algebra/Group/Defs.lean:700) - direction FLIPPED vs the classic
  `a * a = a ^ 2`. `rw [← pow_two]` therefore searches for a `?a * ?a`
  pattern, which never matches an `x i ^ 2` goal; nlinarith ring-normalizes
  squares itself, so the rewrite is simply dropped.
- (record 1118 additions) calc-step INDENTATION is load-bearing: steps must
  be monotonically indented (or uniformly aligned). A non-monotonic dip
  (col 10 -> 12 -> 14 -> 12) lets the parser bind shallower steps into the
  PREVIOUS step's by-block, producing phantom "unsolved goals" at the calc
  end. Fix: flatten every step to one column.
- (record 1118 additions) one-sided rewrites on a shared symbol need
  `conv_lhs => rw [hu]`: plain `rw [hu]` where `hu : uK = insert i ...`
  rewrites the uK on BOTH sides (the RHS `(uK \ {i})` also contains uK),
  looping/failing. Scope it with conv.
- (record 1118 additions) theorems with leading IMPLICIT args (`{d}`, `{A}`)
  must be called with only their EXPLICIT args: `lbCollect d rad x` fills
  the implicit `d` slot positionally and errors ("function expected" /
  type mismatch at the matrix arg). Call `lbCollect rad x`. Same trap for
  `qformDoubleSum x` (not `qformDoubleSum A x`).
- (record 1118 additions) to_additive-generated Finset lemma names
  (`Finset.sum_add_distrib`, `Finset.sum_sub_distrib`, `Finset.sum_neg_distrib`,
  `Finset.sum_comm`) are INVISIBLE to `theorem <name>` greps of the Mathlib
  tree - they are generated, not declared. Verify existence via usage sites
  (rg the bare substring inside Mathlib source) before scripting against them.
- (record 1118 additions) `nlinarith` will not bridge the atom split between
  `|x i * x j|` and `|x i| * |x j|`: feed the explicit equation
  `have hmul : |x i * x j| = |x i| * |x j| := abs_mul _ _` and close with
  `linarith [hmul, ...]`. Same for a goal shaped `-|E * q| <= E * q`: route
  via `mul_assoc` + `neg_abs_le`.
- (record 1118 additions) `show T, by tac` is not term syntax (comma);
  a declaration whose binders are implicit `{a b : R}` but is applied with
  positional explicit args surfaces as "Function expected", not as an
  arity error - check binder brackets first when the error names a lemma.
  Diagnostic sums built from `Finset.sum` need the summand parenthesized
  even inside `have` type ascriptions (the swallow is parse-level, not
  goal-level).
- (record 1122 additions) `𝓝` / `𝓝[>]` are SCOPED Filter notation: a module
  with plain `open Filter` but no `open scoped Filter` fails every nhds site
  as "unexpected token '>'" PLUS "Unknown identifier 𝓝" - one root cause per
  whole error batch, fix the scoped open first. Dot-projection `h.not_le` on
  `h : a < b` resolved into the nonexistent `Real.lt.not_le` (instance-path
  quirk) - close the contradiction by linarith over both facts instead.
  Also: proving `f 0 = 0` for a complex numerator needs `simp [def]; ring`
  on the UNcoerced equation first; simp alone stalls on the `.re`/`.im`
  projection of the unreduced complex expression (owner-file route).
- (record 1118 additions) vec notation (`⬝ᵥ`, `*ᵥ`) used in a module that
  forgot `open Matrix` does NOT fail as an unknown identifier: the parser
  consumes the subscript as a raw token and elaboration dies with
  "elaboration function for `Mathlib.Tactic.subscriptTerm` has not been
  implemented" at EACH notation site, and the tail of the error batch shows
  a PHANTOM "(deterministic) timeout at `isDefEq`, maximum number of
  heartbeats (200000)" at the first application of the mangled term - fix
  the open first, never chase the unification timeout. (1118 audit, build
  #1; the 220 KB data module itself was green first try.)
- (record 1119 additions) `abs_add` and `sub_neg` (old meanings) do NOT
  exist in v4.30. The subtraction triangle is `abs_sub (a b) :
  |a - b| <= |a| + |b|` (a <=-lemma, NOT a rewrite rule - consume it as
  `have tri := abs_sub x y`, then linarith). `sub_neg` now states
  `a - b < 0 <-> a < b`. Route every `-|x| <= x <= |x|` need through
  `abs_le.mp (le_refl _)` (gives BOTH halves as a conjunction).
- (record 1119 additions) `linarith` does NOT split nonlinear atoms:
  `mu * radG j i` and `mu * radG i j` are DISTINCT atoms even when a
  symmetry hypothesis says the matrices agree transposed. Pre-rewrite the
  offending bound to ONE index form via the symmetry hypotheses BEFORE
  calling linarith, and do not pass the symmetry hypotheses to linarith
  (it cannot use a linear equation to identify products).
- (record 1119 additions) `linarith` does not decompose an `abs` atom on
  its own: an inequality over `|Δ i j| + |Δ j i|` needs the explicit
  `p : -|Δ i j| <= Δ i j /\ Δ i j <= |Δ i j|` pairs fed in
  (`abs_le.mp (le_refl _)` per term).
- (record 1119 additions) `rw [Matrix.transpose_transpose] at h` rewrites
  only ONE instantiation per application (the first match, e.g. `Lamᵀᵀ`
  but not `absLamᵀᵀ` in the same hypothesis). For several double-transpose
  instances in one hypothesis use `simp only [Matrix.transpose_transpose] at h`.
- (record 1119 additions) `Matrix.ext_iff : (∀ i j, M i j = N i j) <->
  M = N` - `.mp` goes entrywise→equality, `.mpr` equality→entrywise.
  When a goal is already entrywise, avoid the lemma entirely: prove the
  equation as a local `have ... := by rw [...]` and use it as a fact.
- (record 1119 additions) a docstring must sit IMMEDIATELY before the
  declaration keyword; `set_option ... in` goes BEFORE the docstring
  (reverse order = syntax error at the docstring).
- (record 1119 additions) `all_goals (t1; t2)` errors "No goals" when t1
  closes a branch entirely; `<;>` is safe but fires the
  `unnecessarySeqFocus` linter ONLY when t1 leaves exactly one goal in
  EVERY branch (then `;` is provably safe). Decide per-declaration from
  the build log, not globally.
- (record 1119 additions) an anonymous `(fun i j => ...)` in
  matrix-multiplication position fails HMul synthesis (the `binop%`
  collector does not coerce lambdas to Matrix). Use a genuine Matrix
  built with `•` (`(2 : ℝ) • M`) plus `Matrix.mul_smul` /
  `Matrix.smul_mul` (note: `Matrix.mul_smul` is PROTECTED - full name
  required despite `open Matrix`).
- (record 1119 additions) grepping the Mathlib tree is UNRELIABLE for
  name existence (several real lemma names live behind generated/opaque
  locations). Definitive check: scratch file with `#check <full name>`,
  run `lake env lean scratch.lean` on the mirror, then delete the
  scratch from BOTH trees.
- (record 1119 additions) dropping an UNUSED explicit parameter from a
  generic theorem's signature (e.g. `dd` pinned anyway by `hslack`'s
  type, or a hypothesis `hLamL` never referenced) is cleaner than
  `_dd`/`_hLamL` silencers and keeps the call sites honest - do the
  signature surgery in the same root-caused fix commit as the warning
  it removes.
- (record 1120 additions) `L=path; tail $L` style shell VARIABLES inside
  `wsl.exe -- bash -c '...'` UNRELIABLY expand across the Git-Bash/WSL
  boundary: observed `$L` expanding EMPTY mid-script (the `ls -la $L`
  silently listed the CWD instead of erroring).  Always inline the
  literal path in each command of a wsl one-liner; reserve variables
  for scripts WRITTEN TO the mirror and executed as files.
- (record 1120 additions) the ext4 mirror is synced file-by-file, so
  docs/proofs JSON inputs may be MISSING on the mirror even when the
  .lean tree is complete - a probe script that reads committed JSON
  must have its inputs copied explicitly (ls the mirror dir, or just
  cp the inputs together with the script) before running.
- (record 1120 additions) `#print axioms` lines for LONG declaration
  names wrap across log lines, so line-based grep reports false
  non-standard axiom lists (7 phantom hits on a fully-green build).
  Rejoin records by bracket matching (accumulate until `Quot.sound]`
  is seen) before pattern-checking - Python on the mirror is the
  reliable joiner; awk one-liners mis-handle the continuation logic.
- (record 1120 additions) `rw [Matrix.mulVec_mulVec]` is
  direction-agnostic for proving `M.mulVec (N.mulVec x) = (M * N).mulVec x`:
  whichever way the lemma is stated, rewriting either side makes the
  `have` goal rfl-closed.  Use this shape instead of guessing `<-`
  direction; then `rw [hRK, Matrix.zero_mulVec]` finishes a C1-style
  kernel discharge in three tactics.
- (record 1123 additions) A declaration whose CONCLUSION is a structure
  (e.g. `ICStageBContraction g`) is a `(noncomputable) def`, never a
  `theorem` - Lean rejects it with "type ... is not a proposition", and
  any audit `example` returning that def's output must itself be
  `noncomputable example`.
- (record 1123) `refine` cannot synthesize an implicit argument that
  appears in NO conclusion field (e.g. `absolute_spanK_q*`'s `y` lives
  only in hrep/hnorm); pin it by name: `refine f (y := ...) ?_ ?_`.
- (record 1123) `rw [← h]` fires on EVERY syntactic occurrence of the
  pattern, including copies inside `Real.sqrt`/inv subterms - nesting
  garbage.  Use `nth_rewrite N [← h]` to hit a specific occurrence.
  Also `← mul_assoc` needs a RIGHT-associated product; after `pow_two`
  the goal is left-associated, so plain `mul_assoc` comes first.
- (record 1123) `simpa using h` cannot reduce projections of an APPLIED
  def without its equation lemmas: write `simpa [def-name] using h`.
- (record 1123) `Q28/Q38/Q48.K` are RECTANGULAR `Matrix (Fin 8) (Fin 5) ℝ`
  (8 window tests, 5-dim class space); helper lemmas about `K.mulVec`
  must not specialize to square matrices.
- (record 1123) hypotheses carried for CONTRACT shape only (E1's
  budget slot, unused in the body) get an underscore name to keep the
  zero-new-warnings gate.
- (record 1218 additions) `+/-` inside a Lean DOC COMMENT is a
  nested-comment opener: Lean block comments NEST, so `/-- ... +/- ...
  -/` swallows the real terminator and the file dies with
  "unterminated comment" one module later.  Write `+-` in any emitted
  or hand-written comment text.
- (record 1218) `(simp [...]; norm_num)` fails "No goals to be solved"
  when simp CLOSES the focus (new data with exact-zero entries does
  this).  Robust shape: `(simp [...] <;> norm_num)` - `<;>` applies
  norm_num to whatever goals survive, including zero.
- (record 1218) heartbeat-raise archaeology: grep the generic
  `maxHeartbeats [0-9]+`, NOT a remembered literal - the parent used
  `20000000` (2e7) and a grep for `2000000000` (2e9) returned 0 hits,
  producing a false "parent has no raises" conclusion.
- (record 1218) `Set.Ioo (-2 * a)` and `Set.Ioo (-(2 * a))` are NOT
  defeq (numeral placement); match the parent statement's form exactly
  or the lemma application type-mismatches.
- (record 1218) generated-instance namespace nesting: an instance
  `Q28M` declared inside `namespace C1WindowRationalIngest` is reachable
  only as `C1WindowRationalIngest.Q28M.top`; audit `#print axioms`
  paths and `open`s must use the FULL nested path.
- (record 1218) audits must `open` every namespace they consume
  lemmas from (`ratio_headline`/`absolute_headline` live in
  `C1GateLevelTransferClasses`, not where the consumer defined them);
  one missing open = one build iteration.
- (record 1326 additions, 1539 batch) `rw [lemma]` where a LEMMA
  PARAMETER does not occur in the lemma statement (e.g. an `p` used
  only by the proof) leaves the pattern metavariable UNASSIGNED and rw
  appends a RESIDUAL GOAL of that parameter's type — observed as
  `⊢ CCM24VisiblePrime` tagged `case p` (the binder name becomes the
  goal tag).  Fix: instantiate explicitly at the call site
  (`rw [lemma p S _]`), or drop the phantom parameter.
- (record 1326) `rw [map_add]` splits only the FIRST matching
  instantiation: for `g (f (a + b))` the inner `f (a+b)` goes first and
  the outer `g (sum)` stays; chain `rw [map_add, map_add]` (one per
  layer) or the next rw in the chain "did not find" the pattern.
- (record 1326) `rw [hSplit]` whose atom appears in MANY statement
  positions rewrites ALL of them — including inside the goal's own RHS
  — destroying the target form.  Use a bridge `have step1 : lhsA = lhsB
  := by rw [← hsplit]` and close with `exact hbd.trans (step1.trans
  hadd)`; term-level `Eq.trans` chains check only the paired middles
  (no kabstract search).
- (record 1326) a chained `rw [hbd, step1, hadd]` over huge CLM-coe
  terms can die in kabstract `isDefEq` with the FULL 200000-heartbeat
  budget ("deterministic timeout at isDefEq") even when every rewrite
  is syntactically fine; the `Eq.trans` + `exact` form is O(1) and
  immune.
- (record 1326) `calc ‖( … ` — a calc LHS that is a NORM opening
  directly with a paren and spanning multiple lines fails to PARSE
  inside a by-block ("unexpected token '('; expected '‖', '‖₊' or
  '‖ₑ'" + "Unexpected syntax" at the calc keyword) even though the
  same term parses fine in statement position; rewrite the proof as
  ascribed `have hA := lemma term` chains joined by
  `exact le_trans hA (le_trans hD (le_trans hB hC))`.
- (record 1326) lemmas shaped `‖(I - P) ?u‖ ≤ ‖?u‖` bind `?u` on BOTH
  sides — using them twice in one `le_trans … ?_` refine lets the RHS
  `‖x‖` assign `?u := x` first, producing a wrong middle term; spell
  each intermediate `have` with its concrete term instead.
- (record 1326) `gcongr` on `‖A‖ + ‖c • Y‖ ≤ x + c * ‖Z‖` does not
  produce the two expected subgoals when the sides are not additively
  parallel (it may auto-normalize the smul and leave one goal); use
  explicit `add_le_add hint le_rfl` with the calc-step target
  restructured to carry the `(I - P)` inside, then a final
  `add_le_add le_rfl (mul_le_mul_of_nonneg_left …)` to the statement
  form.
- (record 1326) Lake v4.30 change detection is CONTENT-HASH based:
  `touch file.lean` does NOT force re-elaboration (no-op rebuild,
  exit 0, and the resource wrapper's `--log` capture then writes an
  EMPTY log file).  To force: delete the module's `.olean` (7a rule)
  or edit content meaningfully.  For a citable green log of a warm
  no-op-adjacent build, run `lake build > log 2>&1` inside a script
  FILE (never shell vars in wsl.exe one-liners — 7a rule re-burned
  2026-09-11).

- (record 1327 additions, 1540 batch) `prefix` is a RESERVED Lean 4
  command token (notation-declaration syntax) and cannot be a binder
  identifier: the theorem statement dies at the binder with
  "unexpected token 'prefix'; expected '_' or identifier" and every
  declaration after it cascades into phantom parse/elaboration errors.
  Use `pull`/`pre`; ordinary identifiers CONTAINING the token (a longer
  theorem name) are fine.
- (record 1327) `CCM24FiniteSActualSchurCascade` declares the
  `sourceSoninCarrier` CompleteSpace witness as `noncomputable LOCAL
  instance` — `local` instances are NOT exported to importers.  Any new
  file stating theorems over `sourceSoninCarrier` must re-declare it:
  `noncomputable local instance … : CompleteSpace (sourceSoninCarrier
  lambda) := (ccm24ArchimedeanSoninClosedSubspace
  lambda).isClosed.completeSpace_coe` (the ClosedSubmodule lives in
  `CC20Concrete.CCM24HardyTitchmarsh`, exported).  Expect the failure
  signature "failed to synthesize instance of type class
  CompleteSpace ↥(sourceSoninCarrier unitSoninScale)".
- (record 1327) `PositiveTrace.summable_adjoint_normSq` sits one
  namespace DEEPER than the file top: inside
  `namespace BasisHilbertSchmidtPairData` (lines 257-624).  Call it as
  `BasisHilbertSchmidtPairData.summable_adjoint_normSq` (with
  `CC20Concrete.PositiveTrace` opened); the bare name does not resolve.
- (record 1327) Mathlib v4.30 `Summable.congr` is the DIRECT form
  `Summable.congr (hf : Summable f) (hfg : ∀ b, f b = g b) : Summable g`
  (summability FIRST, then pointwise equality) — not the iff-shaped
  `congr (h : ∀ b, f b = g b) : Summable f ↔ Summable g`; feeding it a
  lambda produces "Application type mismatch … expected `Summable ?m
  ?m`".
- (record 1327) dot-notation `.adjoint` on a parenthesized `∘L` chain
  can get STUCK ("typeclass instance problem is stuck
  SeminormedAddGroup ?m") because the projection elaborates before the
  chain's endpoints are known; write
  `ContinuousLinearMap.adjoint (chain)` explicitly.
- (record 1327) when pairing `Summable.of_nonneg_of_le` with
  `Summable.mul_left`, the multiplication constant must match the calc
  SQUARE — `‖·‖² ≤ c²·‖·‖²` needs `mul_left (c^2)`, not `mul_left c`;
  the mismatch surfaces as a nonsense leftover goal `c^2 * X² ≤ c * X²`
  inside `case calc.step`.  Also `sq_le_sq' (h1 : -b ≤ a) (h2 : a ≤ b)`
  needs BOTH norms nonnegative in the linarith context: one
  `norm_nonneg _` for the RHS alone is not enough — name two `have`s
  (hA/hB) and let `linarith` see the context.
- (record 1327) batch logs live in `/home/peter/rh/build-logs/` (not
  `logs_local/`); a bad redirect path makes the redirect fail BEFORE
  lake starts and the wrapper still exits 0 — check the log file
  exists before believing any exit code.
- (record 1328 additions, 1541 batch) `Summable.tsum_finsetSum` in this
  Mathlib PULLS the tsum inward:
  `(∑' a, ∑ b ∈ s, f b a) = (∑ b ∈ s, ∑' a, f b a)` with pointwise
  hypothesis binders `fun b _ => summableProof` (finset element first,
  membership binder ignored).  To push a finset sum OUTWARD across a tsum
  (the shape needed by partial-sum comparisons) use the SAME lemma with
  `.symm` — the hypothesis binds over the finset index either way.
- (record 1328) `tsum_mul_left` (Ring.lean) is UNCONDITIONAL with implicit
  `(f) (a)` in v4.30: `∑' x, a * f x = a * ∑' x, f x`.  Never pass
  explicit arguments — `(tsum_mul_left _ _)` fails with "Function expected
  at tsum_mul_left".  Use `rw [tsum_mul_left]` (repo idiom) or
  `le_of_eq tsum_mul_left` in a chain.
- (record 1328) `mul_le_of_le_one_left (hb : 0 ≤ b) (hc : c ≤ 1) :
  c * b ≤ b` vs `mul_le_of_le_one_right (ha : 0 ≤ a) (hb : b ≤ 1) :
  a * b ≤ a` — pick by where the SMALL FACTOR sits in the goal; passing
  the wrong variant yields `S * c ≤ S` where `c * S ≤ S` was needed.
- (record 1328, REPEAT-OFFENSE note) `sq_le_sq'` first hypothesis is
  `-b ≤ a`, NOT `0 ≤ a` (already banked above from 1327 and re-tripped);
  and `linarith`/`norm_nonneg _` must see the atom AS WRITTEN in the goal
  — a `pull.adjoint (column.adjoint x)` fact does not match a
  `(column ∘L pull).adjoint x` goal atom; `nlinarith` with explicit
  per-atom `norm_nonneg` facts is the robust square-comparison closer.
- (record 1328) wsl.exe quoting hazard, NEW CLASS: nested double quotes
  inside a `bash -c '...'` argument — `echo "X: $(grep -ac "error:" $L)"`
  silently terminates the outer string, mangles the grep pattern, and
  returns a bogus `0` count that contradicts `tail` output.  Put grep
  patterns in the SINGLE-quoted region with no nested double quotes, or
  run a script file.  (Extends the "never shell vars" rule: quotes inside
  quotes are equally unsafe.)
- (record 1330) a.e. indicator proofs, three coupled traps: (a)
  `Set.indicator_of_not_mem` and `le_of_not_lt` are NOT names in this
  Mathlib era — normalize with `simp only [Set.indicator_apply,
  Set.mem_Iio, Set.mem_Ici]` to the if-form FIRST, then close branches
  with `if_pos` / `if_neg (by linarith : ...)`; (b) `rw` of a scale
  equality INSIDE an if-condition dies with "motive is not type correct"
  because the `Decidable` instance depends on the rewritten Prop — only
  `simp only [h, add_lt_add_iff_right]` carries that dependency (put the
  hypothesis `h` in the simp list); (c) lifting a function-level equality
  into `=ᵐ[volume]` needs a POINTWISE forall (`ae_of_all volume (fun x =>
  congr_fun h x)`; for Lp-element equalities `DFunLike`/`FunLike.congr_fun`
  names are unavailable/instance-stuck — `rw [ContinuousLinearMap.comp_apply]`
  in the have-target instead); ACLM→`.toContinuousLinearMap` application is
  defeq and accepted under explicit ascription.
- (record 1330) `CLM` pointwise bound idiom: `ContinuousLinearMap.le_opNorm
  _ _ : ‖f x‖ ≤ ‖f‖ * ‖x‖` (repo green precedent
  C1G8P1RadialCommutatorChannelLedger.lean:150); `norm_apply_le` and
  `map_norm_le_opNorm` DO NOT exist in this version.  Unfold
  `radialComplement` at the ELEMENT level (`simp only [radialComplement,
  ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]`) then read
  back a.e. via `Lp.coeFn_sub` — a `show`/`simp` at the COERCED-FUNCTION
  level gets stuck on the coercion normal form.  Square comparisons:
  `(sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h`, not `sq_le_sq'`
  (that one is an implication, no `.mpr`).
- (record 1330) consumer checklist for the CCM25 radial stack: opening
  `...AntiresonantRadialBlockRecurrence` alone is NOT enough —
  `newFrameAntiresonantColumn` / `radialSupportProjection_comp_newSuffixFrame`
  live in the `...RadialSplit` namespace, `sourceSoninCarrier` lives in
  `CCM24FiniteSFrameGramCalculus`, and the `CompleteSpace (sourceSoninCarrier
  λ)` instance is `local` (redeclare per consumer from
  `(ccm24ArchimedeanSoninClosedSubspace λ).isClosed.completeSpace_coe`);
  mirror the 1324 leaf header exactly.
- (record 1356, B1 session 1556->1556c) THREE TRAPS, each cost one red
  build: (1) METAVAR INSTANTIATES ONCE - `rw [abs_mul]` unifies the lemma
  pattern against the FIRST match only; two summands `|2*x| + |2*y|` are
  different instances, so the second survives untouched and a "deduped"
  rw list silently under-rewrites. Rewrite-all-with-all-matches is
  `simp only [abs_mul, abs_of_pos (show (0:ℝ) < 2 from by norm_num)]`.
  (2) COMMITTED ORDER IS THE CONTRACT - C1SpectralHermitianPartner's
  pair lemma is PARTNER-FIRST `(t (part rho) + t rho).re = 2*(t rho).re`
  (:171-176); a hand-written partner-LAST grouping needs `rw [add_comm,
  lemma]`. Grep the committed statement text, do not assume summation
  order from a paper formula. (3) ASSOC GAP AFTER PROJECTION SIMPS -
  `simp only [Complex.add_re]` leaves a 4-vs-2+2 parenthesization
  difference over ℝ that only `ring` closes.
- (record 1356 s6) `forall₂_congr` demands the pointwise iff in the
  SAME orientation as the two big iff's; when the per-item lemma reads
  gate-first and the locked statement contest-first, pass `(lemma g)
  .symm` - proof-level orientation, statement untouched (law-42-safe).
- (record 1356 s6, brick-era hygiene) After a green log, the file you
  COMMIT must be BYTE-IDENTICAL to the built mirror copy: even a
  doc-comment edit post-build gets reverted rather than drifting the
  verified bytes (`cmp` local vs mirror before committing).
- (record 1362 s7, L1 brick session) Probe the fork's Mathlib BEFORE
  designing any tsum/Fubini route: `HasSum.sigma`
  (HasSum f a -> per-fiber HasSum -> outer HasSum, AddCommMonoid +
  ContinuousAdd + RegularSpace) gives value-level fiber Fubini over ANY
  signed summable family - it KILLED the planned ENNReal ofReal-descent
  and the pos/neg decomposition entirely. Do not import memory of
  upstream lemma names: tsum_sigma/HasSum.comp_equiv/summable_sigma all
  ABSENT here; value transfer along equivalences needs one hand-rolled
  `hasSum_comp_equiv` (net of Finsets).
- (record 1362 s7) `(SummationFilter.unconditional L).filter` is DEFEQ
  to `Filter.atTop` on `Finset L` in this snapshot: after
  `unfold HasSum at hf ⊢`, a `show` to atTop passes and cofinality
  arguments go through `Filter.tendsto_atTop_atTop_of_monotone`.
- (record 1362 s7) `le_div_iff₀`/`div_lt_iff₀` here are stated with the
  DIVISION form on the LEFT (`a <= b / c <-> a * c <= b`): deriving the
  multiplication form from the division form takes `.mp` - the OPPOSITE
  of the memorized upstream direction (compiler caught both).
- (record 1362 s7) `Finset.sum_image` wants an explicit `Set.InjOn g ↑s`
  proof and `hf.injective.injOn s` mis-elaborates; pass
  `(show Set.InjOn e (↑s) from fun x _ y _ h => e.injective h)`.
  `rw` auto-closes `t ⊆ t` via the @[refl]-tagged subset lemma, so a
  trailing `exact` after such an rw errors "No goals".
- (record 1356 era + 1363) `linter.style.show` warns when `show`
  CHANGES the goal (defeq-rephrasing); non-fatal, but prefer `change`
  for goal-shaping steps. Five such warnings sit on record in batch
  1558's accepted log (lines 86/89/94/111/145 of C1A2WindowSplit).
- (record 1366 s3, batch 1559) `exact_mod_cast` is a TACTIC only in this
  fork: `refine exact_mod_cast (..)` fails ("Unknown identifier") and the
  bare `mod_cast` does not exist at all. Pattern: `have` the un-coerced
  fact, then `exact_mod_cast <lemma> <have>` in tactic position.
- (record 1366 s3) `Set.encard` is `Nat`-infinity-valued; `: ENNReal`
  annotations insert coercion nodes. `Set.eq_empty_of_forall_not_mem` is
  ABSENT from this import chain - use
  `Set.not_nonempty_iff_eq_empty.mp` (`.mp` = ¬Nonempty -> s = ∅, `.mpr`
  is the CONVERSE) then `exact_mod_cast Set.encard_eq_zero.mpr hempty`.
  Generic `zero_le _` mis-elaborates here ("Function expected"); pass an
  explicit `le_of_lt h`.
- (record 1366 hygiene near-miss) A combined ERE hygiene scan
  (`C:\\|/home/|...`) reported CLEAN while a known `/home/peter/` line sat
  at line 21 of the same file - a simple `grep -c "/home/"` caught it.
  Law: run hygiene scans as SEVERAL simple greps (one per family), never
  as one big alternation; validate any scan pattern against a known
  positive control before trusting an exit=1.
- (A7c recurrence, 1366) the sync+launch fuse trap fired AGAIN exactly as
  in 1225: `wsl.exe -c 'cp && cp && nohup ... &'` backgrounded the whole
  AND-chain and died mid-copy when the session exited. The fix that
  worked: foreground sync + md5 verify, then a SEPARATE launch under the
  harness background mechanism (or plain `run_in_background` bash call).
- (record 1368 s3, batch 1560) indicator vanishing on the NON-mem side:
  `Set.indicator_eq_zero_of_not_mem`/`Set.indicator_of_not_mem` are
  ABSENT; the working shape is `classical` +
  `rw [Set.indicator_apply, if_neg hn, Complex.zero_re]` (indicator_apply
  carries a `[Decidable _]` instance arg). `Set.indicator_of_mem` EXISTS.
- (record 1368 s3) register-name facts: `weilCriterion_iff_sourceRH`
  must be written `C1WeilCriterionEquivalence.weilCriterion_iff_sourceRH`
  (namespace not open by default; `.mp` = forall-gate -> SourceRH);
  `spectralTerm` lives under `open C1SpectralWeil`;
  `sourceNontrivialZeroSet` is a `Set ℂ` - as a binder it is the
  subtype (fields `.1`/`.2`; RH applies as `hRH rho.1 rho.2` - there is
  no `.isNontrivial`).
- (record 1375 s6) `mul_le_mul` args here are `(hab) (hcd) (0 <= c)
  (0 <= b)` - the nonneg side conditions cover the SECOND LHS factor and
  the FIRST RHS factor, not both sides of the goal.
- (record 1375 s6) `ring` cannot equate `4^n` with `2^(2*n)`: never close
  an equality that regroups powers of the COMPOSITE atom `(2*Real.pi)`
  across exponent groupings; keep constants composite and use
  `pow_add`/`mul_pow` + `ring` only for reordering.
- (record 1375 s6) nonneg witnesses: `sq_nonneg` needs a literal `^ 2`
  (use `pow_nonneg (norm_nonneg x) _` for `x^(2*(n+2))`); `norm_nonneg`
  takes the INNER term (`norm_nonneg (z.im / (2*pi))`, never
  `norm_nonneg ||z.im / (2*pi)||`); `pow_le_pow_left0`'s first arg is the
  whole product base.
- (record 1375 s6) calc tactic-block indent must be >= the expression
  lines of the same step; a shallower tactic line parses as an expression
  continuation ("expected '{' or indented tactic sequence") and cascades.
- (record 1375 s6) point decomposition `z = re + im * I`: do NOT rewrite;
  apply the bound at `(z.re, z.im)` and `simpa only [Complex.re_add_im]
  using h` (CC20YoshidaConvolution.lean:701-705 pattern).
- (record 1375 s6) a `noncomputable section` needs its own bare `end`
  before the namespace `end`s.
- (record 1375 s8) v4.30 `pow_mul : a^(m*n) = (a^m)^n` — forward rw rewrites the EXPONENT product of the composite base; to swap `(x^a)^b = (x^b)^a` use `rw [← pow_mul, ← pow_mul]` + targeted `mul_comm` on exponents.
- (record 1375 s8) `summable_geometric_of_lt_one`/`tsum_geometric_of_lt_one` take `(0 ≤ r)` (not `-1 < r`); the tsum form concludes `(1-r)⁻¹` — after rw into `1/(1-r)` shape close with `ring`.
- (record 1375 s8) `Summable.of_le` does NOT exist in v4.30 — use `Summable.of_nonneg_of_le (hg : ∀ b, 0 ≤ g b) (hgf) (hf)`; per-shell nonneg via `tsum_nonneg` + rfl-unfold + `mul_nonneg`.
- (record 1375 s8) `field_simp` cancels NUMERAL-base powers (`3^m`, `(2π)^k`) silently and leaves a `pow_add`-shaped residual; close with exponent-ring rewrite + `pow_add` + `pow_one` + `ring`.
- (record 1375 s9) Premise ORDER is semantics: referencing `N` before its `(N : ℕ)` binder auto-binds a DIFFERENT variable (`N✝`) — application fails with two distinct N's; bind early.
- (record 1375 s9) `healthyDetectorData_halfDensityShift_of_raw_values_of_spectral_neg` takes the detection value in `bne` form — bridge with `(bne_iff_ne).mpr hdetect`.
- (record 1375 s9) `halfDensityShift_support_subset`: the exp(x/2) multiplier preserves support EXACTLY (no shift) — detector support clause = assembled `(n+1)`-window verbatim.
- (record 1375 s9) Nonmembership hypotheses (`↑z ∉ targetNodes`) are plain implications, NOT subtype memberships — no `.1/.2` projections.
- (record 1375 s10) `exact_mod_cast` does NOT exist in this Mathlib ("Unknown identifier"); `0 < (↑k : ℝ)` from `0 < k` goes through `Nat.cast_pos.mpr`.
- (record 1375 s10) BY-BLOCK GARBAGE LAW: a `by tac` in an ARGUMENT position whose expected type still has unassigned metavars (first arg of `mul_le_mul_of_nonneg_right (by linarith) hX`, `le_of_eq (by ring)` inside `le_trans`) elaborates against GARBAGE instantiations (manufactured a monster `K²·r^(2N)` goal) and splatters phantom failures onto unrelated lines. State the inequality/equality as a separate `have` with a FULLY CONCRETE type first, or `refine ... ?_` so later args fix metavars.
- (record 1375 s10) `mul_le_mul_of_nonneg_left (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b`; `_right` multiplies on the right. `_right (by linarith) hX` was both the wrong direction AND a by-block.
- (record 1375 s10) `ring`/`ring_nf` cannot flatten `(x^a)^b` for VARIABLE exponents nor equate numeral-base variants (`2^(8(N+1))` vs `256^N`): all pow-pow forms must be rewritten via `← pow_mul`/`pow_add` BEFORE `ring`.
- (record 1375 s10) `field_simp` may close a simple equality completely; a trailing `ring` then errors "No goals to be solved". Robust idiom: `field_simp ... <;> ring`.
- (record 1375 s10) A FAILED composite tactic rolls back and its DISPLAYED residual is `ring_nf`-normalized — misleading vs the true post-`field_simp` state. Never write the next fix against a rolled-back display; probe with an identity `rw` first.
- (record 1375 s10) This Mathlib's `mul_div_mul_comm : a * b / (c * d) = a / c * (b / d)` — the ← direction MERGES a product of divs into one div. In div-normalization chains run every ← merge while the target div is still top-level CLEAN, before `mul_div_assoc` steps nest it.
- (record 1375 s10) OPS LAW RE-CONFIRMED (try-8 built a STALE file): `cp … && cmp … && nohup … & echo` — `&` binds looser than `&&`, the whole chain backgrounded and wsl.exe killed it. Sync (foreground, `cmp` + marker `grep`) and build launch are separate harness calls, never one `&`-chain.
- (record 1375 s10) `grep '\b…'` fails after a multibyte char (`₀`): `\b` is byte-oriented. Use prefix matching in log-greps over Lean identifiers.
- (record 1375 s11) `∧` binds TIGHTER than `→`: `A ∧ B ∧ c → D` parses as `(A ∧ (B ∧ c)) → D`. Parenthesize conditional tails in ∃-statements (`... ∧ (hypo → conclusion)`) and close the paren at the end.
- (record 1375 s11) Anonymous-constructor flattening spans ∃ and ∧ together: against `∃ n, ∃ g, P ∧ Q` the 3-component form `⟨n, x, Y⟩` reads x as the g-witness and Y as P. To supply a whole nested ∃ as one component use the 2-component form `⟨n, proofOfExistsG⟩`.
- (record 1375 s11) The Hermitian square-kill bridge (`selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero`) consumes ASSEMBLED kills. Raw correction kills transfer in two lines (`rw [laplaceAt_convolution, laplaceAt_convolutionIterate, hraw]; simp`) — a zero factor kills the product, no base-value hypothesis needed at kill nodes.
- (record 1375 s11) `#print axioms` lists WRAP across build-log lines: a single-line pattern for the full axiom set finds nothing. Verify via (a) print count, (b) `grep -A1` continuation class size 1 (`uniq -c`), (c) one `Quot.sound]` per print.
- (record 1375 s12) `Nat.lt_pow_self (hb : 1 < b) {n : ℕ} : n < b ^ n` — `n` is IMPLICIT (inferred from the expected type); never feed it explicitly, and give the intermediate step its own typed `have` (`h2k : (k:ℕ) < (2:ℕ) ^ k`).
- (record 1375 s12) Cast lemmas (`Nat.cast_lt.mpr` etc.) with `have h := …` UNANNOTATED leave the typeclass target as a metavariable → "stuck, CharZero ?m". Always write `have h : <full type> := …`.
- (record 1375 s12) Even ANNOTATED, the annotation elaborator-normalizes `((2 : ℕ) ^ E : ℝ)` to `(↑2) ^ E`, mismatching the lemma's output `↑(2 ^ E)`. Annotate in the lemma's OWN output shape (`((2 ^ E : ℕ) : ℝ)`), then `rw [Nat.cast_pow, Nat.cast_ofNat] at h` to normalize after.
- (record 1381 additions, all hit on the C1CompactLogL2Export build loop) Two-namespace split for the B5 register: the TYPE `CompactLogTest` lives in `CCM25Concrete.CompactLogConvolution` while `laplaceAt`/`exponentialWeight`/`exponentialWeight_apply` live one level deeper in `CC20YoshidaConvolution.CompactLogTest` — a Dev leaf needs BOTH `open CCM25Concrete.CompactLogConvolution` and `open CC20YoshidaConvolution.CompactLogTest`.
- (record 1381) `intervalIntegral.integral_nonneg` takes `hab : a ≤ b` as its FIRST explicit argument, then the pointwise hypothesis; but `ContinuousOn.intervalIntegrable` takes NO `hab` (valid for both orientations). Do not guess arg shapes between the two families.
- (record 1381) `sq_nonneg` is POWER form (`0 ≤ a ^ 2`), `mul_self_nonneg` is gone from v4.30: state squared-window integrands in power form (`u x ^ 2`), square via `ContinuousOn.pow 2`. Power and mul spellings of the same square are NOT defeq — one wrong spelling starves the whole rw chain.
- (record 1381) `Set.Ioc` is LEFT-open right-closed (`a < x ∧ x ≤ b`); Ioo→Ioc membership is `⟨hxc.1, le_of_lt hxc.2⟩`. And `measurableSet_Ioc` is ROOT-level in v4.30 (`Set.measurableSet_Ioc` is an Unknown constant).
- (record 1381) A failing `rw` ABORTS the whole tactic block: later tactics never elaborate and report NOTHING. Read build-log errors top-down and fix only the first failure per iteration; absence of errors below a failure is NOT evidence those lines work.
- (record 1381) Rewriting inside a spliced ∀-hypothesis (`have h1 := hnonneg T`) requires the pattern to be a syntactic SUBTREE of the instantiated type. `hnonneg`'s shape `(C + 2*t*B) + t*t*A` groups the leading C with the middle term — the rewrite equation must carry the FULL expression including C; a pattern grouping the last two terms alone matches nothing.
- (record 1381) `integral_congr_ae` refined directly against an INEQUALITY goal strands `?G` as a metavariable and dies on a stuck `NormedSpace ℝ ?m` typeclass; route through `refine le_of_eq ?_` first (Eq-unification pins G), or `beta_reduce` first. `show` used as beta-reduction trips the show-linter — use `beta_reduce` (Mathlib/Tactic/DefEqTransformations.lean).
- (record 1381) Coercion through the `TestFunction` alias (= SchwartzMap ℝ ℂ) in a `have` STATEMENT sticks typeclass search (`NormedSpace ℝ ?m`) because the elaborator must unfold the alias to find FunLike while G is a metavariable: annotate `((e.test : ℝ → ℂ) x)` in the statement. Goals produced by already-elaborated register definitions are safe.
- (record 1381) `integral_add` splits the tree `(A+B)+C`: the middle hypothesis must be `h1.add h2` paired with `h3` (a three-term `hsum` matches nothing). `intervalIntegral.integral_const_mul` is needed once PER DISTINCT constant.
- (record 1382 try25-30, complex-Gram conventions to lean on) `inner_smul_right x y r : ⟪x, r•y⟫ = r * ⟪x,y⟫` (SECOND slot linear, no star); `inner_smul_left : ⟪r•x, y⟫ = r† * ⟪x,y⟫`; `inner_sum s f x` is second-slot additivity, `sum_inner` the first-slot version; `Matrix.gram_apply : gram 𝕜 v i j = ⟪v i, v j⟫`; `star_dotProduct_gram_mulVec : star x ⬝ᵥ (gram 𝕜 v) *ᵥ y = ⟪∑ i, x i • v i, ∑ i, y i • v i⟫`. THIS Mathlib's `dotProduct` (⬝ᵥ) is PLAIN bilinear `∑ v i * w i` (no hidden star) and is reachable as bare `dotProduct` — `Matrix.dotProduct` is an Unknown constant.
- (record 1382) `rw` higher-order matching is CAPTURE-SENSITIVE: goal `∑ x, ⟪v i, v x⟫ * c x = ⟪v i, ∑ i, c i • v i⟫` (RHS binder shadows free node var `i`) makes `rw [inner_sum]` say "did not find an occurrence"; `rename_i` renames the LAST introduced binder (the instance! tactic state lists instances last), not the shadowed one. Law: never rw under a shadowing binder — drive with a `trans` chain of `Finset.sum_congr rfl` + `intro x _` + local `rw`, and apply API lemmas with ALL explicit arguments.
- (record 1382) `calc` step parsing chokes on `∑ x, ...` binder commas and on nested `:= by` step proofs even with parenthesized sums; `trans` chains are the drop-in replacement in sum-heavy modules.
- (record 1382) `norm_sub_sq (x y : E)` does NOT infer 𝕜 from the vectors — stuck `InnerProductSpace ?m E` — always pass `(𝕜 := ℂ)`. `⟪ ⟫`, `†`, and dot-notation `re` are Mathlib-LOCAL notations: outside those files write `@inner ℂ E _` and `RCLike.re z` term-style. To take `re` of a real-cast power: `(RCLike.ofReal_pow r 2).symm` then `RCLike.ofReal_re`.
- (record 1382) `simp` will not unfold a def-wrapper predicate stored in a hypothesis (`FiniteMellinMomentMatches := ∀ ...` gives "simp argument hy unused"); expose it first by defeq: `have hys : ∀ i, @inner ℂ E _ (representer i) y = cfg.target i := hy`.
- (record 1382) `rw`'s auto-close is REDUCIBLE-transparency only: a plain-def defeq gap (`‖∑ i, ...‖` vs `‖synthesis‖`) survives as a residual goal — end the rw chain with an explicit `rfl`.
- (record 1382) `congrArg (fun z => ...)` lambdas need a domain annotation (`(fun z : ℂ => RCLike.re z)`) or class search sticks on the unelaborated lambda domain.
- (record 1383, window-Gram leaf) `λ` is NOT a legal identifier character in Lean 4: `hλ` is a parse error ("unexpected token 'λ'"). Use `hlam`.
- (record 1383) Cast spelling for `rw`: `RCLike.ofReal_pow`/`RCLike.ofReal_re` print as `↑` but are NOT the head that `(r : ℂ)` ascriptions elaborate to, so `rw` rejects them ("did not find ↑?m ^ 2" against a visually identical target) while `exact`/`.trans`/`show` accept them via defeq. LAW: term mode crosses the RCLike/Complex cast split, `rw` does not — for rw chains over ℂ use `Complex.ofReal_pow` and `Complex.ofReal_re`.
- (record 1383) A type ascription `(∫ x in a..b, ‖W x‖ ^ 2 ∂volume : ℂ)` PROPAGATES the expected type into the integral: it elaborates as the ℂ-valued integral with the cast INSIDE the integrand and the power outside the cast — `(fun x => (‖W x‖ : ℂ)^2)`. The printed form `∫ x, ↑‖W x‖ ^ 2` hides this. To force a genuine cast-of-whole-integral write the coercion notation `↑(∫ ...)` or the double ascription `((∫ ... : ℝ) : ℂ)`.
- (record 1383) A bare `↑t` inside `‖↑t‖ ^ 2` with nothing forcing the codomain to be ℂ can resolve to the IDENTITY coercion ℝ → ℝ (the printer drops it silently, yielding a real absolute value). `Complex.sq_norm` then finds no occurrence. Fix by double ascription: `‖((∫ ... : ℝ) : ℂ)‖ ^ 2`.
- (record 1383) `by`-blocks placed in LEMMA-ARGUMENT position (`integral_congr fun x _ => by simp [h]`) elaborate against unresolved function metas: simp sees `?f x = ?g x`, fires nothing, and reports "unused simp argument". First `refine` the congruence so the goal pins f and g, then rewrite.
- (record 1383) `h.trans ?_` chains: the intermediate RHS meta is never pushed into the next lemma's proof argument, so inner `?_` holes die with "don't know how to synthesize implicit argument". Fix: each intermediate equality becomes a fully TYPED `have` with the displayed sides spelled out, then `exact (e1).trans ((sum_congr rfl fun j _ => hj j)).trans (mul_sum _ _ _).symm`.
- (record 1383) `rw [a, b] at h ⊢` runs the whole item list PER TARGET: if `b` matches in `h` but has no occurrence in `⊢`, the rw aborts ("did not find" showing the failed target), even though `a` would have sufficed there. Split into `rw [a] at h ⊢` then `rw [b] at h`.
- (record 1383) Mathlib `set x := e with hx` abstracts occurrences of `e` in the GOAL only. A subsequent `rw [← hx] at ⊢` finds no occurrence and fails while hypotheses look untouched. Prefer continuing with the full displayed expression (or rewriting only the hypotheses by `← hx` and leaving the goal in the abstracted form).
- (record 1383) Lemma-argument position does NOT auto-insert membership binders: passing a plain `∀ x, HasDerivAt f v x` to `integral_eq_sub_of_hasDerivAt` (slot `∀ x ∈ uIcc a b, HasDerivAt f (f' x) x`) fails at argument elaboration because the endpoint/derivative metas are still open. Hand-write `have hF' : ∀ x ∈ Set.uIcc a b, HasDerivAt f ((fun z => v z) x) x := fun x _ => hF x` and note the RHS slot must be in FUNCTION form `(fun z => ... ) x`, not the raw value.
- (record 1383) Dot form `Complex.ofRealCLM.hasDerivAt` takes NO explicit `x` (the point is auto-bound in the theorem's own type); appending `x` gives "Function expected". The `have` ascription supplies the point.
- (record 1383) After `convert h.const_smul c using 1`, the function-field goal can close by whnf-defeq (`•` unfolds to `*` for a field over itself) while the derivative-value goal (`c = c • 1`) survives: a following `· ext y` then reports "No applicable extensionality theorem found for type ℂ" and the next bullet "No goals to be solved". Use one `all_goals simp [smul_eq_mul]`.
- (record 1383) `Complex.norm_of_nonneg` DOES NOT EXIST. For `‖(r : ℂ)‖ ^ 2` use `rw [Complex.sq_norm, Complex.normSq_ofReal]` — note `normSq_ofReal` has RHS `r * r`, not `r ^ 2`. And `Complex.normSq_eq_conj_mul_self` is stated with the cast inside: `(normSq z : ℂ) = conj z * z`, so after `rw [Complex.sq_norm]` the forward rewrite into it needs no `←`.
- (record 1383) `intervalIntegral.integral_ofReal (μ := volume) : (∫ x in a..b, (f x : ℂ) ∂μ) = ↑(∫ x in a..b, f x ∂μ)` is the cast-pullback used by the leaf; the pointwise feeder is `(Complex.ofReal_pow _ 2).symm` and the matcher wants the integrand written `((r^2 : ℝ) : ℂ)` (inner `: ℝ` stops propagation).
- (record 1384) `dotProduct` and `dotProduct_zero` are BARE top-level names (`Data/Matrix/Mul.lean`); `Matrix.dotProduct_zero` does not exist and the prefix gives "unknown identifier".
- (record 1384) `Finset.induction_on` over a family carrying `[DecidableEq ι]` fires a "case inst, DecidableEq ι" obligation and the sibling-case membership `simp` dies silently; put `classical` at the very start of the proof.
- (record 1384) `𝓝` is a `scoped[Topology] notation` — `open Filter` alone gives "unknown identifier '𝓝'"; add `open scoped Topology`.
- (record 1384) `eq_neg_of_add_eq_zero_left`'s real direction is `a + b = 0 → a = -b` and `Finset.sum_insert` PREPENDS the new element: to isolate `cⱼ` from `cⱼ + Σ = 0` use `rw [Finset.sum_insert hj, add_comm] at hx0` first, and note `hF.congr_of_eventuallyEq hev` (the `=ᶠ[𝓝 x]` eq is the ARGUMENT to the HasDerivAt-bearing hypothesis, not the reverse).
- (record 1384) `filter_upwards [isOpen_Ioo.mem_nhds hx₀] with y hy` is the neighborhood-transport idiom (the tactic is `filter_upwards`, not `filter_up_feats`); `HasDerivAt.unique` then kills the constant `-(c j)` off the differentiated identity.
- (record 1384) `Set.uIcc` membership from `x ∈ Ioo a b` needs `le_of_lt` on BOTH sides before `min_le_left`/`le_max_right` chaining; a raw `le_trans hx₀.right` is a type mismatch (`hx₀.right : x₀ < b`, not `x₀ ≤ max`).
- (record 1384) To turn a hypothesis `nodes i = nodes k` into goal `nodes i - nodes k = 0`, do not `rw` at the goal (no difference term there): build `have hd : nodes i - nodes k = 0` by calc/ring against `sub_self`, then `sub_eq_zero.mp`.
- (record 1384) For `‖W‖ * ‖W‖ = 0 → ‖W‖ = 0` use `rw [← pow_two]` + `eq_zero_of_mul_self_eq_zero`; there is no `pow_eq_zero` simp shape.
- (record 1384) HEARTBEAT KILLER (200000, whnf deterministic timeout): a theorem's PROOF TERM embedded in a STATEMENT type — e.g. `let hG := windowExpGramMatrix_isUnit_of_injective ...` inside the type, or a refine hole substituting that IsUnit proof (which contains `Classical.choose` + a tactic block) into the cost theorem's argument — forces whnf of the whole proof. Fix: main theorem takes invertibility as an explicit `hG : IsUnit G` hypothesis; a thin corollary supplies it.
- (record 1384) Same whnf timeout hits when a constructed solution vector is injected through a refine hole at an application site inside a heavy proof: restructure as a standalone `have hsolve : G.mulVec w = y := by calc ...` and then plain `exact thm ... hsolve`, spelling `w` IDENTICALLY (including the `( : Matrix ι ι ℂ)` ascription) in both places.
- (record 1384) `Matrix.mulVec_injective_iff_isUnit` must be PINNED `(A := ...)` when the matrix's `Fintype`/`DecidableEq` instances are not solvable from the goal skeleton (stuck `Fintype ?m` in both `.mp`/`.mpr` refine styles); invertibility is the `.mp` direction (`Injective A.mulVec → IsUnit A`).
- (record 1384) `simpa only [Matrix.mulVecLin_apply]` can leave a stuck instance goal; spell the linearity step as `show ⇑(mulVecLin G) (u - v) = ⇑(mulVecLin G) u - ⇑(mulVecLin G) v` + `exact (mulVecLin G).map_sub u v`.
- (record 1384) `Matrix.mulVec_mulVec` is stated `M.mulVec (N.mulVec v) = (M * N).mulVec v` with args `(v M N)` — applied forward to `G.mulVec (↑h⁻¹ mulVec y)` it needs NO `.symm`.
- (record 1384) ENV LAW: the default `lake build` does NOT compile new Dev leaves (nothing imports them) — acceptance build must name BOTH modules explicitly (`lake build Dev.X Dev.XAudit`), and `lake env lean` on the Audit errors "olean does not exist" until the leaf is built: build before audit.
- (record 1385, taper-lift leaf) The `∞` in `ContDiff ℝ ∞ f` is SCOPED notation: a file with only `open scoped Topology` hits "unexpected token" on `∞`, and the parse error corrupts the whole enclosing `def` so that downstream CORRECT equations report bogus "not defeq / rfl fails" on their `.test x` evaluation. LAW: add `open scoped ContDiff` FIRST; only judge defeq failures after the parse is clean.
- (record 1385) The `cases'` tactic does not exist in Mathlib4 ("unknown tactic"): use `rcases le_total 0 a with ha | ha`.
- (record 1385) The right branch of `le_total 0 a` gives `a ≤ 0`, which `abs_of_neg` REJECTS (it needs `a < 0`): use `abs_of_nonpos` for the non-strict side.
- (record 1385) An implicit `{hab : a < b}` binder is SKIPPED by positional application: `f a b hab nodes coeff z` lands `hab` into the `nodes : ι → ℂ` slot with a type mismatch pointing at the wrong argument. Pass it by NAME: `f a b nodes coeff z (hab := hab)`.
- (record 1385) `rw [e, e]` fails on the SECOND pass — each rule rewrites ALL occurrences of its pattern in one go, so a repeated entry becomes a pattern-not-found error, not a no-op.
- (record 1385) `set x := t with hx` gives `hx : x = t`; a hypothesis created AFTER the set contains the UNFOLDED `t`, so naming it requires `rw [← hx] at h` while forward `rw [hx] at h` finds no `x` occurrence.
- (record 1385) The membership hypothesis under `intervalIntegral.integral_congr` is `x ∈ Set.uIcc p q` elaborated to the DISJUNCTIVE normal form `p ≤ x ∧ x ≤ q ∨ q ≤ x ∧ x ≤ p` (no `min`/`max` atoms to rewrite); `rcases Set.mem_uIcc.mp hx with h | h` and linarith the second disjunct with the width hypothesis.
- (record 1385) `Finset.sum_le_sum` / `Finset.sum_congr` inside a `.trans` chain whose right-hand side is pinned only by the LAST `?_` die with "don't know how to synthesize implicit argument g/b"; pin the companion function BY NAME: `(g := fun i => <full form>)`.
- (record 1385) `ContDiff.exp` (dot notation) for the complex exponential of an ℝ-source function leaves stuck `NormedSpace` metavariables; the working idiom is `h.cexp` (green: `hlinear.cexp` in CC20YoshidaConvolution.lean).
- (record 1385) The two infinities — native `(⊤ : WithTop ℕ∞)` and the coerced `↑(⊤ : ℕ∞)` printed by the `∞` notation — are NOT interchangeable at application boundaries at this pin: `by simpa using β.contDiff (n := ⊤)` still fails against a native-`⊤` ascription. LAW: use `∞` uniformly in every `ContDiff ℝ ...` binder; then `β.contDiff (n := ⊤)` and `hcompact.toSchwartzMap hsmooth` both pass with plain `:=`/application.
- (record 1385) After `rw [intervalIntegral.integral_const_mul]` pulls the constant out, the goal right side may still be the unfolded def form; append `rw [defName]` (here `windowTaperGram`) in the SAME rw list to close it.
- (record 1386, Young assembly leaf) `Integrable` is a `def` aliasing
  `And AEStronglyMeasurable HasFiniteIntegral`, so it has NO `const_smul`
  field: `hW.const_smul c` fails with "does not contain And.const_smul"
  (the `.const_smul` only exists on the two FACTORS, not the And). Law:
  rebuild it by hand `⟨h.aestronglyMeasurable.const_smul c,
  HasFiniteIntegral.smul c h.hasFiniteIntegral⟩`. NOTE `AES...const_smul`
  is `(hf) (c : 𝕜)` (hf implicit-receiver, c trailing) but
  `HasFiniteIntegral.smul` is `(c) (hf)` (c FIRST, no const_ prefix —
  `HasFiniteIntegral.const_smul` does NOT exist).
- (record 1386) `Integrable.mono'` third hypothesis is `∀ᵐ a ∂μ, ‖f a‖ ≤ g a`,
  NOT a pointwise `∀ a`; a bare `fun y => ?_` gives "type mismatch, function
  expected". Wrap with `Filter.Eventually.of_forall fun y => ?_` (the alias
  `eventually_of_forall` is NOT exposed; use the `Filter.Eventually.` prefix).
- (record 1386) `norm_eq_abs` is `Real.norm_eq_abs`; bare `norm_eq_abs` is an
  unknown identifier even under `open MeasureTheory`.
- (record 1386) `HasCompactSupport.comp_left (g : β → γ)` takes `g` as an
  IMPLICIT and the proof `g 0 = 0` as the ONLY explicit hypothesis, so
  `hGcN.comp_left (fun y => y^2) (by simp)` mis-binds (it reads the function
  as the `g 0 = 0` slot: "expected ℝ → ℝ but is Prop"). Pass the function by
  NAME: `hGcN.comp_left (g := fun y : ℝ => y ^ 2) (by simp)`.
- (record 1386) `intervalIntegral.integral_congr` consumes
  `Set.EqOn f g (uIcc a b)`, whose intro pattern is a TWO-argument binder
  `fun x _ => ...`; a `funext x`/one-arg lambda "could not unify funext".
- (record 1386) `⨆ i, ‖G i‖ * ‖G y‖` PARSES THE `* ‖G y‖` INSIDE THE BINDS
  (iSup has very low precedence). Parenthesize the sup:
  `(⨆ i, ‖G i‖) * ‖G y‖`. And `mul_le_mul_of_nonneg_right (le_ciSup ...) _`
  puts the bound factor on the RIGHT (`a ≤ sup → a * c ≤ sup * c`); when the
  majorant is `sup * ‖F t‖` you must `rw [mul_comm (⨆ i, ‖G i‖)]` first, and
  `mul_le_mul_of_nonneg_right (le_ciSup ...)` vs the `F`-weight needs the
  `left`-variant oriented for the `‖F t‖ * _` shape.
- (record 1386) `rw [hfun, intervalIntegral.integral_const]; simp` fails
  "no goals to be solved" — `integral_const` fires on the whole square so the
  intermediate `(1 : ℝ)^2`-as-constant collapses early; and the raw lemma
  returns `∫ ... (1)^2 = (d - c) • (1)^2` (the `^2` survives on the RHS under
  the smul). Prove it as a term: `have h : ∫ x in c..d, (1:ℝ)^2 = (d-c) •
  (1:ℝ)^2 := intervalIntegral.integral_const ((1:ℝ)^2); rw [h]; simp`.
- (record 1386) `rw [integral_smul]` fixes its `(?c, ?f)` metas on the FIRST
  matched occurrence; when a term has TWO distinct smul-integrals
  (`(2 s) • ∫Wb` and `(s s) • ∫W`) it rewrites only one per lemma NAME, so
  list `integral_smul` TWICE in the rw chain. `rw [h, h]` for an EXACT-repeat
  still fails (1385); the escape hatch is two different smul metas — for those
  the doubled name is required and correct.
- (record 1386) `Set.Ioo_subset_Ioc_self` is `Ioo ⊆ Ioc`; composing with
  `hsupp : support ⊆ Ioo` to get `support ⊆ Ioc` is `hsupp.trans
  Set.Ioo_subset_Ioc_self` (SUBSET.trans is forward: `h₁.trans h₂ : a⊆b, b⊆c`).
  The reversed `Set.Ioo_subset_Ioc_self.trans hsupp` is a type mismatch.
- (record 1386) The final `compactLogL2sq (f.convolution g)` transfer to the
  pointwise-convolution form is a bare `rfl` (the owner's `.test` is
  definitionally the convolution integral), NOT `congr 1; funext` — the
  latter leaves no goal at the `funext` ("No goals to be solved").
- (record 1387, consumer leaf) At this pin the POSITIVE-DENOMINATOR
  division-inequality lemmas carry the `₀` suffix: a bare `lt_div_iff` is an
  Unknown identifier. The working name is `lt_div_iff₀ (hc : 0 < c) :
  a < b / c ↔ a * c < b`
  (`Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:1131`); the
  negative-denominator siblings `lt_div_iff_of_neg` / `lt_div_iff_of_neg'`
  keep the unsuffixed spelling, which is why the name looks like it should
  exist. Same split applies to `div_lt_iff₀`. Cost: one build iteration
  (try1 = 2 errors, both this name; try2 = 0).
- (record 1387) Whnf-avoidance pattern that WORKED and should be the default
  for consumer leaves: when the upstream deliverable's conclusion contains a
  proof term inside the statement type (here
  `(windowExpGramMatrix_isUnit_of_injective ...).unit⁻¹` inside `K_loc`),
  MIRROR that spelling byte-identically in the consumer's hypothesis rather
  than introducing a `def` wrapper. A wrapper forces a defeq bridge back
  (`rfl` on a noncomputable def with instance-resolved coercions), while the
  mirrored spelling chains by plain `le_trans`. This is the consumer-side
  complement of the record-1384 `hG : IsUnit G`-as-hypothesis law.
- (record 1391) MIRRORING AT TERM LEVEL, NOT IDEA LEVEL. Copying the 1387
  `K_loc` template `↑(isUnit hab nodes hne).unit⁻¹\n y)) y).re)` while
  substituting `y -> (routeAlphaBaseValue rho)` BREAKS the paren algebra: a
  bare template argument `y` needs TWO closes after it (mulVec + star), a
  PARENTHESIZED named application `(X rho)` carries its OWN close and so needs
  THREE. Getting one of these off turns `dotProduct` into a partial
  application and the error surfaces at a DISTANT site as
  `failed to synthesize HMul ℝ ((? → ?) → ?)` — nine such cascades in try1/
  try2. LAW: when duplicating a nested template, count closes per bracket
  against the template, and before the build run a whole-file
  `( count == ) count` python check (1391 used it and it caught the last
  over-close).
- (record 1391) `congrArg Complex.re` does NOT push `.re` under an interval
  integral (the RHS stays `(∫ x, ↑f x : ℂ).re`), and `rw [integral_norm_sq_re]`
  expects the `((‖W x‖ : ℂ) ^ 2)` cast-placement on the SQUARE, not `↑(‖W x‖
  ^ 2)`. The compiled idiom (1385:98, re-armed in 1391) is: orient the
  quadratic lemma integral = dot, then `rw [← hqz, integral_norm_sq_re]` — the
  `ofReal_pow` defeq absorbs the cast shift. Do not hand-build the reduction
  with congrArg.
- (record 1391) `Matrix.mulVec G (G⁻¹.mulVec y) = y` at a let-bound
  `hG : IsUnit G` needs `[DecidableEq ι]` in the LEMMA SIGNATURE even when the
  proof never case-splits — the inversion notation resolves through
  `Fintype`/`DecidableEq` instances at ELABORATION time only.
- (record 1391) `simp only [f] at h1 h2 ⊢` does not finish a multiplicative
  normalization when the hypothesis it must consume is itself a simp result:
  after `h2 : laplaceAt u z = 1`, the close is the explicit
  `rw [h2, one_mul] at h1`. Reserve `simp` for the notation unfolds
  (`Subtype.val`, const) and fire arithmetic rewrites by hand.
- (record 1412) `rw [h]` on a SELF-REFERENTIAL hypothesis `h : a = -a`
  rewrites BOTH occurrences of `a` at once: goal `a + a = 0` becomes
  `-a + -a = 0` (then `abel` normalizes to the unprovable `-2 • a = 0`).
  Route through congruence instead:
  `(congr_arg (fun t => a + t) h).trans (by abel : a + -a = 0)`.
- (record 1412) `add_left_neg` is the `AddGroup` class FIELD
  (projection `AddGroup.add_left_neg`), NOT a global theorem —
  unqualified use is "Unknown identifier". Goal shapes `a + -a = 0`
  match `add_neg_self`, which is a simp lemma: plain `simp` after the
  pointwise rewrites closes them without name risk.
- (record 1412) `rw [integral_neg_eq_self]` (or any lemma whose LHS is
  `∫ x, ?f (-x)`) REFUSES a beta-redex `∫ x, (fun y => ...) (-x)` —
  "did not find an occurrence" even though it is the right identity.
  The proven template fix (`CC20YoshidaFullProduct.laplaceAt_involution`
  :159-172): `let`-bind the flipped integrand so the substitution is a
  first-order match against the local function constant. See law F19:
  transcribe proof skeletons, never reconstruct them from memory.
- (record 1413) `push_neg` on `¬(A ∧ b ≠ 0)` produces the IMPLICATION
  `A → b = 0`, not a disjunction — a following `rcases ... | ...`
  fails. For case splits on a decidable proposition `P` under
  `¬(P ∧ Q)`, skip push_neg: `by_cases hP : P`, and in the positive
  branch recover the zero by `by_contra hne; exact h ⟨hP, hne⟩`.
  Related spelling: `n.IsPrimePow` dot notation does not parse; write
  `IsPrimePow n`.
- (record 1413) `Finset.sum_congr rfl (fun n _ => lemma n)` wants the
  equation VERBATIM (`new = old₁ + old₂`); an instinctive `.symm` is a
  type error at the congruence argument, far from the wrong choice.
  Check direction against the statement's own RHS before adding symm.
- (record 1413) `simp only [integral_add h1 h2]` — a partially applied
  equation lemma whose LHS still contains unassigned metavariables —
  silently reports "simp made no progress" and closes nothing. `rw`
  instantiates those metavariables by matching, so the same term works
  as `rw [integral_add h1 h2]`. When simp declines a lemma you KNOW
  matches, suspect metavariables, not the shape.
- (record 1413) Function-extensionality witnesses feeding an
  `integral_*` rewrite must be a SINGLE lambda with `+`/`-`-headed body
  (`fun y => a y + b y`), never the Pi-algebra sum of two lambdas
  (`(fun y => a y) + fun y => b y`): only the former leaves a literal
  `∫ y, a y + b y` redex. Same root as the 1412 beta-redex entry;
  transcribe from `laplaceAt_testAdd` (law F19).
- (record 1414) H: a MISSING `import` line cascades into dozens of
  "unknown namespace"/"unknown identifier" errors across every open
  and proof body. When the FIRST errors are namespace-shaped, read
  the file's own preamble before touching any proof — the proof bugs
  are invisible until the import lands (brick 3 try1: 67 errors, one
  root).
- (record 1414) I: numeral-negation normal forms — `-1 / 2` in a
  statement parses as `(-1)/2` (HDiv at the root), so a rewrite
  result `-((-1)/2)` does NOT match `neg_neg` (needs `Neg` directly);
  "simp made no progress" lies about WHY. Put `neg_div` BEFORE
  `neg_neg` in the simp list to normalize, or close with an explicit
  `show (-(-1 / 2) : ℂ) = 1 / 2 from by ring`.
- (record 1414) J: for iff rewrites where the lemma instantiates
  different metavariables per side (`mem_set_iff` left with
  `?F := f.reflection`, right with `?F := f`), list the lemma ONCE
  PER SIDE in the rw list — a single pass rewrites only the first
  instantiation's occurrences and leaves a mixed goal.
- (record 1414) K: annihilation lemmas take the FUNCTION first and
  the oddness proof second — `psi_eq_zero_of_odd (oddDiff2 f)
  (oddDiff2_odd f)`; passing `(f, ...)` yields a mismatch whose
  expected type deceptively mentions `f`.
- (record 1414) L: bundled-function fields need their own extensionality
  — `(evenSym2 f).test = (testAdd ...).test` goals with `test :
  SchwartzMap ℝ ℂ` do NOT accept `funext` ("could not unify the
  conclusion of @funext"); the `ext x` tactic reaches
  `SchwartzMap.ext`.
- (record 1416) M: `Finset.not_mem_empty` is NOT a constant in this
  toolchain (v4.30) — an instinctive `absurd hp (Finset.not_mem_empty _)`
  fails with "Unknown constant" on an otherwise fully elaborated file.
  For `hp : p ∈ (∅ : Finset α)` close with `simp at hp`, which reduces
  the membership to `False` and discharges the goal directly. General
  form of the trap: a `Finset`/`Set` emptiness lemma name recalled from
  a newer Mathlib does not exist here, and the failure is a NAME error,
  not a shape error — so the surrounding proof gives no hint. When a
  single "Unknown constant" is the only error in a green-elsewhere file,
  suspect the recalled lemma name first and prefer a `simp` normal form
  over naming a lemma (brick `C1MinimalWeilCriterion` try1: 1 error).
- (record 1574) N: `(-1 : ℂ) • T` with `T` a NON-ENDO `CLM` carrying a
  huge head expression triggers a DETERMINISTIC typeclass timeout
  (`HSMul ℂ (X →L[ℂ] Y) ?m`, 20000 hb) — in statement position AND inside
  `have := rfl` proofs; adding a type ascription does not help (the search
  cost is in the big head term). Fix: carry signs as `Neg` (unique cheap
  instance), sandwich with plain `f.adjoint`/`f` endos, and move any scalar
  sign to the trace via a def-level flip lemma. One `•` hidden inside a
  `have` type produces the misattributed "Unknown constant Subtype.adjoint".
- (record 1574) O: a negation in the RIGHT inner slot (`⟪x, -y⟫`) is
  rewritten by `inner_neg_right` only — `inner_neg_left` silently matches
  nothing and the `simp only` list stalls with the goal unchanged and no
  error about the unused lemma (it comes back later as an unused-argument
  WARNING). Precedent: `C1G8P1EndpointOrientation.lean:67`.
- (record 1574) P: `neg_injective` is `Function.Injective Neg.neg`
  (`-a = -b → a = b`); `apply neg_injective` on a GOAL `-x = -y` matches
  the CONCLUSION `?a = ?b` and leaves the double-negation goal
  `- -x = - -y`. From `h : a = b` to a goal `-a = -b` the right term is
  `exact congrArg Neg.neg h`; `neg_injective` is for CONSUMING hypotheses,
  not goals. The type-mismatch report prints the double negation — read it,
  it names the error exactly.
- (record 1574) Q: in `rw [h] at h'` pick the orientation by what
  SYNTACTICALLY OCCURS in `h'`, not by what `h` "means": `hcyc` contains
  `pairJ.traceProduct`, so `rw [htp] at hcyc` (not `← htp`); and do not
  mix `tsum_neg` into the same rw list that unfolds `ordinaryTraceAlong` —
  after the unfold the negation sits under a binder body that the rw matcher
  has not normalized yet; split into `rw [unfold, unfold]` then
  `simp only [flip set]`.
- (record 1574, toolchain) R: NEVER detach lake builds with `nohup ... &`
  inside a `wsl.exe -- bash -c` one-liner: the launch prints "launched" and
  exits 0, but the session teardown reaps the build and the log file is
  never created (silent lost round; discovered by `ls -t build-logs`).
  Use the harness background runner (it keeps the WSL session alive and
  notifies on exit). Related, re-confirmed twice the same round: `\$(` and
  shell variables inside `wsl.exe -- bash -c` strings are eaten or
  mis-nested — write only literal paths and literal commands.

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
- (29) Pointwise reference lookup (1086 G1): a comparator must evaluate the
  reference AT each sample; nearest-grid lookup on a coarse precomputed grid
  has O(spacing * |phi'/phi|) error (measured 0.45 relative in the chirp
  region, |phi'/phi| ~ 30-40) - symptom: constant-magnitude relative
  residual that does not shrink with candidate improvements.
- (30) Reference self-convergence floor (1086 G1): a float64 quadrature
  reference has its OWN discretization error; a pre-registered tolerance
  tighter than the reference's coarse-vs-fine residual compares the
  candidate against reference noise (1086: gate 1e-6 vs floor 8.4e-5).
  Before firing F-C on a gate failure, measure the reference's
  self-convergence; split the gate into a definitional leg (round-trip
  against the imported original) plus a same-point leg with tolerance
  max(floor, k x self-convergence).  Record the amendment openly.
- (31) FFT autocorrelation normalization (1086): the circular
  autocorrelation is `np.fft.ifft(|fft(x)|^2)` with NO extra factor -
  `np.fft.ifft` already carries 1/L; appending `* L` inflates every lag by
  L (symptom: a window integral ~3e5 where O(1) is expected, and the
  FFT-vs-brute-force tie check at ~L instead of ~1e-16).  Always carry the
  tie check (`abs(R[k]*du - dot(conj(h[:N-k]), h[k:])*du)`) and treat it as
  a hard gate before reading any arch/window number off R.
- (32) Factor-bookkeeping against the Lean source (1086, CORRECTED by 1087):
  closed-form pieces of a Lean quantity must be re-derived FROM THE LEAN
  DEFINITION, not from a prose draft.  The arch tail beyond the square
  support is `F 0 * log tanh(r)` - the FACTOR-X1 form.  The 1020 scan had
  it right all along; the 1086 design draft and this law's first edition
  both asserted a factor 2 ("BOTH numerator terms vanish"), which DOUBLE-
  PAID the 2: `numerator/denominator = -2F0/(e^y - e^-y) = -F0/sinh y`,
  primitive `F0 log tanh(y/2)`. A prose correction without a source-level
  derivation can itself be defective; numerical raw-integrand quadrature is an
  implementation cross-check, not the proof of this identity.
- (33) Cross-check factor implementations by direct RAW-INTEGRAND
  re-integration with TWO gates, not one: (Ga) closed form vs direct must agree to the
  quadrature's own first-cell sliver scale (1087: 5.6e-05 against a grid
  whose body starts at y = step for a direction with O(1e2) integrand
  slope), and (Gb) the rival factor variant must MISS by O(1), rejected
  far outside every noise floor - a single tolerance gate cannot tell
  "closed form correct" from "closed form and direct share the same
  bug". Both gates must be printed in the log and asserted in code
  (`1087_c3_roundtrip_cert.py`).
- (34) A Galerkin variational bound requires a certified inclusion of the
  finite space in the continuum carrier. In record 1087, the smooth-bump
  Legendre profiles use floating-point quadrature/SVD for the moment nullspace,
  while zero-extended sine profiles are not C-infinity at the endpoints.
  Their eigenvalues are matrix observations, not certified lower bounds for the
  `CompactLogTest` supremum. Before invoking the min-max inequality, prove the
  basis belongs to the carrier and certify the constraints and matrix entries.
- (35) An invariance pair must NAME the axis it holds fixed, and the axes are
  not independent: on this rig `dt = 2T/N` and `dxi = 1/(N dt)`, so at fixed
  dt and xi_max the pair (N, T) -> (2N+1, 2T) necessarily scales dxi AND the
  t-extent (1097: dxi 0.05 -> 0.0125, T 10 -> 20).  At deep octaves the dxi
  axis can dominate the gate (13 percent observed on trace-class
  observables), so a "dt-invariance" label on such a pair is a mislabel.
  When the next refinement along the offending axis is out of memory budget
  (32769 x 40 needs 17.2 GiB per complex matrix), do not weaken the gate
  post hoc: fire the pre-registered ABORT, then re-register with the
  certification the budget actually supports (1097b bracket direction:
  coarse member strictly above fine on trace-class observables, with the
  confound named and the non-signed observables excluded explicitly).
- (36) A discharge chain that lands on a previously falsified quantity
  class must re-run that quantity's guard before the chain's endpoint is
  called "narrower" (1096, corrected by 1097b/1098).  Narrowing is a
  statement about IMPLICATIONS, not about evidence: 1096's
  `A-in-HS => SandwichedTermNuclearity` is a valid Lean implication, but
  its primitive is exactly the raw-F1 class 1063 falsified, so scheduling
  the primitive would have resurrected a dead obligation under a new name.
  Before promoting a discharge endpoint to canonical, check its primitive
  against the falsified-class ledger (1063/1067 for this rig) and, if it
  touches one, pre-register a fork like 1097/1097b: the primitive stays
  canonical only if its guard (window growth, no bend, dt-invariance)
  re-certifies at a deeper octave; otherwise re-point to the measured-O(1)
  alternative (1098: absorbed factor + commutator legality).
- (37) A quadratic form built by POLARIZATION (q(i+j) - q(i) - q(j)) from
  a quadrature functional inherits the functional's first-cell sliver as
  an IDENTITY shift on its DIAGONAL only: q carries -step*F(0)/2 (the
  arch body starts at the first lag, missing [0, step] ~= step*F(0)/2),
  and the pairing's F(0) values (2, 1, 1) cancel it off-diagonal but keep
  -step/2 on each orthonormal diagonal.  Eigenvalues at that scale are
  quadrature, not physics (1100: every total top = -(0.94..1.00)*step/2
  across radii AND families - the offset tracks the grid, not the
  window).  Diagnose by checking the measured offset against step/2
  across radii BEFORE reading any sign near zero; cure by adding the
  analytic leading cell to the body (1100b) or integrating the closed
  form.  Also banked: a fresh-uv environment cannot reproduce committed
  probe logs bit-close (era venv deleted; drift 2.4-2.8e-05 at the
  certified fidelity scale) - certify adapted classes against the
  imported rig IN THE SAME ENVIRONMENT (bit-identical; 1100 G-arch-2
  gap 0.0) and RECORD the log-vs-today drift instead of chasing the
  deleted environment.
- (38) Gauss-Legendre interval map: reference nodes [-1, 1] go to
  [c, d] via x = mid + half*nodes with half = (d - c)/2 - and every
  constant consumed ELSEWHERE in the construction (1100b: the F(0)
  anchor feeding the removable-singularity limit and the tail) must be
  computed over the SAME interval.  A shrunken F(0) un-removes the
  removable singularity (delta/sinh(y) spike at y = 0) and inflates an
  O(1) body by ~delta*log-scale, and the error does NOT converge under
  y-refinement - refinement gates stay blind; only an independent
  cross-construction gate (1100b G-cell-3) caught it, at gap 2.4e-01
  against a 5e-6 gate.  Smoke-test the construction against the rig on
  ONE function BEFORE the gated run (1100b smoke: gap 1.0e-10 after
  the fix vs 2.4e-01 before).
- (39) Lint appeasement is a runtime bug factory: never silence
  "possibly unbound" by adding the assignment BEFORE the branch that
  binds it - that converts a static warning into a guaranteed
  UnboundLocalError at exactly the guarded site (1100b run5, after
  four green gate groups).  Fix the control flow (move the default
  initialization INSIDE the branch that owns it); the linter was right
  the first time.
- (40) Interval arithmetic cannot cancel divergent terms: when a
  certified bound evaluates ~1e43 orders over its true value, check
  the FORM for un-cancelled pole terms before touching any width
  model - no width model fixes a non-cancellable form (1101: Leibniz
  sup|h''''| with y^-5 terms gave rem 3.66e3 against a true ~1e3;
  the fix was the algebraic rewrite Q = N - T3*sinh, pole-free by
  construction, rem -> 3.9e-17).  Same law in the other direction:
  when a REGISTERED bound exceeds the budget by orders because the
  intermediate MAGNITUDES are huge (float squared chains at ~1e33
  giving ulp widths 1e25+), REFORMULATE the quantity into an
  equivalent form with small intermediates (integration by parts:
  int f'^2 = -F''(0) as an arb y=0 leg), never inflate the budget.
- (41) Tolerance-band direction: a cross-check gate that compares a
  RAZOR certified interval to a float64 recomputation must expand the
  CERTIFIED side to cover the f64 value (f64 in [L - a, U + a]),
  never demand the interval WRAP the whole 2a-wide band - with a
  budgeted width << a the wrapped form is unsatisfiable by
  construction and will ABORT every correct implementation (1101
  run3: pv width 1.7e-11 vs an implied >= 1e-3 requirement).  When
  registering a gate, check the containment direction against the
  budget section - the two are written together and must not
  contradict.
- (42) The verdict selector must implement the registered mapping
  LITERALLY (every/some quantifiers and the margin clause): printing
  a partial list as if it were the branch verdict converted 1101 run
  4's 3-of-6 strictly-negative table into a false "H2c" while the
  other three rows straddled zero.  A branch NAME is a CLAIM, not a
  summary - a wrong selector line pollutes the official run log even
  when the JSON table is correct; re-derive the branch from section 4
  text word-for-word, and prefer the more conservative reading when
  the code and the doc disagree (a verdict may only get harder to
  claim).
- (43) Prime-tail measure (record 1102): when certifying a tail of a sum over
  PRIMES whose weight depends on log p, integrate against the PNT measure --
  primes in [y,y+dy] number ~ e^y/y (the Jacobian e^y of the linear density
  d pi/dx = 1/ln x), NOT one-per-unit-y.  A per-prime weight y*G(y) therefore
  tails as int_{Lt}^{inf} [y G(y)] * (e^y/y) dy, not the unit-spaced
  int y G(y) dy; dropping the e^y under-counts by ~ e^{Lt}.  Verified at Lt=12:
  direct prime sum = 7.38e-12 <= PNT bound = 7.41e-12, while the unit-spacing
  formula gave 9.3e-16 (~8000x low) and turned a correct reconciliation into
  an unexplained FAIL whose residual was byte-identical across dps=30..90.
- (44) mpmath quad(error=True) under-certifies semi-infinite/oscillatory
  integrals: at dps=50 it self-reported ~1e-52 while two INDEPENDENT closed
  forms of the same W_R disagreed by ~5e-13, and that residual was
  byte-identical across dps=30..90 (so not arithmetic precision).  Budget on
  the CROSS-METHOD disagreement (law (19) three-point anchor), never on the
  quad self-report; give any analytic tail bound an explicit safety factor
  (x3 in 1102) covering quad tolerance plus higher-order / m>=2 terms.
- (45) Non-decay-in-u test functions break the TWO-SIDED Weil identity
  (record 1103): if the spatial transform G(u)=inv[f(s)f(1-s)] fails to decay in
  |u| -- g_3 at d^2=4 turns negative (~-1.2 by u=5..6) -- then MULTIPLE right-hand
  terms are individually non-convergent, both the u-form W_R integral AND the
  infinite prime sum over log p.  Symptom set: (a) two closed forms of W_R disagree
  (digamma +0.43 vs capped-u<=8 form -2.69, xcheck ~3.1); (b) the truncated prime
  side ps3(U) is not stable in U (U=6 -> -430, U=7 -> -1000, U=8 -> -263; diagnostic
  U=10 -> +5.8e4); and (c) per-cutoff certified reconciliation then FLIPS verdict
  PASS(1.43)/FAIL(0.72)/PASS(3.05).  Within the certified toolkit such an object can
  ONLY be reconciled with a FINITE one-sided gate (record-1089's arch_g.convSq +
  finitePrimeSum_g.convSq <= 0, visible primes q < exp(2*(n+2))), and must NOT be
  claimed as a two-sided Weil equality.  Scope limit (2026-09-03 narrowing, prompt-006
  round-1 F5 audit): the measured symptom set does NOT rule out a two-sided identity
  under conditional convergence or another regularization - "the terms diverge
  individually => no faithful two-sided object exists" is a non sequitur; it only
  establishes that no two-sided reconciliation is currently CERTIFIABLE here.  A
  regularization-invariance theorem would be needed to close that gap either way.
  The method still validates on compact / decaying controls (records 1102 PART1/2).
- (46) Gate-scope inheritance (record 1104): every pre-registered gate must inherit
  the regime scope of the phenomenon it tests.  1104's G1 explicitly exempted radii
  a < 1.5 from the zero-pinning claim ("data, not failure"), but G4 (counterfactual
  sign > +0.3) was registered "at every radius" on the same ray and was falsified
  exactly in the exempted regime (a = 0.5: n_visible = 1, counter = -0.54;
  a = 0.75: +0.001 - no mirror can exist with 1-3 prime powers).  The literal
  verdict stays FAIL (law 42: no post-hoc rescoping); the cure is an explicit
  written addendum restricting the claim to the regime (G4 restricted to a >= 1.5
  PASSES with min +1.10).  Also banked: an anchor tolerance cannot be tighter than
  the reference's PRINT precision (1104 demanded 1e-9 against six-decimal audit-log
  anchors; worst miss 4.8e-7 was pure reference truncation, the in-environment
  rerun itself being deterministic) - register the abort threshold at the reference
  floor, not at aspiration (law 30 family).
- (47) A gate FAIL must survive re-derivation of its own arithmetic before it is
  attributed to physics (record 1105): the first run printed FAIL on two legs that
  the printed lines ALREADY satisfied - the in-house gate layer had applied the
  registered kappa band to a cell the pre-registration exempted (law 46 at the code
  level) and had a sign slip in the pin-depth comparison (claim top(M) =
  kappa*lam_min(Z) vs code topM - (-kappa*lam_min_Z)).  Law 42 applies to gate CODE,
  not only to verdict prose: re-derive the selector word-for-word from the
  pre-registration section before trusting a FAIL, fix the selector, re-run, and log
  BOTH runs (the false FAIL stays in the addendum).  The underlying physics
  (Weil-identity matrix residuals, 15/15 P-2 values) reproduced digit-close on the
  first run - the FAIL was purely implementational.
- (48) An ABORT-AGREE-class diagnostic abort is resolved by PER-BLOCK high-precision
  cross-machine comparison, not by re-deriving algebra in the dark (record 1108): when
  the anchor-agreement diagnostic failed at +0.381, one scratch run recomputed each
  matrix block (G, R, A, P) at 30-digit mpmath against the anchor machine entry by
  entry - G/A/R agreed to 8 digits, only P00 differed (0.204) - localizing a
  weighting-convention bug in minutes where whole-derivation re-reads had failed.
- (49) Prime-side weights in this repo's window-class functional are von Mangoldt:
  w(q) = Lambda(q)/sqrt(q) = log p / sqrt(q) for q = p^k (the f0.lam_sieve convention
  since 1005).  Using log q / sqrt(q) instead silently over-weights prime powers by k
  (1108 run-2: P00 off by 0.204); the probe's von_mangoldt_log and the pre-reg section 1
  now register the convention explicitly.
- (50) A PSD gate must test pivot POSITIVITY via the lower endpoint (mid - width/2 >=
  floor), never absmin >= floor: absmin is SIGN-BLIND and waves through any negative
  pivot away from zero (1109 run-1: the inherited 1108 predicate PASSED the interval
  Cholesky at a U below the top, where the exact T has a provably negative direction
  c*'Tc* = U - top).  Corollary design rule: an oracle gate that has never observed a
  REJECTION is an untested gate - pair every certification predicate with a registered
  must-fail canary side (G-bracket style); that one line cost nothing and localized
  the hole in one run.  The same audit cleared 1101: its certified signs use
  endpoint predicates (total_L > 0 / total_U < 0) and its absmin uses are
  sign-irrelevant |P'|-away-from-zero Kantorovich requirements - semantically correct.
- (51) python-flint arb (0.9.0): operations propagate ball radii but MIDPOINTS store
  at float64 REGARDLESS of flint.ctx.prec, and any float() conversion (IV.span,
  midf/rad reads) quantizes sub-float radii away.  An arb chain therefore certifies
  entries to ~1e-15 relative, NOT to the ctx precision - a Schur/Cholesky walk on it
  cannot see directions below ~1e-15/entry-conditioning.  Resolution rule: before
  claiming certification at gap g, verify g >= ~1e3 x (machine resolution x
  conditioning, e.g. 1/lambda_min(G)); if not, move the predicate to an explicit
  float-domain oracle with a REGISTERED eps budget or change library.  Caught by the
  1109 G-bracket canary at run-2 (real -1e-9 direction, arb lows all >= +4.8e-5);
  1108's conclusion survived via its 1e-6 margin, but the interval gate never saw the
  dangerous direction.  Audited and cleared: 1101's certificates are analytic-tail
  dominated (2e-7 widths >> 1e-15 midpoint effect).
- (52) A flint arb ball (mid +/- rad) is NOT interval arithmetic: it tracks per-op
  rounding, not dependency.  Any recursion that REUSES an uncertain quantity
  nonlinearly - a Schur/Cholesky walk dividing by earlier pivots - loses enclosure
  validity when pivots are ill-conditioned (1109 run-3: true final Schur pivot
  4.22e-08 vs arb-walk low 9.768e-05; the 4e-14 radii never covered it).  PSD gates
  on such pencils must run in a stated domain (float + registered eps budget, as
  1109's fix batch 2) or with true interval arithmetic (mpmath mpi) PLUS a
  dependency control (whitening congruence or dangerous-subspace subdivision) - a
  ball-walk Cholesky must never be labeled an interval certificate.  Also: a PSD
  oracle must test POSITIVITY (eigmin >= +floor); a negative tolerance (-tol "PSD")
  lets a bisection certify BELOW the true optimum and is unsound (caught at 1109
  fix-2 design review before any run).
- (53) LAPACK symmetric eigensolvers SILENTLY read one triangle: numpy eigh and
  scipy eigvalsh(a, b) with a non-symmetric a return garbage at the ||a|| scale,
  no warning (1110 run-1: eigvalsh(Mz, Bz) = +3.58e+01 where the quadratic form
  is -2.6e-10).  M = A + P here has skew part ~||M|| BY DESIGN - prime shifts are
  one-directional and B(-xi)^T = B(xi) exactly, so P^T != P.  Standing rule: any
  matrix that reaches a symmetric driver must be explicitly (X + X^T)/2'd at the
  call site (the primary pencil_top already symmetrized after congruence; only
  the xcheck's raw pass was bitten).
- (54) A must-fail canary needs MEASURED leverage, not an assumed one (extends
  law 50): 1110 run-2's random-entry sign-flip ABORTed because the (4,8)
  vanishing rows have wildly unequal leverage on the top - dropping s=1/2 moves
  it +7.9e-01, dropping s=0 or s=1 moves ~1e-10, SAME SIZE AS THE PIN.  The
  pipeline was healthy; the premise was fantasy.  Before registering a
  sensitivity floor, run the leverage measurement (drop/perturb experiment) in
  the same session and choose the corruption along a measured load-bearing
  direction; when a canary fires, root-cause whether the pipeline is blind or
  the perturbation is inert before touching anything, and fix the corruption
  rather than the floor (law 39 optics).
- (55) A gate PASS must survive re-derivation of its own arithmetic (law-47
  MIRROR, 1112): the registered (4,8) STRADDLE prediction falsified UPWARD, and
  executing the pre-registered "book the real coupling" path from the bundle
  caught a real hole - the FLOAT center of an affine whitened box is displaced
  from the exact rational product (realized |Gmid_sym - I| = 6.2e-11), while
  the attached scalar floor (1e-13) was both under-provisioned AND structurally
  wrong (an entrywise product-rounding pattern is not bounded by a scalar).
  Sub-lessons: bound congruence-rounding channels as entrywise comparison sums
  4*eps*(|X| @ |mid| @ |Y|T) and never estimate them inertly - the channel
  flows through the SAME whitening amplification as the data (realized cost
  2.44e-02, my inert estimate was 5e-8, six orders wrong); and a PASS margin is
  NOT evidence of soundness (run 1's worst-row budget was half unbooked
  channel - the 1108-erratum geometry).
- (56) Post-compression phantom files: before editing ANY file, verify it
  exists (ls / git ls-files). The session resumed from compaction replayed a
  "file" (Dev/RayleighPosSemidef.lean) with fake diagnostics and even a fake
  commit id that exist in NO object database and NO directory - a distorted
  echo of the real E0SlemmaBridge.lean. Ground truth is `git log --oneline` +
  `git status` + direct ls; when editor/LSP diagnostics contradict the
  filesystem, the filesystem wins, and no edit proceeds on a file not seen by
  `ls` in the current window.
- (57) A background-task "completed exit 0" notification across the wsl.exe
  boundary is NOT evidence the work happened: in the 1113 launch the wrapper
  reported completed while the python process was still at 109% CPU and the
  log was 0 bytes (stdout block-buffering + the detached wrapper's own
  exit). Acceptance protocol: before rerunning anything, `ps aux | grep
  <script>` to check the process is gone, THEN read the log CONTENT (a
  real completion ends in the script's own sentinel, e.g. "DONE").
  Corollary: python probes whose verdict matters should flush per section
  or accept that mid-run state is invisible.
- (58) Python chained comparisons are (a > b and b > c): writing a
  positivity guard as "pins[hi] > 0.0 > pins[lo]" silently tests the OPPOSITE
  (hi positive AND lo negative) and reported every healthy ratio as
  "undefined". Any guard added in a pre-run edit must be smoke-evaluated as
  a one-liner against a known-positive input before the edit is committed;
  display bugs found post-run are fixed in the same commit as the addendum
  with the reconstruction from printed primary quantities stated (the 1113
  ratios were recoverable exactly from the logged pins).
- (59) Model-scan input ranges must be CLOSED, not assumed: 1114b run 1
  counted ball nodes over a precomputed zero list whose top (gamma_90) was
  below the largest ball ceiling (T+R = 284), silently undercounting
  N_ball at k=15/20 while every print looked sane. Rerun with KMAX=170 and
  a per-row assert (gammas[KMAX] > T+R) that fails loudly. Same law's
  second hit the same hour: `mpmath.dps = 30` on the top-level module
  raises a set-time AttributeError (correct target: mpmath.mp.dps) - a
  Pyright flag I had conditioned myself to distrust was REAL here, so the
  law-56 discipline cuts both ways: verify diagnostics against the
  interpreter, fix what is true.
- (60) Registered extrapolation bands pay rent when they fire: the 1113
  pin(5) band [1.7e-12, 7e-12] was violated DOWNWARD (realized 4.43e-13;
  per-unit decay 1.12e-2 / 1.61e-2 / 1.70e-3 across 2->3/3->4/4->5 =
  SUPER-geometric past a=4). The two-point geometric fit was a 2-point
  fit, and the STRADDLE fired via the U >= 0 selector (DELTA wider than
  realized pin), not the registered noise-floor route. Never re-use a
  two-point margin extrapolation to pick a third-point DELTA without a
  refit band; and when a falsifier fires, the booked direction of surprise
  is itself the finding (here: the horizon is CLOSER than modeled).
- (61) Raw float-domain centers are NOT exactly transpose-symmetric and this
  is DATA, not corruption to repair: the 1115 probe found max |M_ij - M_ji|
  = 7.0e-01 / 2.5e+00 / 7.1e+00 for the 1112/1113 Gram centers ((2,8)/(3,8)/
  (4,8)) - independent roundings of mirrored entries.  Quadratic forms kill
  the antisymmetric part EXACTLY (generic theorem `qf_transpose`), so every
  gate value and certificate ever emitted is unaffected; but any exact
  algebraic identity trusted on ONE center (e.g. K^T (U G - M) K = L D L^T
  with symmetric RHS) is LITERALLY FALSE on the raw data and must run
  through an explicit symmetrization + the qflip instead.  When an assert
  fires on your input data, measure it, bound its consequence, and change
  the certificate shape - never silently symmetrize.
- (62) Kernel-check heartbeats are per-declaration quantities on bignum
  data: 300-400-digit exact rationals pushed the whnf check of the numeral
  equality proof of ONE theorem (hD: `D = U • G - M`) past the default
  200000 while all thirteen sibling identities pass at default.  Diagnose by
  bisection on the declaration list (the hd2 probe style), raise
  `maxHeartbeats` ONLY on the measured declaration via the scoped
  `set_option ... in` form, and record in-file why (the lint demands the
  comment; treat it as documentation duty, not appeasement).
- (63) Let the failure modes choose the tactic shape, per theorem, by log
  evidence (1115 fix batches 6-9): with 64 fin_cases foci whose simp-closure
  is MIXED (some entries close under simp alone, some carry the bignum
  arithmetic), the three shapes fail in three DISTINCT LOUD ways -
  `(simp; norm_num)` errors "No goals to be solved" iff some focus closed;
  pure simp reports "unsolved goals" iff some focus survives; the
  never-executed lint fires iff ALL foci closed.  One build per candidate
  shape reads like an experiment and PINNED the per-theorem map
  (hKV pure; hD/hDK/hKDK sequential; hDc/hWR/hcl/hLd/hLdLt `<;>`) with zero
  guesswork - uniformity is an aesthetic, evidence is a proof.
- (64) The ext4 mirror (/home/peter/rh) has NO .git of its own - it is a
  file-synced working tree (per-file cp from /mnt/c inside wsl.exe).  Any
  `git -C /home/peter/rh ...` silently walks UP to an unrelated outer repo
  (observed 2026-09-03: it fetched from a dask/distributed clone at
  /home/peter and printed its log lines as if they were ours).  Before ANY
  git command on a mirror path, verify `rev-parse --show-toplevel` equals
  the intended repo; sync the mirror ONLY with cp/rsync from /mnt/c.
- (65) A numerical twin of a PINNED interpolatory construction must be built
  at the TRUE collision-resolved node set, not at a perturbed surrogate
  family (1116): at the healthy pinning, `1-rho-bar` and `1-rho` collide
  with `rho`/`rho-bar` at delta=0 and Lean's case-ORDER resolves them
  (first match wins) - 13 constraints, not 17.  The positive-delta
  surrogate drags the conflicting (+1,-1) pair, so its coefficients
  diverge (x~2-4 per halving) and its plateau (GATE/f0 = +0.44908) does
  NOT converge to the true value (+0.45698): surrogate non-convergence is
  a structural finding, always test the coefficient scaling trend toward
  delta -> 0 before trusting a branch surrogate's limit.  Related: a
  convention self-test must count EVERY fold in its expectation
  (corr = chi counts as base^{*1}; build_g(a=[1], nexp) yields chi^{*(nexp+1)}).
- (66) Cross-domain fidelity gates (float x-side vs arbitrary-precision
  s-side identities) must be sized at the domain-noise floor, never at the
  scientific target precision (1116 batches 4-5): the x-side noise of a
  cancellation-dominated assembly is eps * sum|a_m| * kernel-mass *
  e^{Re z * support}; assert the identity only at nodes above a
  measured floor (max(|lhs|,|rhs|) >= 1e-8 * max|F|, at least 3 nodes,
  include OFF-AXIS nodes so the conjugate/shift conventions are tested),
  and keep off-axis residuals as reported ratios.  Structural breakage
  (aliasing, index, conjugation) appears at O(1) - a threshold between
  the noise floor and O(1) (here 1e-4 vs observed 7.5e-6) is a faithful
  gate, not a weakening.  The root-cause of the original 4.2e+67 ratio was
  Gauss-Legendre under-resolving e^{i xi x} at xi ~ pi/DX (~1.5 points per
  wavelength); the lesson generalizes: never evaluate a transform at
  frequencies the quadrature cannot resolve - build the function on its
  own resolved grid and convolve there.
- (67, record 1329 probe round, 2026-09-11) WSL wall-kill + dense-linalg
  probe laws, banked from two silent-death invocations:
  - THIS wsl.exe/timeout path surfaced a SIGTERM wall-kill to the outer
    shell as EXIT 0 (controlled: `timeout 2 python3 -c "sleep(10)"` ->
    exit 0).  So for numerical runs, "exit 0" proves NOTHING - the
    completion criterion must be an explicit final `DONE` sentinel line
    in the log that the verdict parser requires (A2x rule).  Same lesson
    class as the build-side log-not-exit-code law, now on the probe side.
  - Dense complex QR ~4087^2 and full-matrix SVD of 2048x4096 cost
    MINUTES (~93 s/cell) under this WSL numpy build.  Budget dense
    linear algebra per cell BEFORE registering a wall cap; and an
    ONB-rebasing invariance audit does NOT need a dense random unitary:
    64 random Givens pair-mixings of the basis rows is orthonormality
    preserving, O(64M), and tests exactly the same invariant (validated:
    E-delta 3.6e-12, ONB-deviation 6.6e-15).
  - REGISTERED-SHAPE guard promoted to a gate: every model cell must
    assert realized constraint-count K == preregistered K before any
    number is adjudicated (inv1 defect: a model id parsed by slice
    `name[2:]` kept its dash -> `int("-3")` -> empty mode list -> the
    whole M3 family silently ran K=1 while printing plausible numbers).
    Parse hyphenated ids with `split("-")[1]`, never with a fixed slice.
- (68, records 1332-1334 probe round, 2026-09-11) SVD-statistic and
  gate-witness laws from the Toeplitz corridor probe:
  - `numpy.linalg.svd` returns DESCENDING singular values; the near-kernel
    floor block is at the TAIL. A cliff witness `s[r]/s[r-1]` silently
    measures the TOP of the spectrum (gap ~1.0) — the correct statistic is
    `s[D-r-1]/s[D-r]`. Any threshold-defined rank must index from the tail.
  - `sigma_min` is USELESS as a discriminator once the operator is exactly
    rank-deficient in float (floor ~1e-17): pre-register the CLIFF COUNT
    (or another tail statistic) as the primary readout, never the floor
    value — the 1332 monotonicity clause failed at the floor and returned
    INCONCLUSIVE on data that was actually decisive (ratio to winding).
  - Control witnesses must match the OPERATOR, not a sibling convention:
    `phi=1` on the grid-center basis gives the unitary DIAGONAL
    `diag((-1)^m)`, so `max|T-I|` witnesses fail at value 2 while
    `sigma_min` passes at 1.0; the safe identity witness is
    (off-diagonal max, min |diag|) pairs. Smoke-test the GATES themselves
    at reduced size before the official run — 1334's G0/G1/G2 defects were
    all caught by a 10-second N=1024 pass, each fixed as a pre-run
    amendment (A1/A2), never by post-hoc re-thresholding.
  - Kernel-diagonal density conventions (raw sum |w_j(xi)|^2 vs
    h-folded) must be written once and every gate constant derived from
    it; G1's "K_full = d/(2L)" vs "d*h/(2L)" mismatch was exactly this.
  - Re-confirmed: NEVER put shell `$vars` inside nested `wsl.exe -- bash
    -c "..."` python strings — MSYS expands them to empty before WSL sees
    them (a loop silently no-ops with zero output). Pass literal values.
- (69, record 1338 probe round, 2026-09-11) Subspace-extraction and
  interpolation-path laws, banked from three smoke-caught defects (all
  pre-run amendments inv4/inv5/inv7; zero official digits were produced
  under any of them):
  - `np.linalg.svd(A, full_matrices=False)` on a WIDE matrix (rows <
    cols) returns only `min(shape)` right-singular vectors, so the
    null-space slice `Vh.conj().T[:, rk:]` is TRUNCATED or EMPTY — it
    silently produced a 0-column "null basis" (phantom statistic 0.000)
    and mixed row-space vectors into the next cell. Null-space
    extraction ALWAYS requires `full_matrices=True` (or QR/rank-revealing
    alternatives) when rank can be < rows.
  - Every derived subspace gets a TRACE WITNESS as a machinery gate:
    `sum_k K'(x_k) h == dim` to 1e-8. This (G7) is what caught the SVD
    slice defect — the statistic itself looked merely "interesting", the
    trace caught it. Wrong-dimension subspaces produce plausible numbers.
  - Band-limited interpolation kernel parity: `sin(pi M u / P) /
    (M sin(pi u / P))` is the EXACT symmetric-band reproducing kernel
    only for ODD M (the band sum is 2K+1, which equals M-1 for even M),
    and NEVER interpolate a space containing the grid's Nyquist mode
    (m = N/2 on an N-point grid aliases; that was the first G4 failure
    at 1e-4..1e-2). Use an ODD oversampled grid (M = 2N+1). Cross-check
    an interpolation path against exactly-known targets: constant
    reproduction (row sums == 1) caught the parity bug immediately.
  - Constants entering a probe from memory or a sibling record are
    DATA: derive at runtime or verify against a witness (inv3: three
    hand-typed zeta ordinates were fabricated; G5's residual witness
    `|zeta(1/2+i gamma)| <= 1e-3` for every used gamma caught them
    before any cell ran). KSHAPE recurrence — data-fidelity gates are
    MANDATORY for any probe consuming external tables.
  - Smoke gate policy: resolution-limited gates (cliff sharpness,
    tolerance-pair rank) may be downgraded to WARN ONLY under an
    explicit smoke-mode env flag registered as a pre-run amendment;
    machinery gates (identity, exactness, cross-checks, data fidelity)
    abort at every resolution. A smoke run never emits verdicts — it
    prints a distinct sentinel (SMOKE-MACHINERY-GREEN).
- (70, record 1341 B0 audit, 2026-09-11) Obligation-dissolution audits —
    run BEFORE any design cycle on a gated existence obligation:
  - PINNING audit: when a gate is phrased as existence of a structure with
    PINNED data fields (family := fixed construction), immediately test
    the GENERALized structure. If the generalization trivializes
    (e.g. `exists positive trace-class family with Tr -> c` <=> `c >= 0`
    via a CONSTANT rank-one family), every no-go theorem proved for the
    pinned family is a family-specific artifact and constrains NOTHING —
    the whole "moving-family engineering" surface evaporates. Dissolve
    first, engineer never.
  - TARGET-EQUIVALENCE audit: before funding a campaign toward a gate G
    with goal T, check both committed directions: G -> T (usually the
    architecture) AND ¬T -> ¬G (often committed too, e.g. counterexample
    machinery used inside the capstone proof body). When both hold, G is
    G-as-T in disguise; the lane's value is construction discipline, not
    weakening — say so in the record and let the owner decide.
  - Both audits are paper-only, bounded (hours), and each has already
    saved a multi-record campaign (1225 F3 quantifier repair; 1341
    family-shopping closure). Make them the mandatory first paragraph of
    any "attack surface X" recon.
- (71, record 1342 probe round, 2026-09-11) Composite-quadrature and
    fidelity-ladder laws from the simpson rig defect:
  - UNIT-TEST every hand-rolled composite quadrature rule against a
    trusted reference (scipy) AND against an exact-for-the-rule
    polynomial, BEFORE it carries a control anchor. The 1116-era
    `simpson_uniform` was the 2/3 three-point rule on DISJOINT triples
    (no overlap) while labeled composite Simpson - the defect survived
    two probe generations because nobody asked it to integrate `x^4`.
    Fix = `simpson_fixed` + a G1a provenance gate (recompute a committed
    anchor, relative band) + a G1b independent-path cross-check (scipy).
    When a rig fix moves a control anchor: record old and new values and
    check the SIGN class first (1342: corrected anchor +0.1302074,
    committed in prereg inv9; same sign as the broken-rule reading, so
    every 1225-era sign adjudication survives; no Lean object consumed
    the rule - grep before panicking).
  - Truncation points inside a cross-domain fidelity gate (explicit
    formula geometric vs spectral side) must be CALIBRATED BY
    MEASUREMENT, never hand-picked: Gevrey-class tails decay at a rate
    that depends on the dimensionality of the test vector (1342: the
    5-dim smoke witness was tail-clean at T=800, the 21-dim official
    witness still had residual 4e-05 there - ~160x slower). The
    self-calibrating form: pick the first (T,2T) in a geometric ladder
    whose MEASURED drift is below the gate's own drift budget, cap it,
    and fail honestly above the cap. This removes human T-selection
    freedom, which matters most when the gate adjudicates the sign of
    the object that controls it.
  - Law-42 rig-defect pattern (third instance, after inv5/inv9): an
    official attempt killed by its own fidelity gate is ABORTED, fully
    disclosed with digits BEFORE the amendment commit, and the
    amendment may authorize exactly one further attempt anchored by a
    control that passes the same gate on the same code. After the
    re-run the probe is spent regardless of outcome.
- (72, record 1347 A1 round, 2026-09-12) Refactor the hot term, gate the
  refactor on a FULL-OBJECT dual-path equivalence check, keep the
  reproduce-tier and stability-tier digits on the VERBATIM spent-probe
  path (importlib-import the old module; never copy its bodies). When a
  naive repeat of a previous official run would bust the pre-reg budget
  (A1: m=96 verbatim ~5.1 h vs 4 h budget), the admissible fix is an
  algebraically identical refactor of the dominant cost term ONLY,
  admitted by a same-Gram equivalence gate (G9: band 1e-12; actual
  result bit-exact 0.0) - the refactor buys the budget (A1 ran at 1/12
  estimate), the gate converts "trust the new code" into a measured
  fact, and an implementation bug the gate would have caught was
  instead caught earlier by re-deriving against the verbatim source
  during the pre-launch review (F5 working as designed). Companion rail:
  when a scalar readout lands NEAR its decision boundary, pre-declare
  the drift statistic as an honesty rail (A1: alpha_3pt = 0.988 against
  boundary 1, pairwise slopes RISING 0.984 -> 0.993): the branch verdict
  is then explicitly TIER-LIMITED and the resolving measurement is a
  named new prereg, never a silent extrapolation of the current one.
- (73, record 1353, 2026-09-12) Before any claim of the form "a LOCAL
  COUNTING condition implies a sampling-energy bound" (frame bound,
  O(1)-robustness, threshold f*), run the Shannon-number placement
  audit: for band-limited samplers of type sigma, N_eff(interval of
  width L) = sigma*L/pi is the per-node-information ceiling (top
  Slepian/prolate eigenvalue; smoke-measured lam1/pred = 1.000), and
  the adversary controls NODE PLACEMENT, not just the count. A set of
  nodes clustered sub-Nyquist-tight (L << pi/sigma) carries ~N_eff
  information regardless of its cardinality, so count-based contests
  are NOT O(1)-robust; the count-only statement must be upgraded to
  count + spread before it is written into any target spec or
  conditional theorem. Using the prolate operator as an information
  ESTIMATE does not reopen the frozen prolate producer route (1055).
- (74, record 1353 renumber, 2026-09-12) Pick a record number by
  checking BOTH `git log` HEAD and the TAIL of MEMORY.MD for reserved
  future numbers ("next = ... -> verdict record 1349" style plans)
  BEFORE creating the file; a same-session parallel wave can move HEAD
  while you work (here: 1349 was reserved for the batch-1548 A1b
  verdict by the 1350-1352 wave mid-session; the audit renumbered to
  1353 in-place). Pointer edits and renames in the same wave must be
  sed'd carefully - a link-pattern sed corrupted two markdown links on
  first pass; re-read pointers after bulk edits.

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
- Consumer-3 landmine (record 1081): the root-support wall lives ONLY on the
  prefix side.  The TAIL side is damper-free closable for every test
  (`exists_fourthOrderTail_halfDensityShift_convolutionSquare`: the Hermitian
  product squares quadratic vertical decay into fourth order).  Do not
  re-attack the tail with n-fold damping - the n-fold orbit is what DESTROYS
  root support (`Ioo((n+1)*baseLower + lower, ...)`), and the epsilon-vs-radius
  circle (`epsilon = f(C(corr(R(n0(epsilon)))))`) is broken in-library only by
  that damping.  Also: `mul_le_mul_of_nonneg_left` cannot see through
  left-association - state `81 * (A * B)`, not `81 * A * B`.
- Integral-rewrite diseases (record 1082, six build iterations 38 -> 0
  errors).  All are kabstract pattern-shape traps around `integral_add`:
  (1) `MeasureTheory.integral_add` is BETA-form (`∫ a, f a + g a`),
  `integral_add'` is Pi-add form (`∫ a, (f + g) a`) - pick the variant whose
  LHS matches the GOAL's syntactic integrand shape, not the defeq one.
  (2) Merging twice: the first merge produces beta-form `∫ f a + ∫ g a`; to
  merge THAT again the second hint's function must be a LAMBDA (`have h :
  Integrable (fun y => B y + C y) := B.add C` - the ascription is defeq and
  fixes the syntactic shape).  A Pi-add-typed hint produces an unmatched
  `(f + g) a` pattern; a Pi-add of a Pi-add never matches.
  (3) `rw [h]` rewrites ALL occurrences of the instantiation: from
  `a = -a`, `rw [two_mul, h]` lands on `-a + -a` where `add_neg_cancel`
  cannot fire.  Route: `have h3 : -a + a = 0 := neg_add_cancel _;
  rw [← h] at h3` then `two_mul` + `mul_eq_zero` + `resolve_left`.
  (4) `integral_congr_ae`'s conclusion has integrals on BOTH sides - `apply`
  fails when the goal RHS is a bare `0`; state the zero-integral equality
  explicitly, then `rw` + `simp`.
  (5) On unrestricted integrals the `Filter.Eventually.of_forall` /
  `filter_upwards` hypothesis has ONE binder (no set membership); over
  `Set.Ioi` restricts the authority is ALSO one binder in this Mathlib -
  `fun y _ => ...` fails with introN.  Verify against the expected-type in
  the error, not against intuition.
  (6) `rw`'s closing `rfl` is NOT full-defeq: `0 + 0 = 0` (Complex instance
  head) and `f.involution.test t = star (f.test (-t))` (structure-projection
  unfold) both survive it - finish with explicit `simp` / `ring` /
  `simp only [involution_apply]`.
  (7) `exponentialWeight f s` returns a CompactLogTest, NOT a function:
  integrability of the weighted test is `SchwartzMap.integrable (...).test`.
  (8) `ConvolutionExistsAt f g x L μ` IS the `Integrable (fun t => L (f t)
  (g (x - t))) μ` statement - `HasCompactSupport.convolutionExists_left_of_
  continuous_right ... y` supplies pointwise convolution integrability
  directly (dodges nonexistent `SchwartzMap.comp`); continuity input is
  `(g.test.smooth ⊤).continuous` (`SchwartzMap.contDiff` is not a field).
  (9) `eq_neg_self_iff` does not exist in this Mathlib; use the
  `neg_add_cancel` + `mul_eq_zero` route above.
- Owner-construction lessons (record 1083, three probe iterations 27 -> 13
  -> 1 -> 0):
  (1) `(by tac).symm` / `(by tac).field` dot-chains STRIP the tactic block of
  its expected type ("invalid 'by' tactic, expected type has not been
  provided") - bind the fact in an ASCRIBED `have h' : T := by tac` first,
  then apply the projection to `h'`.
  (2) A constant-times-function compactness fact must be reached with an
  ASCRIBED pointwise type: `have h : HasCompactSupport (fun x => (c:ℂ) * f x)
  := f.compactSupport.mul_left` works (isDefEq does the Pi.mul elimination),
  but stating `(fun _ => c) * f.test` inline elaborates `HMul` at the wrong
  head, and `simpa` can never see through an UNAPPLIED `Pi.mul` sitting
  inside `HasCompactSupport` (Pi.mul_apply needs an application).
  (3) Reflection WITHOUT conjugation gives `lap f.reflection s = lap f (-s)`
  by pure substitution; the chain is `rw [hsplit, integral_neg_eq_self]` -
  do NOT put `integral_neg` in the list (the hsplit integrand has no leading
  negation; the pattern can never match).
  (4) Before union/rsplit reasoning on supports, `Function.mem_support` must
  be in the simp set (`x ∈ support f` is `f x ≠ 0`; `rcases` on `≠` fails -
  it is not inductive).  Then split the goal disjunction with `by_cases` on
  ONE summand, not `rcases` on the hypothesis.
  (5) `rw [← sub_neg_eq_add]` for `a + b = c → a - -b = c`; the forward
  direction only matches goals that still contain `- -`.
- Anchor-scaling lessons (record 1084, three probe iterations 5 -> 1 -> 0):
  (1) the `ext` TACTIC has no registered extensionality lemma for `ℂ` in
  this Mathlib ("No applicable extensionality theorem found") - use explicit
  `apply Complex.ext` with the re/im subgoals, where bare `simp` closes
  star-of-numeral goals (the `ℂ` star instance is conj-defeq);
  (2) `Complex.star_def` rewrites `star z` into the `(starRingEnd ℂ) z`
  spelling, which then does NOT match `Complex.conj_ofReal`'s `conj ↑r`
  pattern - bridge with `starRingEnd_apply` or avoid the chain entirely;
  (3) exact archimedean scaling (`F = 2h` pointwise => `arch F.convSq =
  4 * arch h.convSq`) needs NO integrability input: `integral_congr_ae` +
  `integral_const_mul` are unconditional, because `archimedeanTerm` is a
  constant-times-`test 0` plus an integral read off the test pointwise.
- v4.30 `inner` refactor laws (records 1498/1499, 2026-09-16):
  (1) `inner` takes 𝕜 as the FIRST EXPLICIT argument in v4.30; bare
  `inner x y` elaborates with the vector in the 𝕜 slot ("expected Type ?u").
  Write `inner ℂ x y` or the scoped `⟪x, y⟫_ℂ`. In `have` ascriptions, type
  the whole `inner ℂ _ _` expression explicitly or the `InnerProductSpace ?m
  ↥Carrier` typeclass search sticks on a metavariable.
  (2) `norm_sq_eq_re_inner` as a bare rewrite rule leaves the 𝕜
  metavariable stuck — pin the scale: `norm_sq_eq_re_inner (𝕜 := ℂ)`.
  (3) `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` is MUL-form
  (`‖x+y‖ * ‖x+y‖ = ...`), not POW-form; bridge into `‖·‖²` goals with
  `rw [pow_two, hpyth, pow_two, pow_two]`.
  (4) `abs_of_pos h : |a| = a` is an EQUALITY; for `0 < |a|` use
  `abs_pos.mpr (ne_of_gt h)`.
  (5) Parse law: a docstring `/-- -/` cannot be followed by `set_option ...
  in` — put the set_option BEFORE the docstring, with a `-- reason:` comment
  (the linter requires one).
- Subtype-coercion isDefEq pathology (records 1498/1499): declaring a lemma
  argument as a SUBTYPE (`sourceSoninCarrier lambda`) when instantiation
  points pass ambient-typed terms (`finiteSCarrier`) forces `↑v` coercions
  that blow 1M-heartbeat isDefEq timeouts. Declare ambient-typed arguments
  and give instantiation lemmas ambient-typed conclusion types; pin the
  `congrArg` motive type exactly (e.g. `fun T : sourceSoninCarrier lambda
  →L[ℂ] finiteSCarrier => T v`), and rewrite INSIDE a norm with
  `rw [congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
    T (basis i)) hsplit]`.
- List/summability hazards (record 1499): `List.mem_map_elim` does not exist
  in v4.30 — use `List.mem_map.mp` and destructure `⟨a, ha, hout⟩` with
  `hout : f a = b`, orienting rewrites as `rw [← hout, hMN]`. A conjunction
  of Summables must parenthesize EACH `Summable` — a bare lambda body
  swallows the `∧` (AddCommMonoid Prop synthesis failures). `rw` rewrites
  ALL occurrences of the first matched instance; use `conv_lhs => rw [...]`
  when the RHS shares the pattern.
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
- A published compact-window Weil lower bound is not automatically a
  `CC20EndpointTraceCertificate`.  Before importing it, prove the exact
  log-coordinate carrier map, Hermitian-square convention, sign/normalization
  readback to `cc20WInfinityLog`, and an auditable certificate for its claimed
  interval computation.  Once scalar `0 <= cc20WInfinityLog g.convolutionSquare`
  is available on a triple-vanishing test, prefer the existing
  `zeroTraceCertificate_of_nonnegative_wInfinity` constructor; do not recreate
  a nonzero trace package without need (record 1088).

### 7h. Compute-device selection + probe process laws (record 1220, 2026-09-07)

Device selection rule (RTX 5090 present on the box):
- Pre-registered probes that mandate EXACT rational/interval arithmetic
  (Fraction endpooints, generation-time asserts) run on CPU only, via the
  multiprocessing band-slice pattern of record 1220: parent primes caches,
  forks a Pool, workers take interleaved slices of an exactly-associative
  accumulation, canonical-order sum.  Do NOT port exact-Fraction interval
  pipelines to GPU: variable-width bignum + gcd has no CUDA semantics, the
  adaptive stack is branch-divergent, and the prereg pins the exact
  arithmetic (1220 case: port would be a week-scale project to speed up a
  one-shot half-day probe whose permanent artifact is a CPU-side Lean
  build anyway).
- Exploratory float work (fine-grid sweeps, spectral scans, Monte Carlo
  parameter scans) SHOULD target the GPU first: 1212-style ladders,
  1087-style spectral verdicts, F-pack sweeps are textbook SIMD.
- The Amdahl critical path of an adaptive refinement (one heaviest region,
  serial split decisions) is never GPU-shaped; size the pool to the band
  count, not the core count.

Process laws from the 1220 run ledger:
- Health checks of WSL processes must use `ps aux | grep -a <pattern> |
  grep -v grep` plus log content, BOTH.  `ps -C <name>` produced a false
  negative under wsl.exe (7h, 2026-09-07); single-command verdicts stay
  forbidden (same family as the fake-`0` law, 1217).
- A Pyright red (error-class) flag on generated/probe code must be either
  fixed or explicitly re-adjudicated in writing before launch; dismissing
  it by analogy to earlier false positives caused the run4
  imap_unordered crash (it does NOT unpack task tuples; starmap does).
  Static red = treat as real until proven otherwise (law 56 cuts both
  ways).
- In a preregistered probe, if a loop variable is syntactically dead in
  the body (1220: `sign` in the entry-assembly leaf loop), record it as a
  registered review note at prereg time and let the registered falsifier
  adjudicate; never silently "fix" semantics mid-campaign.

### 7i. CPython 4300-digit int->str landmine (record 1220 salvage, 2026-09-08)

- Python 3.11+ caps int<->str at 4300 digits by default
  (CVE-2020-10735 mitigation; check `sys.get_int_max_str_digits()`).
  Exact-Fraction probes whose checkpoints/printouts serialize endpoints
  via `str(Fraction)` will crash AFTER all compute, BEFORE the
  checkpoint write, whenever denominators exceed the cap (1220 entry
  endpoints: 1e4-1e6 digit denominators).
- Rule: any exact-arithmetic probe driver must call
  `sys.set_int_max_str_digits(0)` at driver entry (serialization-only,
  no bound affected) BEFORE launch, not after the first crash.
- LIVE FIRE 2026-09-13 (1396 certificate): the guard fired exactly as
  predicted — padded-Fraction ceilings have ~1e4+-digit ints, crash at the
  FIRST print. Two sound remedies (both now in the template): (a)
  `set_int_max_str_digits(0)` when the full endpoint digits must be
  recorded; (b) render intermediates as `float(Fraction)` (correctly
  rounded, display-only) and print exactly only the FINAL small dyadic
  pair — 1396 chose (b): the certificate's auditable artifacts are the
  20-digit dyadics, and the giant intermediates have no reading value.
- Diagnosis signature of the pre-crash grind: 100% utime, zero syscalls,
  zero minflt over a 30 s window (`/proc/<pid>/stat` delta) = giant-int
  normalization in progress, not a hang; strace/py-spy may be absent in
  the WSL distro - /proc counters are the fallback.
- Live-process salvage that worked: Ubuntu python3.12 exports
  `PyRun_SimpleString`/`PyGILState_Ensure` in its dynamic symbol table
  even when statically linked, so with passwordless sudo + gdb:
  `sudo gdb -p <pid> -batch -ex 'call (int)PyGILState_Ensure()'
  -ex 'call (int)PyRun_SimpleString("import sys;
  sys.set_int_max_str_digits(0)")' -ex detach` repairs a running
  process; verify by injecting an `os.write(1, ...)` marker into the
  run log and reading it back (`[RUN4_LIM=0]` / `[RUN3_LIM=0]`).
  yama ptrace_scope=1 blocks non-root attach; sudo gdb works.
- Sequence discipline: inject FIRST when the crash point is imminent
  (minutes away), commit the script fix second (law 42 only orders
  reruns), then mirror-sync.

### 7j. Instrument-scout process laws (record 1225 invocations 4a/4b, 2026-09-09)

- NEVER restart a probe onto the same log path: the runner's `>` redirect
  truncated 4a's live log when the companion relaunched 4b onto
  `1225_official4.log`, destroying rung 3-4 evidence (rungs 1-2 survived
  only because the probe also writes a results JSON). Rule: every re-run
  gets a NEW log path (suffix by invocation), codified as A9 turn rule 2.
- Cross-lane protocol (A9, 1225 sec. 6.3): when two sessions work on one
  working copy, each names its lane's files, no kill/restart of the other
  lane's live invocation, no edits into the other lane mid-run, and the
  prereg record's amendment section is the hand-over point (whoever ends a
  turn appends the state there).
- Pre-register the FAILURE MODE as a finding: the A8/A9 amendments reserved
  "a later rung breaching the capture gate = REAL capture finding, not
  protocol death" BEFORE the run; when rung 4 asserted
  `tail_gap 5.40e-08 > 1e-8` (predicted ~2.5e-8), the run converted to
  ABORTED-UNINFORMATIVE with a permanent yield instead of a mystery crash.
  An instrument campaign that dies on a pre-registered knife edge still
  pays out.
- Calibrate gates on REALIZED geometry, not nominal rank: the rank-2560
  windows realize ~7250x7250 dense at n=8 (support-limited), and the FP
  truncation error scales as ||K|| * tail_gap * bulk_cont, so a naive
  "gap < 1e-10" gate was unachievable while 1e-8 is meaningful (A8
  history: 1e-10 -> 1e-8 committed before the rerun). Also verify the
  Slepian knee position at each rung: fixed rank cannot certify exact
  capture beyond the family's knee (the 1225 capture law).
- Determinism is a measurement, cheap to buy: running the byte-identical
  script twice (same md5) and comparing rung values to the digit converts
  "was it noise?" into a proved fact; keep scripts hash-pinned in the
  ledger so reproducibility claims cite the md5.
- Heavy-eig silence is health: during a rung the log goes silent for many
  minutes; verify liveness by `ps` CPU TIME (~7 worker threads burning),
  NOT log mtime; a dead run is proven by Traceback + runner `official
  exit N` lines, not by pgrep counts (self-match artifact: the monitoring
  bash wrapper matches its own pattern).
- Official runs go through the resource-lock wrapper
  (`scripts/run_resource_aware_task.sh --class heavy --log <fresh path> --
  <cmd>`), with PYTHONUNBUFFERED in the runner and a scheduled checkpoint
  (cron) that reads the LOG for a VERDICT-MARKER - acceptance is always by
  log content, never by exit code (law of the 1217/1220 ledger).

### 7k. Capability-frontier epistemology (1342/1343 close-out discussion, 2026-09-12)

Born from an in-session error, kept as the correction template. While
answering "胜算多少 / 有没有路子 / 你根本做不出来吗" I asserted, from
training memory: "no demonstrated success inventing new-structure
mathematics" and a 1-3% campaign probability. Both rested on a 2024-era
capability prior that was ALREADY FALSE by weeks:

```text
  falsifier (same week, verified live 2026-09-12):
  - OpenAI NS blowup, 10k agents x 88 h, Lean-checked (Quanta 2026-09-08):
    quantamagazine.org/ai-has-solved-one-of-maths-1-million-millennium-prize-problems-20260908
  - Astra "ten advances" (2026-08): non-sofic group CONSTRUCTION, Connes
    rigidity DISPROOF, unit-distance disproof, ... all Lean certificates,
    ~$2k tokens. openai.com/index/ten-advances-in-mathematics
  - arXiv 2605.22763: 9/353 open Erdos problems autonomously resolved.
```

Laws:
- (F1) Any claim of the form "X is impossible for AI systems / has zero
  precedent" is a FACTUAL claim about the live frontier and requires a
  same-day dated web search + cited URLs BEFORE being written into a
  record, report, or decision table. Training cutoff is a FLOOR on the
  capability curve, never the curve itself. (The NS result landed 3 days
  before I opined "categorical no".)
- (F2) Keep solvability estimates MODE-CONTINGENT, never absolute.
  Demonstrated winning modes (as of 2026-09): (A) deep proof search
  inside EXISTING attack vocabulary with machine-checkable candidates
  (NS blowup, permanent bounds); (B) counterexample/construction search
  exploiting verification asymmetry (unit-distance, non-sofic,
  AlphaEvolve 48-mult). ZERO precedent for (C) inventing a new
  DEFINITIONAL vocabulary (Weil-1952-type objects). Re-estimate the
  A/B/C boundary every time a frontier event moves it; the numbers in
  this repo's odds tables are dated and expire silently - stamp them.
  SAME-DAY AMENDMENT (F5 in action): "ZERO precedent for C" was already
  too strong - the 2026-08-10 Anthropic note (Claude, Lean-checked,
  Conrey/Goldston-verified, critical-line proportion 41.6% -> 67.2%,
  mechanism = definiteness fusion) is a demonstrated NOVEL-THEOREM result
  INSIDE the RH family. Corrected statement: novelty inside RH-territory =
  precedented; FULL CLOSURE of RH = still no precedent, for anyone. "No
  precedent" is a measurement of past capability, never a boundary of
  current capability - the owner's "no" here was right twice.
- (F3) RH-specific anatomy that survives the F1 correction: RH-false is
  mode-B-shaped but prior ~0 (10^13 zeros + RMT statistics + this
  repo's own B0a NO-FIRE stack up); RH-true requires mode-C UNLESS an
  existing-vocabulary attack vector is found - and the barrier theorems
  (Epstein zeta: functional equation alone insufficient; Bombieri-Hejhal
  grand symmetry class: standard L-function axioms insufficient) say the
  needed input is "a definable property specific to zeta that no fake
  shares", i.e. vocabulary-level, not search-level. State barriers like
  theorems, never as vibes, and check them when a mode record moves.
- (F4) STRATEGIC corollary of d767a1d (weilCriterion_iff_sourceRH, green
  log 1546_1343_brick_green.log): the FIRST moment in 170 years where a
  machine-verified Lean statement equivalent to RH coincides with
  engines that CONSUME exactly such statements as attack targets. The
  correct reframe of "开打" is therefore not a think-harder campaign
  (mode C, no precedent) but a KNOCKER-BUILDING campaign (B0d'):
  (i) a certificate-witness language for the gate (positive-definite
  kernel / SOS / positive-measure representations of qw, each
  candidate Lean-checkable), so any A/B-mode engine can fire at our
  door; (ii) a function-field blueprint diff-card inventory (every
  ingredient of Weil's manifest positivity on curves vs its missing
  Z-analogue, itemized to theorem granularity); (iii) both artifacts
  carry standalone value at RH-odds-zero - bet the interface, never
  the breakthrough.
- (F5) When a premise of your own published analysis is falsified
  mid-conversation, RETRACT EXPLICITLY and re-derive in the same breath
  (this section exists because of it); do not quietly edit the old
  conclusion. Wrong-then-corrected in public beats confidently stale.
- (F6) Route taxonomy before funding (owner directive 2026-09-12:
  "大概率能成的方案,而不是抽彩票"). Every proposed route must declare its
  class: LOTTERY (closure upside, unquantified odds), MEASURED-DISTANCE
  (every rung high-P(deliverable); the single closure-uncertain step
  carries an explicitly computed shortfall number BEFORE funding),
  EVIDENCE-TURN (increments guaranteed, closure provably unreachable -
  ceiling citation required), AUDIT (adjudicates external claims;
  decisive either way). Hard rules: never fund a LOTTERY rung before its
  thermometer number exists; "无先例" is not a rejection reason (F2), but
  "unquantified odds" is; a campaign is composed so that ~all budget buys
  certain deliverables and the closure bet is placed LAST and only if the
  thermometer reads HOT. First application: record 1345 s5 (N1 contest
  route activation gates).
- (F7) Thermometer bands must reference a NON-VOID baseline (2026-09-12,
  1346 stage-0 lesson): "within 2x of existing technology" is meaningless
  when existing technology provides NOTHING in the required direction - a
  ratio to zero is not a small ratio. Where the baseline is void, replace
  ratio bands with reachability classes declared before the run: HOT =
  constant-tuning inside published explicit technology; WARM = one
  genuine new lemma with a nameable proof route; COLD-STRUCTURAL = no
  named technology reaches the required regime. Corollary: a stage-0
  recon may be run IMMEDIATELY on any missing-bone claim - it is paper,
  costs nothing, and its adversary-consistency audit (is the attack
  configuration blocked by ANY located unconditional theorem?) is the
  cheapest possible ranging shot. First application: 1346 (NLLE
  COLD-STRUCTURAL for assault, WARM for harvest).
- (F8) RECON THE REGISTER BEFORE LOCKING A PREREG (2026-09-13, 1388 -> 1389
  -> 1390). A prereg locks a MODEL, and a model names register objects: a
  node family, a value pattern, a support window, a positivity condition. If
  any named object is the wrong one, the prereg is void - and law 42 forbids
  editing it, so the correction costs a whole record. The failure mode is
  invisible at write time because the wrong object is a REAL object of the
  right type from a neighbouring route. 1388 locked the orbit package's 7-node
  `sourceFunctionalEquationOrbit` plus a radius grid of which 19/25 cells
  violated the route it had itself committed to. Sequencing rule: source
  readback of the exact definitions the prereg will name is part of WRITING
  the prereg, not a follow-up. It is free, it is finite, and every minute of
  it is cheaper than a superseded record. Second-order rule: a prereg's grid
  must be checked against the model's own hard constraints before commit -
  write the constraint as a gate (G0 ADMISSIBILITY in 1390) so the check is
  mechanical rather than a hope. RECURRENCE 2026-09-14 (1415), at
  CAMPAIGN-PLANNING scale: the F2 plan (1412) priced brick 4
  ("dictionary psi=Q in Lean: LONG") from the 1411 fork framing
  without re-reading the register; the dictionary was already landed
  and audited (`gate2ExplicitFormula_centerTwo`, summability +
  identity legs proved for every test, consumed by the wall's own
  bridge). Prereg-stage recon (grep for the PROPOSITION by name and
  search theorem statements, not just file lists) took minutes and
  voided days of duplication. Rule extended: BEFORE writing any
  campaign-brick plan item, grep the register for a theorem that
  already states it - a campaign brick is a prereg of a different
  shape, and F8 binds it identically.
- (F9) GREP FOR AN IFF BEFORE COSTING A ROUTE (2026-09-13, 1389 s3). When the
  target is a conjunction of obligations, search for a theorem that
  characterizes the whole package as ONE condition before estimating the work.
  `healthyDetectorData_iff_selectedDetectorArchimedeanGate` collapsed a
  four-field `HealthyYoshidaDetectorData` package to a single scalar sign on a
  ROOT-pinned test, and choosing that register removed an `(n+1)`-fold iterate,
  two decay constants, a height-tail budget and a growing support window from
  the critical path. Cost estimates made before that search were wrong by an
  order of magnitude in BOTH directions (the iterate was feared as new
  analysis and was free; the sign was assumed free and is the open science).
  Corollary: when two registers reach the same target, table them
  side-by-side on obligation count, not on familiarity - the familiar one is
  usually the expensive one.
- (F10) A MODEL PREREG MUST LOCK ITS PRECISION CLASS (2026-09-13, 1390 ->
  1392/1393 -> 1394). Formulas are exact; implementations are not, and a
  prereg that states only formulas silently delegates the precision choice to
  whoever writes the script. 1390 did: the v2 run died on G3 at R = 0.02
  (cond(G) ~ 1e13, spurious imaginary ~294 on a model-real quantity) - the
  MODEL passed every check, float64 did not. A precision defect looks
  identical to a content defect from the sentinel, and law 42 then forces a
  new record to confess it. Rule: the prereg names the arithmetic (bit
  precision or exact rationals) and the tolerance classes (residual,
  imaginary leakage, band-edge tie window) NUMERICALLY, in the gate section.
- (F11) WRITE AT LEAST ONE GATE THAT A PLAUSIBLE BUG MUST FAIL (2026-09-13,
  1393 G3 proving itself). Every validity gate is paid for at the moment a
  silent implementation bug would otherwise masquerade as a verdict. The
  1393 invocation-1 mpmath zero-fill made ALL 96,000 cells "PASS" - the
  perfect fake result, the one no sanity read of a summary line would
  question. It died because G3 demanded K_loc > 0 unconditionally: a fact
  the MODEL guarantees (positive definite Gram at distinct nodes, 1384) but
  no bug can fake cheaply. Gates with that asymmetry - true of the model by
  theorem, false under a plausible transcription bug - are the cheapest
  insurance in the campaign; every prereg should own at least one.
- (F12) AUDIT EVERY GATE FOR SATISFIABILITY BEFORE THE PREREG SHIPS
  (2026-09-14, 1398 v1->v2->v3; three waves, three recurrences). A gate is
  defective not only when a plausible bug passes it (F11) but when NO
  correct instrument can pass it: 1390 v2's G1 demanded a band-DROP the
  reference itself failed; 1398 v1's GV tie scale integrated a divergent
  1/y kernel (S = infinity, every cell forced TIE); 1398 v2 locked GF/GR
  convergence recomputes at 1e-8 relative while the model's OWN numbers -
  tier-1 Gram alpha 5.9e-12, coefficient dynamic range 3.6e9 vs g ~ 1e4,
  and a measured first-order C/npw discretization law - put the floor at
  ~1e-6. For every tolerance class the prereg must carry a pre-run
  estimate: condition number x machine epsilon for arithmetic floors, and
  a derivative/step bound for discretization; a class at or below its own
  prediction is an unsatisfiable gate and costs a revision record (law 42)
  plus a VOID log each time it is discovered post-run.
- (F13) DOCUMENTED PITFALLS ARE ONLY PROTECTION IF CONSULTED (2026-09-14,
  1398 inv1). The mpmath `mp.matrix(m, n, list)` zero-fill was ALREADY
  written in this file's numeric pitfalls section with the correct fix
  syntax - and 1398's instrument rewrite re-inflicted it anyway, because
  no step in the rig-writing protocol said "re-grep the pitfalls section
  for the libraries you are about to touch". New rig checklist item zero,
  before the first import: grep AGENTS.md for each dependency
  (mpmath/numpy/wsl/lean) and copy the documented-correct idiom, not the
  remembered one. A law not consulted has zero enforcement.
- (F14) VISIBILITY IS NOT SENSITIVITY (2026-09-14, 1400/1401). A parameter
  can be representable in the instrument's arithmetic and still be a dead
  lever: if it enters the measured quantity only through a physical
  correction of size delta/R, then representable delta ~ 1e-14 at R ~ 0.1
  moves A by ~1e-10 relative, and every tolerance class that certifies the
  MAIN value also certifies the perturbation away. Before declaring a
  lever "tested", compute the perturbation's SIZE, not just its
  resolvability: 1399 found eps dead via float64 invisibility (delta
  7e-33); 1401 found it dead anyway via the locked budget formula
  delta = eps*alpha/(4(1+eps)TB^2), which caps delta/R ~ 1e-12 on ALL
  (J1)-feasible geometries of the 4-node family - the rung-2 construction
  STRUCTURALLY forbids an aggressive taper, so no more grid searching of
  that family for rung 3 is justified (82/82 negatives are one mechanism).
  RECURRENCE 4 (1403 inv1, 2026-09-14): the gate that failed was the NEW
  one - GI-beta's 1e-30 mp class is unsatisfiable against the model's own
  taper band (sharp-pairing reassembly of a TAPERED solve deviates by
  delta*||c||*R <= 5.6e-15 from the v1 audit's OWN columns), because the
  audit checked the inherited gates and never the invented one. RECURRENCE
  5 (1403 inv2, same day): the CHECKER must resolve what it checks - the
  imported laplace_g panel-density proxy 3|im target|+2 sees 0 at REAL
  nodes and gave a 16-node panel to a 730-rad oscillation at im=1054:
  gdmax 7.7e-2 ALIASING read as 5 BADCELLs while the model was fine
  (3e-16 at the +-rho detection nodes; error scaled with |s_j| = the
  diagnostic fingerprint; the 2.2e-7 "passes" at im=100 were the same
  defect under class). Gate satisfiability audits must cover the
  INTEGRATOR resolution of each gate, not only tolerance floors.
- (F15) PRICE A CAMPAIGN FROM THE EXIT'S HYPOTHESES, NOT THE FILE COUNT
  (2026-09-14, 1402). Before costing a multi-day formal campaign, read
  the endgame theorem's hypothesis list to the root. Doing that for
  route beta took one session and found: (i) the "pending" 1083/1084/1085
  chain was already CLOSED (pair existence, anchor collapse to one test,
  bridge to the 1080 gate - all standard-axiom audited; "formal prereq"
  in 1399/1401 had mislabeled landed machinery as pending work); (ii)
  the live mainline consumes NO beta sign (the detector producer
  exists_healthyDetectorData_of_sourceNontrivialZero_right is
  UNCONDITIONAL); (iii) the exit's second pillar (endpoint certificates)
  carries the same content as the B0b gate, machine-checked
  weilCriterion_iff_sourceRH - so beta re-partitions the wall and one
  piece IS the wall. When hypotheses are the price, a campaign that
  cannot shorten the wall does not exist.
- (F16) A PREREG BRANCH THAT CANNOT FIRE IS A DESIGN DEFECT
  (2026-09-14, 1405/1406). F12 audits whether a gate can PASS; its
  twin asks whether each VERDICT BRANCH can be reached at all. 1405's
  EXCLUDES/COVERS dichotomy was decided in advance by the evaluator's
  own formula (psi reads only the even-real part of F, so the
  imaginary-odd cross is annihilated identically - |P_x| >= 1e-3 was
  unreachable). Before locking a dichotomy, derive which branch the
  instrument's formula already decides; a probe whose outcome is
  implied by type is decoration. (Also: 1404's "queue empty by
  construction" meant the rig/brick queue - F15 re-audit of the 004
  exit hypotheses later found live paper surface; "empty" claims name
  their universe.)
- (F17) TRANSCRIBE, NEVER RECONSTRUCT (2026-09-14, 1405 inv1-4 / 1406
  forensics). A helper functional inside a probe is a line-by-line
  copy of the committed instrument with only call sites parameterized.
  Reconstructing from the derivation paper silently drops terms the
  instrument committed later: the probe's A_of dropped the analytic
  tail reF0*log(tanh(Rg)) and the owner.Cg kink grid, and the tail is
  literally a printed line of this register's own 1404 decomposition
  (closed-loop evidence). Mandatory companion: a parent-agreement gate
  (G0-class, tie class above evaluator noise) for every
  reconstructed quantity - here it correctly FAILED four times before
  the transcription fix, and every derived sector number from those
  runs (A_r=-1.75 vs true -0.68) was silently wrong.

- (F18) CITE THE FORM PREMISE VERBATIM, ESPECIALLY YOUR OWN. The 1406
  collision triangle was sharp only because T1's support field was
  paraphrased from memory; the register's own
  `exists_healthyDetectorData_of_sourceNontrivialZero_right` carries NO
  support bound (radius `2^(n0+1)+2+dist(2,rho)`, height-dominated), and
  the root-support-exit header says the orbit theorem does not supply
  the window. Before pricing any dichotomy/collision, quote the exact
  statement text (file:line) of every formal vertex in the record; a
  paraphrased vertex can manufacture a crisis the kernel never proved.
  F17 applied to logic, not just code. (Born 1407/1408.)

- (F19) TRANSCRIBE PROOF SKELETONS THE SAME WAY YOU TRANSCRIBE
  INSTRUMENTS. Before hand-writing any tactic that duplicates a
  machine-checked shape elsewhere in the repo (negation substitution
  under a bilateral Laplace integral, etc.), locate the proven template
  and copy its skeleton verbatim. The 1412 leaf reconstructed
  `laplaceAt_involution`'s argument-flip shape from memory twice:
  `rw [integral_neg_eq_self]` silently refuses to match a
  beta-redex `(fun y => ...) (-x)`, and the fix is the template's
  `let`-bound helper so the substitution is a first-order match.
  F17's duty covers Lean tactics, not only numerical code.
  (Born 1412, try1+try2 of the same brick.)

- (F20) GREP FOR OVER-SPECIALIZED DEFINITIONS, NOT ONLY FOR EXISTING
  THEOREMS. F8 says: before planning a brick, grep whether a theorem
  already states it. F20 is the second half of the same duty: grep
  whether a DEFINITION already carries a free parameter that the repo
  has never instantiated. A `def` with an unused parameter is standing
  inventory — the generalization you are about to "invent" may already
  be typed, and the only missing work is two instantiations. Record
  1416 found `C1.healthyCriterionState (F : Finset
  CriticalVanishingPoint)` and its `F`-generic `iff`
  (`C1HealthyTestSpace.lean:100,108`) fully landed, while all 696 uses
  of `cc20TripleFiniteVanishingSet` across 45 files instantiate `F` at
  exactly one value. The minimal-normal-form brick was therefore
  reassembly (13 declarations, green on try2), not new mathematics.
  Corollary for pricing: when a candidate bone's target quantifies over
  a parameter that some landed `def` already abstracts, price it as
  reassembly and expect a sub-day brick — and check FIRST, because the
  same grep often reveals that the apparent degree of freedom is
  vacuous (here: every sub-triple `F` gives an `SourceRH`-equivalent
  gate, so "choosing a better vanishing set" can never weaken the
  wall). (Born 1416.)

- (F21) PRICE A CANDIDATE BY HYPOTHESIS *LEVEL*, NOT JUST BY COST. F15
  prices from the exit's hypotheses. When the exit is a sign, ask one
  further question before any spend: is the target obligation
  PHASE-level or DENSITY-level, and are the candidate hypotheses on the
  same side of that line? A density-level input cannot determine the
  sign of an exponentially long oscillating sum, no matter how sharp the
  estimates. Record 1417 found exactly this: the prime measure
  `nu([0,u]) ~ 2 e^{u/2}` makes the full gate phase-level, while every
  strictly-lower datum the project owns (the Gamma-side symbol `Phi`,
  exponential type from support, `{log p}` independence plus PNT) is
  density-level. Consequence: it killed a whole strategy (more bones in
  the same category) rather than one bone, and it explains the recurring
  1342-1353 finding that "every candidate positivity theorem encountered
  was the same Weil-Bombieri wall in different clothes" - the candidates
  were all density-level. Corollary: when a filter kills a strategy
  rather than a candidate, the correct move is to change category, and
  the replacement category must be chosen for having a PROVED theorem on
  the target side, not for being fashionable.
  (Born 1417, and it is what selected map 011.)

- (F22) A RECORDED SIGN-CONVENTION FRACTURE IS A BLOCKING PREREQUISITE,
  NOT A CAVEAT. Do not write "subject to the sign audit" and continue
  deriving. 1417 derived a fourth normal form and a phase/density filter
  while carrying the 1214/1216 fracture as a footnote, then discovered
  from committed source (`C1MinimalWeilCriterion.lean:247-248` and the
  theorem name `qw_nonneg_of_archimedeanTerm_nonpos_...`) that the
  obligation direction is `archimedeanTerm <= 0` - so an intermediate
  claim ("A is unbounded below, contradicting the gate") had its sign
  inverted and became the program's most promising deliverable (the
  window theorem W1). Two rules follow. (1) Resolve the direction from
  committed source BEFORE deriving anything that consumes it; the
  theorem NAME is evidence, not decoration. (2) Stale prose records can
  carry the opposite convention: 1389's "`0 < archimedeanTerm`" must not
  be quoted as the obligation. When a measurement's sign is the
  evidence (1398's `A = -88.1952`), check it against the committed
  direction first - a sign fracture makes every historical number
  ambiguous in exactly one direction, which is the worst case.
  (Born 1417, self-reported.)

- (F23) A CATEGORY CHANGE MUST BE AUDITED FOR REDUCTION, NOT JUST FOR A
  PROVED THEOREM ON THE TARGET SIDE. Record 1418 showed that the Arakelov
  bridge program's identity `widehat{deg}(phi(g)^2) = -c * qw g` would carry
  the full RH difficulty inside the existence of `phi`; it therefore
  re-encodes the wall rather than lowering it. In addition, pinned Mathlib
  v4.30 has no arithmetic intersection vocabulary needed for the proposed
  A4 Lean leg. Keep the experiment as a paper-only, typed audit, but do not
  describe it as a reachable RH route. The independent W0-W1 window theorem
  is a local consequence target and must also be labeled as non-RH.
  (Born 1418, self-reported.)

- (F24) A BRIDGE CLAIM IS ADJUDICATED POSITION BY POSITION ON COMMITTED
  DEFINITIONS, NEVER BY SHARED NAMES. Before asserting "record X supplies
  hypothesis Y", write both sides as full CLM composition chains from the
  committed `def`s and compare slot by slot: left factor, kernel/operator,
  input map, inserted ambient factors, cutoff placement. The word
  "leakage" named at least four distinct operators in this repo
  (source-Sonin leakage `(I-P) C J`, coframe leakage
  `finiteEulerMetricCoframe - J`, band projection `E - P`, boundary
  outputs), and record 1497's source-Sonin leakage was name-adjacent to
  the G8 diagonal obligations while differing in three slots (left
  projection, input map, ambient factor) — map 042's audit found all
  three by slot comparison, and the same pass converted both obligations
  into source-carrier normal forms and surfaced one free corollary
  (survivor OUT half already dominated). Payoff rule: a slot-by-slot
  audit that ends in "does not supply" should also re-derive what the
  mismatched slots REDUCE TO — the reduction is usually the next brick.
  (Born 2026-09-16, map 042.)
- (F25) AN ALMOST-ORTHOGONALITY (OR ANY "COLLECTIVE CANCELLATION") HOPE
  MUST BE STATED AT THE LEVEL OF THE NORM THE GATE ASKS FOR. A
  Hilbert-Schmidt square-sum gate (`Summable i, ||T e_i||^2 = Tr(T†T)`)
  consumes NUCLEAR cross-term decay `||Q_M† Q_N||_tr <= a(M-N)`, never the
  OPERATOR-norm cross bounds `||Q_M† Q_N||_op <= a(M-N)` that
  Cotlar-Stein/Cotlar-Knapp supply - an op-norm lemma cannot bound a trace
  without rank control. Check the level BEFORE the constants, and check the
  decomposition too: frequency/spectral-annuli pieces have EXACTLY vanishing
  cross terms (AO degenerates to Pythagoras - summability becomes the same
  per-piece ledger), and support-annuli cross blocks ARE the same
  off-diagonal integral the single-column screening already priced. Record
  1576 retired AO as a (star) feeder this way; the exponent ledger (F21)
  catches costs, only the level check catches wrong-kind hopes.
  (Born 2026-09-17, docs/proofs/1576.)

- (F26) AN OWNER DECISION-CARD OPTION IS A SPEND CLAIM, SO THE F8 PRE-SPEND
  SWEEP APPLIES TO IT BEFORE IT REACHES THE OWNER. The F8 sweep (grep committed
  material before funding any new card) was applied to fresh mathematical ideas
  since 1417, but record 1576 handed the owner four options and TWO of them were
  already settled: option (i) "B3 paper-verify then brick" asked for a lemma
  whose conclusion had been proven unconditionally four records earlier, at
  `C1G8R3CompositeBoundaryEnergy.lean:1147-1200` (zero `sorry`, support premise
  discharged internally), and no consumer anywhere awaited the object; option
  (ii)'s exit hypothesis could not close its own obligation because the leg's
  other premise lived inside the stop the same record had just filed. Second
  occurrence of the 1415 "brick 4 is a phantom" mode. Cost of not sweeping a
  card: one full wave of the owner's attention. Procedure: for each option, ask
  (a) is the conclusion already committed? (b) does its exit hypothesis close
  anything, given this wave's own negatives? Then price. (Born 2026-09-17,
  docs/proofs/1577.)

- (F27) COMMITTED SOURCE IS THE FIRST INSTRUMENT; A RIG IS NOT A DEFAULT.
  Before opening any numerical surface, ask whether a committed `def`/`theorem`
  already decides the question by being READ. Owner standing instruction
  2026-09-17: "attack directly where the definitions already answer." Record
  1578 is the case study: the pinned constant `C' = log pi` is a five-step hand
  derivation from `SelectedWeilFormula.lean:96-109` +
  `C1SameOwnerWeil.lean:61-64` + the digamma partial-fraction series, needing no
  quadrature at all; meanwhile a Galerkin pass over `PW_R` was in flight toward
  a "counterexample to (OB)" that the committed hypothesis list of
  `C1MinimalWeilCriterion.lean:263-271` had already ruled out. A rig remains
  legitimate for ONE purpose: producing a certified falsifier where the class is
  right and the question is genuinely open - and then it must carry its own
  basis-validation sentinel (`Psi ≡ 1 => M = I`) before any eigenvalue is
  quotable. Where a rig does run, its numbers are MODEL evidence (law 65) and
  its algebra self-checks belong in a record appendix, not in the verdict.
  (Born 2026-09-17, docs/proofs/1578 + owner correction.)

- (F28) EXTREMIZE ONLY OVER THE OBLIGATION'S OWN CLASS. Before maximizing or
  minimizing any candidate restatement of an obligation, enumerate the FULL
  membership hypothesis list from the committed theorem that owns it, and check
  each hypothesis survives into the trial space. 1417 §3b's operator box kept
  `support ⊆ [-log2/2, log2/2]` and silently dropped
  `CC20VanishesOn C1.healthyCC20TestSpace {half}`, which unfolds to
  `laplaceAt g (1/2) = 0`, i.e. `g-hat(i/4pi) = 0` - a codimension-one COMPLEX
  linear constraint sitting exactly on the unique maximum of the symbol
  (`Phi(0) = +5.372`). Maximizing without it targets a strictly larger set, so a
  violation found there is not a counterexample. Corollary / tripwire: when a
  cheap computation's consequence is an absurdity (there: not-RH, via the
  machine-checked `0 ≤ qw ⟺ SourceRH`), the prior is overwhelmingly that the
  computation mis-scoped, not that the theorem failed - audit the class and the
  basis normalization first. This is F24 (position-by-position adjudication)
  applied to DOMAIN membership instead of operator slots.
  (Born 2026-09-17, docs/proofs/1578 §2.)

- (F29) SUPPORT IS LOCATION; SUMMABILITY IS VOLUME. When pricing a
  square-summability obligation whose defect has been confined to a strip or
  window, locate the HILBERT-SCHMIDT FACTOR in the chain (an L²-kernel
  operator, a prolate factor, a finite-rank piece) - a range-location fact
  contributes nothing: isometric embeddings into L² of a finite-measure window
  are bounded, range-confined, and NOT Hilbert-Schmidt. Corollary from
  1579's slot read: a committed generic concluding
  `Summable ‖defect ∘L rootConvolution ∘L M ∘L ...‖²` with the kernel
  HARDWIRED in the conclusion is not evidence for a consumer chain that
  lacks the kernel, however abstract its `M` parameter is - quantification
  over `M` means any factor may fill THAT slot, not that any chain matches
  the theorem. Price a square-sum by its HS source, never by its support.
  (Born 2026-09-17, docs/proofs/1579 §2.)
- (F30) ZONE-ANCHORED ASYMPTOTICS. Evaluate an asymptotic only inside its
  validity zone; a residual bound that diverges THERE flags the PRICING as
  void, not the object as infinite; and a divergence verdict must name the
  functional it diverges for. Recurrence: the β₋ = 1/2 row was invalid twice
  (zone violation + a smooth-compact-zone assumption) and its premise had to
  be withdrawn one wave later. (Born 2026-09-17, docs/proofs/1581.)
- (F31) SWEEP PREMISE SHAPES, NOT NAMES. The pre-spend sweep (F8) applies to
  the SHAPE of every premise a brick will consume - a uniform spectral gap, a
  domination, a compactness, an injectivity - not only to the cards that carry
  its name. Grep the maps/records for the ruling on the shape: a premise
  already ruled "not an available premise" in the sibling reduction returns
  under a new spelling with no new content. Recurrence: the 1586 angle-gap
  branch was retired one wave after being introduced. (Born 2026-09-17,
  docs/proofs/1587.)
- (F32) THE SWEEP INCLUDES THE MATHLIB LAYER, BY SHAPE. Before writing a
  helper, search Mathlib for the STATEMENT SHAPE, not the project's name for
  it: the tree carried a local duplicate of
  `Submodule.starProjection_comp_starProjection_of_le`, and an ad-hoc
  `nlinarith` replacement for a nested split Mathlib states outright. The
  search costs minutes; the duplicate is a permanent maintenance seam.
  (Born 2026-09-17, docs/proofs/1588.)
- (F33) CHECK THE EXISTENCE OF THE BASE OBJECT. A reduction chain must be
  checked for its base object's EXISTENCE, not only for the correctness of its
  steps: before transporting an obligation onto a subspace / fixed space /
  kernel, grep the tree for the ` x, x ≠ 0` hypothesis that carries that
  object's nonemptiness. An identity whose two sides both vanish is a valid
  theorem and a useless one, and the chain must be recorded as CONDITIONAL on
  the base being nontrivial. Recurrence: 1586-1589 price the gate residual on
  a carrier whose nonemptiness is nowhere proved
  (`Dev/SoninWindowWitness.lean:44`). (Born 2026-09-17, docs/proofs/1589 §5.)
- (F34) A RIGIDITY IDENTITY DOES NOT SURVIVE A MULTIPLIER. Before using an
  `H² ∩ H² = {0}`-type two-sided-analyticity step on a Toeplitz / model-space
  kernel, compute the horizontal-line growth of the RECIPROCAL multiplier:
  polynomial growth (here `|1/φ(x − iη)| ~ (1+|x|)^{2πη}`) is enough to make
  the two-sided extension fail `H²` while its boundary values stay in `L²`.
  Corollary: analyticity of `1/φ` in a half-plane decides only that the
  element is ENTIRE (1331 §2.2), never that it vanishes - and no Liouville
  shortcut replaces the rigidity, because entire functions CAN lie in
  `H²(₊)` (`((sin z)/z)² · e^{2Iz}` is a witness). (Born 2026-09-17,
  docs/proofs/1590 §4.)
