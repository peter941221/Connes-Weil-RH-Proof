# 2723 — The wired `hprefix` proved from orbit data (hprefix REPLACED by {hright, htarget, hzero}; premises 7 -> 9 with the analytic sign estimate removed; no pin, gate, cap or RH-core premise touched)

Verdict: the 2708 joint-acceptance contract's P2 duty — deriving the
finite-set span prefix from the record-2722C transport theorem instead
of assuming it — is DONE on the stored row-B lane. Three theorems in
`ConnesWeilRH.Source.C1RowBPrefixTransport2723`:

```
dyadicShellIndex_abs_im_lt_six_2723
    |Im rho| <= 421/20  ->  dyadicShellIndex |Im rho| < 6
rowBSpanPrefix_re_le_negXiMult_sq_2723
    {hoff, h6, htarget, hzero} at any source test g
      ->  the wired hprefix shell-range-6 bound
rowBSpanPrefix_of_imCap_2723        (the same with the wired cap)
storedRowBPrefix2723                (the stored-carrier instance,
                                     in exactly the 2722F hprefix shape)
fourPointContradictionRowBStored2723
    the 2722F stored contradiction with hprefix REPLACED by
    {hright, htarget, hzero}
```

The proof body of the span bound is two steps: rewrite the shell-range
sum to the finite prefix by
`sum_spectralHeightShellPrefix_eq_shell_prefix` (the identification
2708 P2 named), then apply
`finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport`
with `rho ∈ spectralHeightShellPrefix 6` from
`mem_spectralHeightShellPrefix_iff`. The entire summation sign
argument now lives inside a proved theorem; what remains named is
pointwise orbit data.

Build green in the Linux-native workspace (footer 3868 jobs; 0 lines
starting `error:`, 0 `uses sorry`, 0 warnings on either entry file;
five-declaration axiom census exactly
`[propext, Classical.choice, Quot.sound]`). Checker
`scripts/check_rowB_prefix_2723.py`, 29/29 GREEN (build-attested grade)
(`results/2723_rowB_prefix_check.json`): parent/variant binder lists
pinned to the committed text, the positional application sequence
guarded, the hprefix token-stream tie between the 2722F hypothesis and
the 2723 stored conclusion machine-checked, four mutation controls
(one infeasible on first run, disclosed below), and the build census +
log sha256 carried in the artifact.

## 0. Binding-route audit (start-of-round declaration)

- Consumer: `fourPointContradictionRowBStored2722F` (record 2722F),
  reached from the 2722D/2722C chain up to the wired 2721C
  contradiction; downstream: selected detector `qw < 0` -> same-owner
  `qw >= 0` -> `SourceRH` -> Mathlib RH. This record acts only on the
  reopen-motion premise list of the wired row-B contradiction, exactly
  as authorized by the 2722E routing decision ("reopen obstruction is
  {hgate24, hprefix} + Lean-side bricks").
- Owner: the stored row-B configuration captured in 2722F (the
  record-1980 `build_owner` data for `CANDIDATES[1]`).
- Premise removed: `hprefix` (a shell-sum analytic sign estimate on
  the actual owner). Premises added: `hright` (right-off-line, a
  first-order sign fact), `htarget` (source-test Laplace values on
  the functional-equation orbit), `hzero` (convolution-square Laplace
  vanishing at in-ball non-orbit zeros). Logical count 7 -> 9.
- Failure criterion / stop: two modules, a small bounded number of
  record builds, no pin/gate/cap motion; stop at verdict. Used: 3
  builds (build 1 failed on the `neg_mul` shape and a missing final
  newline; build 2 green pre-rename; build 3 green after the
  long-line rename).

## 1. Instrument findings (this round's two build defects)

- `neg_mul` shape law: the 2722C transport theorem's conclusion prints
  `-↑(xiMultiplicity rho) * 24 ^ 2` (unary minus on the cast, then
  multiply) while the wired `hprefix` family spells
  `-((xiMultiplicity rho : Real) * 24 ^ 2)` (parenthesized product).
  These are NOT definitionally equal `Real` terms, and `exact
  htransport` dies at the bridge with a type mismatch whose two sides
  look identical in the pretty-printer. Bridge with
  `simpa only [neg_mul] using htransport`. Do not "fix" it by
  re-spelling either side: the stored instance must keep the PARENT's
  spelling (it is a positional argument into the 2722F contradiction),
  and the transport theorem must keep its own.
- Final-newline law (2ab/2ah recurrence): both fresh files were
  written WITHOUT a trailing newline; the whitespace linter reported
  `'' starts on column 16` on the Dev module's last line. Check
  `tail -c 20 <file> | od -c` after every fresh write.
- Long-line law for audit files: the second `#print axioms` line at
  111 characters tripped `linter.style.longLine`. The bundle prefix
  `#print axioms ConnesWeilRH.Source.C1RowBPrefixTransport2723.` is 60
  characters, so theorem names must stay at or below 40 characters;
  the span bound was renamed
  `rowBSpanPrefix_re_le_neg_xiMultiplicity_mul_sq_2723` ->
  `rowBSpanPrefix_re_le_negXiMult_sq_2723` (98-char print line).

## 2. The shell-index derivation

`dyadicShellIndex r = Nat.find (exists_lt_two_pow_succ r)`, so
`dyadicShellIndex |Im rho| < 6` from `|Im rho| <= 421/20` is
`Nat.find_min' (exists_lt_two_pow_succ _) hpow` with
`hpow : |Im rho| < 2^(5+1)` (`norm_num` reduces to `64`, `linarith`
closes against `21.05`), then `omega`. The `have`'s ascription to
`dyadicShellIndex` unifies against `Nat.find` at default transparency;
the house pattern (`rw [← dyadicShellIndex]`) was not needed.

## 3. Premise accounting and honesty line

`hprefix` was NOT a black-box premise: it is an analytic inequality
on the actual owner (a shell sum bounded by the negative anchor). The
replacement premises are strictly weaker in kind:

- `hright` is a first-order sign fact supplied by the RH consumer's
  off-line hypothesis (a right off-line zero), not an estimate;
- `htarget` / `hzero` are pointwise EQUALITIES (interpolation values
  and vanishings), with no summation or sign content;
- every sign estimate in the chain is now proved (the transport
  theorem), so `hprefix` is no longer an obligation at all.

So: `hprefix_removed = 1`, `premises_added = 3`, net logical count
7 -> 9, obligation shrunk IN KIND not in count (the 2722C doctrine).
`htarget` / `hzero` are named residual duties whose numeric support is
the 2719 complete-owner identification (`hzero`'s data leg: the stored
lists ARE the in-ball zero set) and the orbit-value tables
(`htarget`'s leg); their Lean certification is a separate brick. No
pin, no `hgate24`, no rho cap is discharged. No producer GO, no RH
claim, `DEAD_ON_CURRENT_FAMILY` unchanged.

## 4. Evidence

- Lean: `ConnesWeilRH/Dev/C1RowBPrefixTransport2723.lean` (sha256
  `2ea6e86bb8226bfb0ef30a72de086919db3da245d45d37d4f6f5b781fe379763`)
  and the paired `...2723Audit.lean`
  (`0314ea6e9292e14b6454c6de68878184477f507591e741eda3e71c24a6374be6`),
  five `#print axioms` records.
- Check artifact: `results/2723_rowB_prefix_check.json` (schema
  `2723_ROWB_PREFIX_CHECK_V1`), checker sha256
  `7ee2fd502e46309a88ca9cf328eddb23aa99f83d1ef31482ea7307707741dfeb`,
  build log sha256
  `1e9a9ac1bfd71edee4bb02743a322546c6dbb4aa9c161c40afc3ac3f18b8738a`
  (the log itself is gitignored; the artifact carries its values).
- Checker first-run defect (disclosed): the K1 mutation
  `dev.replace("rho hNorm hIm hcontractPin", ...)` was a NO-OP — the
  actual text has a newline between `hIm` and `hcontractPin` — so the
  "control" re-checked the unmutated copy and reported FAIL. Fixed by
  a regex mutation plus a `k1 != dev` changed-text assertion inside
  the control itself (infeasible-control law, second instance:
  2721B's arithmetic-impossible rejection preceded this one).  Two
  further checker edits (log path reduced to its basename; existence
  details made root-relative, so the committed artifact carries no
  machine paths) forced two artifact regenerations before the final
  run — the checker-sha binding law, second instance (2722E).
- Convention: the checker is location-independent (2722C pattern) —
  canonical sources resolve relative to the repository root; the
  build log and mirror are passed in as `--log=PATH` / `--mirror=PATH`
  and without them the recorded grade is source-only.  No machine
  paths are embedded in the committed script.
- WSL engine note: the build ran in the Linux-native workspace
  (toolchain v4.30.0, 289 GiB free); the stale-era mirror (no Dev
  oleans, only pre-2026-10-11 logs) was NOT used.  Sources were synced
  with md5 equality asserted on both sides before the build.  The live
  workspace path moves between record eras — recover it from the newest
  era build log and confirm the target module plus its oleans exist
  there before syncing; never assume the mirror path.