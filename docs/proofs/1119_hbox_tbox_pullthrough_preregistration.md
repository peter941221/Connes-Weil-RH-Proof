# 1119 - Hbox rational data + T-box (Gt,Mt)-level pull-through: pre-registration

Date: 2026-09-04. Status: PRE-REGISTRATION committed BEFORE any build.
Consumers (record 1118): sub-obligation (a)'s full box theorem (1118 §1a:
"for all real Gt/Mt with G_lo <=entrywise Gt <=entrywise G_hi and M_lo
<=entrywise Mt <=entrywise M_hi: forall c, R.mulVec c = 0 -> dotProduct c
(Mt *v c) <= U * dotProduct c (Gt *v c)") and sub-obligation (b)'s Lean
half (1118 §1b: "per class, the rational matrices G_lo/G_hi/M_lo/M_hi as
committed data + entrywise containment theorems (norm_num) tying them to
1115's MID/rad decomposition").  After this record, the ENTIRE (a)+(b)
chain of the class certificates reduces to the single named analytic
hypothesis `Hbox` (the true Gram/arch data lies in the committed outward
boxes) - the law-34 chain's own obligation, unchanged.

## 0. Ground truth verified before registration (exact Fraction precheck)

On all three classes ((2,8), (3,8) from 1113_cert.json, (4,8)):
  (i)  rad_G and rad_M are EXACTLY symmetric entrywise (symmetrization of
       the perturbation is lossless against the committed Dred_rad/radp);
  (ii) the committed bundle box sits INSIDE the 1115 box entrywise:
       G_lo >= mid_G - rad_G and mid_G + rad_G >= G_hi (likewise M) - the
       bridge from `Hbox` to the radius form of the T-box hypothesis;
  (iii) Lam (1115_qchain.json) is unit-lower-triangular, so |Lam| is data
       and Lam*L = L*Lam = 1 is a pure rational identity.

## 1. What lands (per class a in {28, 38, 48})

### 1a. Generated data module `C1HboxRationalData.lean` (generator
`docs/proofs/1119_generate_hbox.py` from 1115_qchain.json + the cert
bundles), plus generic `InBox`/`Hbox` defs and the entrywise identities:
  - data: radG_a, radM_a (8x8, from qchain rad_G/rad_M), GLo_a, GHi_a,
    MLo_a, MHi_a (8x8, exact fraction strings from the cert bundles),
    absK_a (8x5), Lam_a, absLam_a, DredRad_a (5x5);
  - symmetry: radG_a i j = radG_a j i, radM_a i j = radM_a j i (norm_num);
  - reverse containment (the Hbox bridge): GLo_a i j >= Q*.G i j -
    radG_a i j AND Q*.G i j + radG_a i j <= GHi_a i j, likewise M;
  - abs bridges: absK_a i j = |Q*.K i j|, absLam_a i j = |Lam_a i j|;
  - provenance identities (norm_num, raised budgets):
    hLamL_a : Lam_a * L = 1 and hLLam_a : L * Lam_a = 1;
    hDredRad_a : absK_a.transpose * (mu_a * radG_a + radM_a) * absK_a
      = DredRad_a  (Dred_rad = |K|^T (|U| rad_G + rad_M) |K|, mu = -U);
    hRadp_a : absLam_a * DredRad_a * absLam_a.transpose = radp_a
      (radp = |Lam| Dred_rad |Lam|^T - ties the NEW data to the LANDED
      record-1118 radp/slacks; the slack identity is untouched).

### 1b. Generic module `C1EntrywiseBound.lean`: the one-shot entrywise
triangle lemma |(X^T * B * Y) k l| <= (a * p * c) k l from function bounds
|X| <= a, |B| <= p, |Y| <= c; plus matrix smul/transpose bookkeeping.

### 1c. Per-class pull-through `C1TboxPullthrough.lean`:
  - `tbox_a` (the 1118 §1a full statement, radius form): for ANY Gt/Mt
    with |Gt - Q*.G| <= radG_a and |Mt - Q*.M| <= radM_a entrywise and
    c in ker R: c.(Mt.c) <= U * c.(Gt.c).  Mechanism: closure witness
    c = Kx; quadratic form sees the symmetrization via x.(M.x) =
    2 x.(((M + M^T)/2).x) with the product-transpose ring identity
    (K^T B K)^T = K^T B^T K (NO sum reindexing anywhere); the perturbation
    B - D is entrywise-bounded by |U| rad_G + rad_M = p (symmetric), the
    symmetrized perturbation by p; propagation through K by the generic
    lemma = DredRad_a; whitened congruence z = L^T x, x = Lam^T z (from
    hLamL/hLLam), E = Lam Delta Lam^T bounded by radp_a; the landed
    record-1118 kernel `qform_nonneg_whitenedBox` closes.
  - `tbox_true_a`: `Hbox` (true data in the committed bundle box) +
    reverse containment => radius form => the same conclusion for the
    TRUE data - Hbox is the only analytic hypothesis left in (a)+(b).
  - `absolute_true_a`: gate-level absolute form with ICgate (record 1117)
    on the LHS: Hbox + hrep + hker + hnorm => ICgate w.convSq <= -mu_a -
    the registered 1118 §2 ABSOLUTE shape, now unconditional from (a)+(b)
    modulo the named `Hbox`/`hrep`/`hnorm` slots.

## 2. Gates (registered before the build)

G1: focused `lake build` of the three new modules + audit on the ext4
    mirror; acceptance = "Build completed successfully" footer AND zero
    `^error:` lines.  G2: audit `#print axioms` on every public
    declaration of the three modules - allowed set exactly {propext,
    Classical.choice, Quot.sound}; zero sorry.  G3 (fidelity): `tbox_a`
    must elaborate with the hypotheses literally |Gt i j - Q*.G i j| <=
    radG_a i j (radius form) and `absolute_true_a` with LHS literally
    `ICgate ((w).convolutionSquare)` and RHS `-mu_a`.  G4: staged-file
    hygiene grep 0 matches before every commit.

## 3. Falsifiers (no threshold weakening)

Any of the new per-class identities failing to prove (symmetry, reverse
containment, hLamL/hLLam, hDredRad, hRadp) => report that class,
shrink the claim to the remaining classes, bank the failure as data.
If a norm_num identity cannot close at maxHeartbeats 2e9, split it
per-entry before ANY other change.  No box, radius, slack, or U value
may be edited.

## 4. Run protocol

Commit (prereg, generator, modules) BEFORE the first build; one
root-caused fix commit per failing build; post-run addendum after G1-G4.
RH NOT claimed; no map change keyed.

## 5. Post-run addendum (2026-09-04, after build 7)

VERDICT: LANDED.  Final focused build (1119_hbox_build7.log) = "Build
completed successfully (3653 jobs)", zero `error:` lines, zero warnings on
all four new modules.  Modules: `ConnesWeilRH/Dev/C1EntrywiseBound.lean`,
`C1HboxRationalData.lean` (generated), `C1TboxPullthrough.lean`,
`C1TboxPullthroughAudit.lean`.

G1 PASS (footer + zero error lines).  G2 PASS: 51/51 audited declarations
report exactly `[propext, Classical.choice, Quot.sound]` (2 EntrywiseBound
+ 30 HboxRationalData + 19 TboxPullthrough); zero `sorry` in the log.
G3 PASS: the two audit `example`s compile - `tbox_q28` elaborates with
hypotheses literally `|Gt i j - Q28.G i j| <= radG_q28 i j` (radius form)
and `absolute_true_q28` with LHS literally `ICgate w.convolutionSquare` and
RHS `-mu_q28`.  G4 PASS: per-commit staged-diff hygiene grep 0 matches
(commits 52776b3, 3558dfd, 482f77f, 2922537, 300db83, 00c2b34, 5e3a1f9,
8814d7f).

Falsifier outcome: all 30 generation-time exact-Fraction checks PASS on
all three classes (U literals, radius symmetry, REVERSE containment with
worst clearances printed in the generated module, Lam unit-lower +
two-sided inverse, |K|^T (mu radG + radM) |K| = DredRad,
|Lam| DredRad |Lam|^T = radp).  The preregistered per-entry split
fallback was NOT needed: every heavy norm_num identity closed at
maxHeartbeats 2e9.  No box, radius, slack, or U value was edited;
the record-1118 kernel data (radp/dd/slacks) is untouched.

Registered deviations (statement-shape only, no analytic content):
- `tbox_of_identities` does NOT take `dd` as an explicit parameter: the
  whitened kernel's `d` is pinned by `hslack`'s type (the kernel call
  consumes it there); likewise `hLamL` is not a hypothesis of the generic
  theorem - the pull-through only needs the one-sided inverse `hLLam`
  (x = Lam^T z).  `hLamL` remains a PROVEN 1a provenance identity in
  `C1HboxRationalData` and stays under audit.
- v4.30 API facts baked into the proofs: `abs_add`/`sub_neg` (old
  meanings) do not exist (the subtraction triangle is `abs_sub : |a - b| <=
  |a| + |b|`; `sub_neg` is now `a - b < 0`); `linarith` does not split
  nonlinear atoms, so the transposed index bound is rewritten via the
  symmetry hypotheses BEFORE linarith (`mu * radG j i` and
  `mu * radG i j` are distinct atoms); `Matrix.ext_iff` points from
  entrywise to equality (`.mpr`); `rw` rewrites only one instantiation at
  a time (double transposes need `simp only`).

Headline shapes landed per class a in {28, 38, 48}:
- `tbox_a` (radius form): for ALL Gt/Mt with |Gt - Q*.G| <= radG_a,
  |Mt - Q*.M| <= radM_a entrywise and c in ker R:
  c.(Mt.c) <= U * c.(Gt.c) - the 1118 section 1a FULL box theorem.
- `tbox_true_a`: `Hbox GLo GHi MLo MHi G_true M_true` => the same bound
  for the TRUE data (bridge = reverse containment hrevG_a/hrevM_a).
- `absolute_true_a`: hrep + hker + hnorm + `Hbox` =>
  `ICgate w.convolutionSquare <= -mu_a` (1118 section 2 ABSOLUTE shape).

Remaining after this record (unchanged map): (c) Hker (ker R_true vs
ker R_mid: C1 exact annihilation / C2 drift bound) is the only missing
named slot for the class-certificate chain; T2 (Stage-B instance for a
D1-pinned g) open.  RH NOT claimed.
