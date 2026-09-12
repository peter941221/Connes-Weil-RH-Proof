# Record 1362 (DESIGN + LOCKED STATEMENTS) - decomposing TARGET-A2 => gate into bricks: L1 window-split summability brick (buildable now, no new zeta math) / L2 the registered wall

```text
+---------------------------------------------------------------------+
| What it is: the exact Lean build plan between the named open         |
| theorem A2 (1360 s4) and the stop word (1358 s4).                    |
| Why: 1361 proved the mechanism inventory is EMPTY for A2 - so the    |
| only reachable advance is making the IMPLICATION A2 => gate           |
| machine-checked up to a named, isolated analytic lemma.               |
| How: two-layer decomposition below; L1 locked statements (s3) are    |
| committed BEFORE the build log exists (law 42). RH NOT claimed.      |
+---------------------------------------------------------------------+
```

## 1. Where the chain currently ends (committed anchors)

    A2 (paper correlation theorem: N_off(I) < f*(A(I)) N(I))
        |  ???  <-- this record isolates the ???
        v
    per-window contest balance (1353 arithmetic, MODEL)
        v
    total contest balance  0 <= qw g  per vanishing g   [B4.1, 275aca6]
        v
    weilCriterion  <=>  SourceRH                        [B4.3 + d767a1d]

The ??? has two independent halves:
  (L1) window-locality of the MASSES: splitting onLineSpectralMass /
       offLineSpectralMass over ordinate windows - pure summability
       bookkeeping over the committed `SpectralSummable` API. NO new
       analysis; NO zeta facts. Buildable by us, today.
  (L2) the frame-to-count bridge: turning A(I)/N(I) counts into
       energy inequalities per window (localized-kernel sampling +
       sinc-tail gluing). This is the C6 science (1353 s5 two-limb
       target; 1358 s2 OUTCOME 3 says it is NOT derivable from any
       located technology - the wall itself).

## 2. Why L1 is worth building anyway (first-principles reason)

Without L1, a future proof of A2 on paper must ALSO re-derive the
window-vs-total bookkeeping informally - and informality is exactly
where campaigns die (1352 register-vs-text trap; 1361 re-derive-never
-inherit note). L1 makes the wall one lemma thick, named, and the
rest a machine-checked corridor: if A2 (in the L1-anchored form below)
is ever proved by anyone, the gate discharges by compilation.

## 3. LOCKED L1 statements (pre-build; leaf `Dev/C1A2WindowSplit.lean`)

Definitions (from committed dictionary only; window by ordinate
interval, W : Real > 0, k : Int, wW(k) := Set.Icc (k*W) ((k+1)*W)
pulled back along `fun rho : XiZero => rho.1.im`):

    def onLineWindowSet (g : CompactLogTest) (W : Real) (k : Int) : Set XiZero
    def windowOnLineMass (g) (W) (k) : Real    -- tsum over the window set
    def windowOffLineMass (g) (W) (k) : Real   -- same, offLineZeroSet side

Theorems (the brick's whole content; all `sorry`-free required):

    T1  windowMass_split_on   : onLineSpectralMass g
          = Sum (fun k => windowOnLineMass g W k)   -- Int-indexed tsum
        (proof route: Summable.split / tsum over countable Icc-fiber
         partition; needs only spectralSummableProp + re-linearity)
    T2  windowMass_split_off  : offLineSpectralMass g
          = Sum (fun k => windowOffLineMass g W k)
    T3  qw_window_assembly    :
          C1SameOwnerWeil.qw g
            = Sum (fun k => windowOnLineMass g W k + windowOffLineMass g W k)
        (T1 + T2 + qw_eq_onLineSpectralMass_add_offLineSpectralMass)
    T4  contestForm_windowwise_iff :
          (contest balance per B4.1) <->
          Sum (fun k => windowOnLineMass g W k)
            >= max 0 (- Sum (fun k => windowOffLineMass g W k))
        (T3 rewritten; the gate in window coordinates - no analysis)

Non-claims (locked): T1-T4 prove NOTHING about zeta windows being
favorable; they are bookkeeping identities. A2 itself, and the
count-vs-energy bridge L2, are outside this leaf by construction.
Failure branch (pre-registered): if the Int-indexed Icc partition
measurability/summability API fights back harder than expected,
fallback = Nat-indexed half-line windows (k >= 0 and k < 0 leaves) -
same content, uglier statement; outcome note goes in s4 honestly.

## 3a. AMENDMENT, pre-build (law-42 correction BEFORE any log exists; F5)

Caught on implementation recon; no digit existed when this edit was
committed, so the lock is being FIXED, not moved:

  (a) Type name: the committed index type is
      `sourceNontrivialZeroSet` (CC20YoshidaNearZeros.lean:31, a Set ℂ
      subtype); s3's "XiZero" was prose. No semantic change.
  (b) REAL DEFECT: s3 wrote windows as closed `Set.Icc (k*W) ((k+1)*W)`
      - closed windows OVERLAP at endpoints, so they do NOT partition
      and the split T1/T2 would double-count any zero with ordinate
      exactly on a window edge (boundary zeros are not excluded
      anywhere). Replacement: the partition by FIBERS of
      `windowIndex W rho := Int.floor (rho.1.im / W)` - these fibers
      are exactly the half-open intervals [kW, (k+1)W) and tile by
      construction. Added T0 (statement-preserving):
      `windowSet_mem (hW : 0 < W) : rho ∈ windowSet W k <->
        (k:Real)*W <= rho.1.im /\ rho.1.im < (k+1:Real)*W`
      - so the "ordinate interval" meaning of s3 is RESTORED as a
      theorem, with the correct half-open shape.
  (c) s3's `def onLineWindowSet (g : CompactLogTest) ...` carries an
      unused `g`: the window is geometry of zeros, not of tests.
      Retired; the def is `windowSet (W : Real) (k : Int)` (also
      avoids unused-variable lint). T1-T4 keep their locked signatures
      `(g : CompactLogTest) (W : Real)`.
  Theorem NAMES are preserved verbatim from s3: windowMass_split_on /
  windowMass_split_off / qw_window_assembly /
  contestForm_windowwise_iff, plus the new T0 windowSet_mem.

## 4. Acceptance contract (locked now)

Batch number assigned at launch; build Dev.C1A2WindowSplit +
Dev.C1A2WindowSplitAudit (prints `#print axioms` for all four
theorems, expected: three standard axioms only - Data.attempt
prohibited); footer sentinel rule (log-not-exit-code); post-green
byte-identity check vs built mirror (1356 s6 law); no post-build
edits to locked statements (contract-integrity rule).

## 5. L2 registration (the wall, named, with its three sub-lemmas)

The remaining analytic content, stated so it can be attacked (or
imported) as three separate science items - none Lean-buildable today:

  L2a  localized sampling: for test kernels restricted to one window,
       energy of on-line nodes >= A(I)^2 * (frame norm) - the
       1353 prolate/ceiling arithmetic made rigorous (this is C6).
  L2b  tail gluing: cross-window leakage bounded by sinc^2 tails
       (1346 s4 "tails ~sinc^2 ~= 0" made rigorous; explicit budget).
  L2c  count-to-energy: A(I), N(I) (paper quantities in TARGET-A2)
       realized as the L2a/L2b quantities for the committed kernel
       family at scale W = pi/log2.

Under OUTCOME 3 (1360 s3) none of L2a-L2c follows from located
technology; they are the honest shape of "weeks-to-months of
research program" (1357 s5 option B) that the owner's direct-attack
order walks INTO, not around. L1 shrinks the corridor so that L2's
wall has one face, not three.

## 6. Next actions (running order)

1. Launch L1 build (next batch; statements are locked as of this
   commit; pre-reg = this file, s3+s4).
2. On green: 1363 outcome record + brick absorbed into the 1356
   chain file or kept standalone (decide by import weight).
3. W0 (task #14) continues in parallel: Connes number-field Q1-Q3.
4. After L1: attempt L2c-formal only (definitions-side: realize
   A(I)/N(I) for our kernel - may be partially doable without new
   analysis; adjudicate after L1 lands).

## 7. ITERATION LEDGER (leaf build session; appended before any batch log - source-level API facts only, no build digits)

Name reconnaissance via `lake env lean` probes on this fork's Mathlib
snapshot ("API names are DATA"), plus three compiler iterations on
Dev/C1A2WindowSplit.lean. Facts that changed the design:

1. DESIGN SHRINK (F5-style admission): the planned ENNReal descent
   (tsum_fiberwise_ennreal + ofReal pull-in/pull-out + outer-summability
   fight) is DEAD BEFORE BIRTH: this fork has
   `HasSum.sigma : HasSum f a -> (forall b, HasSum (fun c => f <-b, c->)
   (g b)) -> HasSum g a` (AddCommMonoid + ContinuousAdd + RegularSpace
   hypotheses) - unconditional-fiber Fubini directly over R. No sign
   hypothesis is needed at all, so the pos/neg decomposition of the
   signed off-line family is also unnecessary. The brick's core is one
   `hasSum_fiberwise` lemma; summability of the window-mass function
   (needed by T3) comes free as `HasSum.summable`.
2. Value-level reindexing along equivalences is STILL absent in this
   snapshot (probed unknown: HasSum.comp_equiv, tsum_sigma, tsum_sigma',
   summable_sigma, summable_sigma', HasSum.comp_injective,
   tsum_comp_injective, Summable.comp_surjective) - hence the one
   hand-rolled infrastructure lemma `hasSum_comp_equiv` (Finset-net
   argument; cofinality witness `t.image e.symm`).
3. Compiler-verified environment facts for the next builder
   (candidates for AGENTS 7b):
   (a) `(SummationFilter.unconditional L).filter` is DEFEQ to
       `Filter.atTop` on `Finset L` - a `show` passes, so net arguments
       can be written atTop-style after `unfold HasSum`.
   (b) `le_div_iff0`/`div_lt_iff0` in this snapshot are stated with the
       DIVISION form on the LEFT (a <= b / c <-> a * c <= b): proving
       the multiplication form from the division form needs `.mp`,
       the opposite of the usual memorized direction.
   (c) `Finset.sum_image` takes an explicit `Set.InjOn g (s : Set _)`
       proof, and dot-resolving `hf.injective.injOn s` mis-elaborates;
       pass `(show Set.InjOn e (↑s) from fun x _ y _ h => e.injective h)`.
   (d) `rw` closes `t subset t` via the @[refl]-tagged subset lemma, so
       a trailing `exact` after such an rw errors "No goals".
4. Pre-green state: leaf + audit compile with ZERO errors in the mirror
   environment (iteration 3); `grep -c sorry` = 0; audit leaf prints 12
   fully-qualified `#print axioms`. Official batch: 1558
   (lake build Dev.C1A2WindowSplit + Dev.C1A2WindowSplitAudit); the
   batch log remains the only digit-bearing artifact, per s4.
