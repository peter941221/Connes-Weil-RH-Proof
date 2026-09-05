# Record 1145 - G2 repair: kernel-checked certificate for the 1139 checkpoint

Date: 2026-09-05.  Status: PRE-REGISTRATION, committed BEFORE any build.

Consumer: the two public q28 producers of record 1139
(`q28_baseMoment_bounds_of_concrete_certificate`,
`q28_hbox_of_concrete_certificate`), which are held at G2-HOLD because the
private checkpoint `q28_certificate_Q`
(`ConnesWeilRH/Dev/C1ConcreteClassMomentCertificate.lean:304`) is proved by
`native_decide` and therefore carries the extra native-compiler axiom.
RH is not claimed; no statement changes.

## 1. Why every cheap replacement route is dead (root cause, recorded)

The checkpoint's four data values are sums over `powerCoefficientListQ 35`
- a 35-layer cached convolution over `ℚ` with 666 entries per layer.  The
Lean 4 kernel performs delta/iota reduction WITHOUT cross-reference
sharing: forcing any spine element of layer 35 re-evaluates a 20-ary
branching tree of depth 35 (~20^35 node evaluations).  Consequences:

* `decide` is dead twice over: the cached list cannot be kernel-evaluated,
  and the toolchain's `Rat.blt` is externally implemented so rational
  comparison instances do not reduce in the kernel either (1139 addendum).
* one-shot `norm_num` on the 666-term goal is dead (1140 attempt, reverted).
* per-coefficient evaluation routes are dead: forcing `(P^35).coeff k`
  without sharing costs ~10^9-10^10 rational mult-adds at large `k`.

The interpreter (which backs `native_decide`) DOES share the cached layers
as materialized list values, which is exactly why only the native route
has worked so far.

## 2. The repair: layered literal grounding (1115 pattern)

Restore the sharing EXPLICITLY in the proof term, where the kernel can
use it.  The generator `1145_generate_g2_certificate.py` (pure stdlib
`Fraction`, deterministic, byte-reproducible) emits, inside the owning
module:

1. Eighteen private literal tables `groundLayer_2, groundLayer_4, ...,
   groundLayer_34, groundLayer_35 : List ℚ` - the exact 666-entry value of
   `powerCoefficientListQ n` for every EVEN layer plus layer 35
   (payload ~4.1 MB; period 1 would cost ~7.2 MB with no kernel benefit).
2. Eighteen private grounding theorems
   `groundLayer_eq_n : powerCoefficientListQ n = groundLayer_n`, each
   proved by unfolding ONE or TWO convolutions against the previous
   literal table and closing by literal rational equality.  Kernel cost
   per grounding is ~400 mult-adds per entry (two unshared layers against
   a shared literal), i.e. seconds per layer at the top widths.
3. The checkpoint replacement: `q28_certificate_Q` keeps its STATEMENT
   verbatim and its proof becomes
   `have h35 := groundLayer_eq_35` + `simp only [comparisonDataQ, h35,
   listCoeffQ, Finset.sum_range_succ, ...]` + `norm_num` on literal
   bignum sums (the four sums evaluate to the generator's exact literals
   `a0, b0, a2, b2`; the five conjuncts then close by literal rational
   arithmetic, slacks ~7e-16 measured exactly).

Every emitted proof is a first-order literal computation the kernel
checks without any shared-free deep recursion.  No new axiom, no `sorry`,
no native route, no statement change.

## 3. Probe results backing the design (exact, `Fraction`)

* layer-35 table cross-checked against an independent polynomial-power
  evaluation: 0/666 mismatches.
* exact sums: `a0 ~ 5.77115374`, `b0 ~ -1.34734005`, `a2 ~ 12.0107595`,
  `b2 ~ -2.86657955` (up to 7867 exact digits each).
* all five conjuncts TRUE with slacks 7.69e-16 / 7.79e-16 / 6.91e-16 /
  7.05e-16 and `b0 < 0`, `b2 < 0` - consistent with the native checkpoint.
* payload: period-2 grounding = 4.06 MB of literals over 18 groundings.

## 4. Gates

```text
G1  Runner build of the owning + audit modules green: success footer AND
    zero ^error: lines.
G2  THE ACCEPTANCE GATE: the two public q28 producers print exactly
    [propext, Classical.choice, Quot.sound]; zero sorryAx; zero
    native-decide axioms anywhere in the audit output.
G3  Determinism: rerunning the generator reproduces the emitted Lean
    block byte-for-byte.
G4  Hygiene: no local paths, no private artifacts, no mojibake; the
    module's statements are byte-identical to 1139's except the proof
    of the private checkpoint.
```

## 5. Falsifiers / abort protocol

* If a grounding or the final `norm_num` fails to close: RED iteration,
  root-caused, fix batches committed before rebuild (1115 protocol); the
  fallback ladder is (i) per-chunk sum evaluation, (ii) period-1
  grounding (7.2 MB), (iii) per-coefficient grounding theorems.
* If kernel evaluation exceeds the runner budget at ANY rung: report the
  exact obstruction in the addendum and HOLD; do NOT weaken any
  statement, do NOT reintroduce `native_decide`, do NOT touch the q28
  boxes (1139 G4 clause).

## 6. Addendum (2026-09-05, RED-5 post-mortem and the RED-6 fix batch)

RED-5 (the first full-splice build) failed with two independent root
causes, both fixed in this batch and validated on a small-shape scratch
before this rebuild:

```text
F1  Chain bug: groundLayer_eq_35 referenced groundLayer_eq_33 (its
    n-2 predecessor), but the even-layer emission schedule never
    produced layer 33 -> Unknown identifier.
F2  Step explosion: `simp only [groundLayer_eq_{base}, ...]` rewrote the
    cached-layer occurrence inside the UNREDUCED inner map, inlining the
    666-entry literal table at every (k, i) pair - 13320 copies per
    grounding - exceeding the simp step budget on all 18 groundings.
```

The RED-6 design (this emission) replaces both:

```text
R1  Period-1 grounding: all 35 layers get literal tables and theorems
    groundLayer_eq_n, each chaining from its n-1 predecessor; the
    groundLayer_eq_35 consumer now chains from 34.
R2  Single-inline grounding: `show` rewrites the goal once by
    delta+zeta to expose exactly ONE syntactic occurrence of
    powerCoefficientListQ (n-1) inside the map lambda; `rw` inlines the
    previous table ONCE; the tables themselves are delta-unfolded by an
    explicit `simp only [range_666_lit, groundLayer_{n-1},
    groundLayer_{n}]` (measured: `norm_num [table, ...]` does NOT
    delta-unfold a plain table constant); `norm_num
    (config := { maxSteps := 20000000 })` then walks List.getD and
    closes the 666-entry map equality by literal rational arithmetic.
R3  Per-index endpoint/moment grounding (NEW machinery): the
    endpointAQ/endpointBQ equation lemmas recurse on `k + 2`, which
    does NOT match closed Nat literals under simp (measured RED-6:
    `simp only [endpointAQ]` makes no progress on `endpointAQ 4`).
    The generator emits, for each of the four tables, one step theorem
    of arity `n + 1 + 1` (or `n + 1` for the moments) proved by
    `rw`, and 666 per-index value theorems chained bottom-up through
    explicit-index bridges.  4 + 2664 declarations total.
R4  Checkpoint proof: `have h35 := groundLayer_eq_35` + one
    `simp (config := { maxSteps := 20000000 }) only [...]` carrying the
    2664 per-index lemmas + table/getD/sum lemmas, then one `norm_num`.
    Statement unchanged; slacks ~7e-16 as probed (section 3).
```

Scratch validation (8-entry / 4-entry analogues, `lake env lean`, zero
errors): grounding chain shape, single-inline closure, `n + 1 + 1`
bridge, moment adapter, per-index lemma-list consumer - all green.
G3 determinism re-verified on the regenerated 12.34 MB module (two
generator runs, identical md5).  Payload now 7.3 MB of literal tables
(period 1) plus the per-index value theorems.

## 7. Addendum 2 (2026-09-05, RED-6 post-mortem and the RED-7 fix batch)

RED-6 (period-1 grounding + 2664 per-index endpoint/moment theorems +
one mega-simp checkpoint) was ABORTED at ~50 min wall: the lean process
reached 36 GB RSS with swap 100% full and ~4e7 major page faults - it
was swap-thrashing, not computing.  Root cause: the checkpoint's single
`simp only` carried all 2664 per-index lemmas plus the table/getD walk
over FOUR 666-term exact rational sums in ONE tactic, so every
intermediate stayed alive simultaneously on top of the 36 literal
tables and 35 grounding proofs already held by the environment.

A second measured failure inside RED-6's chunk experiment: shifted
indices from `Finset.sum_range_add` (`f (n + x)` with bound `x`) are
NOT literalized by simp's arithmetic simprocs, so per-index lemmas
cannot fire on shifted sums (small-scope probe, trace captured).

RED-7 design (this emission) removes the mega-tactic entirely:

```text
R5  Prefix-sum functions: for each of the four comparison sums, a
    private def sum<prefix> : Nat -> Q with
    | 0 => 0 | j+1 => sum<prefix> j + coeff j * term j, a symbolic
    bridge sum<prefix>_eq : (sum over range j) = sum<prefix> j proved
    by induction + rfl, and 667 per-index value theorems
    sum<prefix>_at_j, each proved by an explicit (j-1)+1 show-bridge,
    one rw of the recursion, one rw of the predecessor value theorem,
    a SINGLE getD walk, and one bignum norm_num.
    Peak memory per declaration is trivial; every intermediate dies at
    the end of its declaration.
R6  Four consumption theorems comparison_<a0,b0,a2,b2>_eq : the exact
    comparisonDataQ summand sums equal the generator's literals, each
    by two rewrites.
R7  Checkpoint proof: `simp only [comparisonDataQ]` (zeta + projection
    iota), `rw` of the four comparison theorems, one small `norm_num`
    over the five conjuncts.  No native_decide, no new axioms.
```

The generator now asserts the five conjuncts on the exact prefix-sum
values before splicing (prereg section 3 slacks reproduced: a0 ~
5.7711537437, b0 ~ -1.3473400459, a2 ~ 12.0107594822, b2 ~
-2.8665795533), and byte-stability was verified by a double run
(identical md5).  Module size ~21 MB source; ~6000 declarations.

## 8. Addendum 3 (2026-09-05, RED-7 post-mortem and the RED-8 module split)

RED-7 (prefix-sum machinery, single certificate module) was ABORTED at
~34 min wall with the SAME signature as RED-6: 36 GB RSS, swap 8192/8192
MB full, CPU rate collapsing.  Root cause now isolated: the ENVIRONMENT
mass itself - ~466000 bignum multiply-add proof terms for the 35-layer
grounding chain plus 3666 table literals plus ~5344 small value
theorems, all resident in one Lean process - exceeds the WSL2 guest's
36 GB no matter how small each tactic is.  Host RAM is 63.4 GB with
Windows-side headroom ~8 GB, so raising the guest limit cannot be the
primary fix.

RED-8 (this batch, approved by Peter) splits the module along its
dependency chain so no single process ever holds the whole environment;
Lean's mmapped oleans keep the imported-but-untouched grounding proofs
file-backed and reclaimable:

```text
C1ConcreteClassMomentBase           the 1139 def block, moved VERBATIM;
                                    namespace KEPT (all fully-qualified
                                    names unchanged; zero downstream edits)
C1ConcreteClassMomentGroundingA     index literal + layer tables 0..17
                                    + groundings 1..17              ~1 MB
C1ConcreteClassMomentGroundingB     layer tables + groundings 18..35 ~6.5 MB
C1ConcreteClassMomentGroundingC     per-index endpoint/moment values
                                    + prefix sums + the four
                                    comparison_*_eq theorems        ~13.5 MB
C1ConcreteClassMomentCertificate    checkpoint + public consumers   ~37 KB
```

Build-process peaks become roughly 15 GB (A), 15 GB (B, with A mmapped),
4 GB (C), 1 GB (certificate).  Secondary win: any future edit to the
checkpoint or consumers rebuilds in seconds instead of re-grinding the
grounding chain.  Generated-file ownership moves to the generator, which
now asserts the five checkpoint conjuncts (prereg section 3) and writes
A/B/C byte-stably; the checkpoint statement is untouched.

## 9. Addendum 4 (2026-09-05, RED-8b/8c post-mortem and the RED-8d fix batch)

RED-8b died at parse time on two section-pairing errors introduced by the
surgery (`Missing name after 'end': Expected the current scope name
'Computable'` in Base, orphaned `end Computable` in the certificate);
lake built NOTHING because an unparseable file yields no import list.
RED-8c fixed both (Base built in 1.8 s), then GroundingA failed fast and
cheap (55 error lines, no memory pressure) with the REAL structural
error of the split, which RED-8b had masked:

```text
F3  Namespace mismatch: the grounding modules declared
    namespace ...Grounding{A,B,C}, so Base's short names
    (powerCoefficientListQ, listCoeffQ, taylorCoefficientQ) did not
    resolve inside the grounding theorems (Unknown identifier at every
    grounding), and the checkpoint's unqualified consumption of
    comparison_a0/b0/a2/b2_eq from C would have failed the same way.
```

RED-8d (this batch) moves A/B/C into the SHARED owning namespace
`ConnesWeilRH.Source.C1ConcreteClassMomentCertificate` - module names
unchanged, namespaces now span the four modules exactly as the original
single-module design intended.  All generated names are distinct across
A/B/C (groundLayer_{0..35} / per-index steps and values / prefix sums /
comparison theorems), so the shared namespace has no collisions, and
every declaration stays public (private does not cross modules).
Validated pre-build: Base already green; A/B/C re-emitted with identical
bodies, only the namespace lines differ.
