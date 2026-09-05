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
