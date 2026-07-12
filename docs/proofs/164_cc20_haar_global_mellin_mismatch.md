# CC20 Haar Interval / Global Mellin Mismatch

Date: 2026-07-12

Status: accepted obstruction; the current Haar operator is not yet a route
consumer.

## Result

The regular-kernel operator currently lives on

```text
Lp ℂ 2 cc20CompactHaarMeasure
```

where `cc20CompactHaarMeasure` is the measure `d rho / rho` on
`[1/2, 2]`.  The route's source tests, however, use the global Mellin
functional on `TestFunction` over the whole positive line.

The new Lean declarations prove a strict non-factorization:

```text
∃ g,
  g|_[1/2,2] = 0 ∧ Mellin(g, 1) ≠ 0

¬ ∃ L,
  ∀ g, Mellin(g, 1) = L(g|_[1/2,2])
```

Source module:

```text
ConnesWeilRH/Source/CC20Concrete/HaarMellinMismatch.lean
```

The witness is produced by
`exists_positive_interval_compact_test_real_bump` with support in `(3,4)`.
Its real part is nonnegative and equals `1` at `7/2`, so its Mellin value at
`s=1` is strictly positive.  Since `(3,4)` is disjoint from `[1/2,2]`, its
restriction to the Haar interval is zero.

## Why This Matters

The already-proved compactness theorem applies to the regular kernel on the
fixed Haar interval.  The route triple-vanishing conditions apply to global
Mellin evaluations.  The Lean counterexample shows that no linear functional
on the current Haar restriction can recover even the single global value at
`s=1`.

Therefore the missing producer cannot be filled by merely constructing three
Riesz vectors in the current Haar space.  A valid route must first provide one
of these lower interfaces:

```text
global-test Hilbert space + unitary restriction/transform theorem
or
same-object global trace operator whose evaluations are bounded there
or
an explicit correction/tail term transporting outside-window tests.
```

Defining the evaluation space as `⊤`, or silently replacing global Mellin by
the interval-restricted Mellin, would change the mathematical statement and is
not accepted.

## Verification

Using the existing WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/HaarMellinMismatchAudit.lean
```

Both passed.  The focused audit prints only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx`, RH premise, or Weil-positivity premise occurs.

## Route Judgment

```text
regular Haar-kernel compactness: accepted
global Mellin factorization through Haar restriction: rejected
three-point evaluation-span containment for current Haar operator: not applicable
active unconditional RH root removed: no
RH: unproved
```
