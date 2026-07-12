# CC20 Parameterized Window Containment

Date: 2026-07-12

Status: lower carrier lemma accepted; the parameterized Haar operator and its
`lambda -> infinity` trace limit remain open.

## Result

For every `PositiveIntervalCompactTest p`, Lean proves:

```text
∃ lambda > 1,
  support(p) ⊆ [1/lambda, lambda]
```

Declarations:

```text
exists_cc20Window_containing_positiveIntervalCompactTest
positiveIntervalCompactTest_support_subset_cc20Window
```

Source:

```text
ConnesWeilRH/Source/CC20Concrete/WindowContainment.lean
```

The proof chooses a natural `lambda` larger than `1`, the upper support
endpoint, and `1/lower`. It uses only `lower_pos` and the support interval
already carried by `PositiveIntervalCompactTest`.

## Route Meaning

This repairs one part of the previous fixed-window mismatch:

```text
positive compact test
        -> some finite [1/lambda, lambda]
        -> candidate parameterized Haar space
```

It does not assert that the Weil form is invariant under scaling, and it does
not identify different `lambda`-spaces. The next required producer is a
genuine family of Haar measures/operators on these windows, followed by a
common-form-domain limit that preserves the CC20 trace read-off.

## Verification

Using the existing WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/WindowContainmentAudit.lean
```

Both passed. The focused declarations use only:

```text
propext
Classical.choice
Quot.sound
```

No RH premise, Weil-positivity premise, `sorryAx`, or stored conclusion is
introduced.

## Route Judgment

```text
finite-window carrier inclusion: accepted
parameterized Haar operator: open
lambda-exhaustion trace/read-off: open
active unconditional RH root removed: no
RH: unproved
```
