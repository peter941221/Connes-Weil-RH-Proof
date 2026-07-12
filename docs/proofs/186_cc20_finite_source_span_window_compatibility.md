# Proof 186: Finite source-span window compatibility

## Result

`GlobalLogKernel.lean` now proves that any finite set of source tests admits
one common logarithmic window:

```text
exists_cc20LogWindow_containing_finite_logPullbacks
```

For arbitrary complex coefficients on that finite set, the compressed
cross-window identity extends from one source pullback to the whole finite
linear combination:

```text
cc20GlobalLogWindowL2Operator_eq_on_finite_logPullback_sum_of_le
```

The proof uses only the finite maximum of the individual support windows,
operator/projection linearity, and single-test compressed compatibility.
No source trace value or RH-level conclusion is stored in the theorem.

## Verification

Using the retained WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/GlobalLogHaarAudit.lean
```

The aggregate build completed `3504/3504` jobs. The import-facing audit for
both declarations reports only:

```text
propext
Classical.choice
Quot.sound
```

## Boundary

This enlarges the stable source-test domain from one pullback to finite linear
spans. It does not prove density of that span in the full source Hilbert
space, a cross-window trace limit, the finite-S positive trace/read-off, the
diagonal `-2 Id` identity, or unconditional RH.
