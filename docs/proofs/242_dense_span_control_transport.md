# Proof 242: Dense-Span Control and Haar/Log Transport

Date: 2026-07-14

Status: accepted as an axiom-clean carrier and completeness repair.  The
finite-S semilocal sign and the identification of the route's global Mellin
rows remain open.

## 1. Correct completeness contract

The raw condition `DenseRange rows` is too strong for a typical Mellin or
Fourier family.  The usable condition is

```text
Dense (span (range rows))
```

`CompactBadSpace.lean` now provides:

```text
exists_finite_controlRows_of_dense_span
exists_finite_controlRowIndices_of_dense_span
exists_finite_hilbertBasis_controlRowIndices
```

For a compact operator `K` and `0 < c`, the first theorem selects a finite set
of actual row values.  If a vector is orthogonal to those rows, then

```text
Re <x, K x - c x> <= 0.
```

The indexed theorem retains the original row labels.  The Hilbert-basis
corollary is the immediate complete-row specialization.

## 2. Exact carrier transport

`GlobalLogControlFrame.lean` uses the existing map

```text
e : L2(Haar window) ~= L2(log window)
```

and the existing preimage basis.  It proves:

```text
dense_span_cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
exists_finite_cc20WindowHaarRegularRemainder_nonpositive_on_logBasis_rows
```

The second theorem starts with the compact logarithmic endomorphism, selects
finite rows there, and transports all three parts of the statement:

```text
row orthogonality
operator action
the shifted quadratic form
```

The key equations are the named preimage-basis application theorem,
`LinearIsometryEquiv.inner_map_map`, and
`cc20GlobalLogWindowRestrictedL2Endomorphism_eq_conjugatedHaarOperator`.
Thus the conclusion refers to one Haar operator and one finite row index set,
not two independently chosen witnesses.

## 3. What this does not prove

The prior guard
`not_global_mellin_one_factors_through_cc20CompactRestriction` remains valid.
Global Mellin values cannot be recovered from the fixed compact Haar
restriction without an additional global carrier or correction term.  A
complete abstract basis therefore cannot be relabeled as the route's three
Mellin rows.  The remaining producer obligation is still:

```text
negative Yoshida owner + actual finite-S rows
    -> contains the compact bad/control space
    -> same-object finite-S sign
```

No route root, skeleton, consumer, or RH theorem was rewired.

## 4. Verification

The Windows source snapshot was copied one way into the isolated WSL2 ext4
mirror.  The owning builds passed:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete.GlobalLogControlFrame

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.GlobalLogControlFrameAudit

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.DenseSourceControlFrameAudit
```

The final audit builds completed at 2987 jobs.  Every new declaration reports
only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx`, project axiom, route premise, or external positivity assumption
appears in the focused output.

## Route Judgment

```text
dense-span finite selector: accepted in Lean
Haar/log basis completeness transport: accepted in Lean
global Mellin/Haar factorization: rejected / still guarded
actual finite-S row-span coverage: open
finite-S remainder sign: open
RH: unproved
```
