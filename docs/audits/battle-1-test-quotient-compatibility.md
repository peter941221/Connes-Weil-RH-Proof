# Battle 1 Test And Quotient Compatibility

Status: proof audit for the first hard package behind the fixed-S positive
trace read-off.

This file does not certify Battle 1. It records the exact statement, source
anchors, and rejection tests needed before the route may use:

```text
Trace(R_Lambda U(h(F_g)))
  =
QW_lambda(g,g)
  +
source rank/pole channels.
```

Focused proof package:

```text
docs/proofs/battle-1-test-quotient-proof-package.md
```

## Result

Battle 1 now has route-evidence proof packages. The result remains
source-conditional and depends on the endpoint-strip `Cdef` package, but the
rank-repair branch no longer has an unexpanded no-defect read-off gap.

The note correctly isolates the wall:

```text
SourceTraceOperatorIdentification(S,lambda)
      |
      +-- SourceOperatorName(S,lambda)               [source-closed]
      |
      +-- RouteSourceOperatorEquivalence(S,I,lambda) [open]
              |
              +-- test conversion
              +-- quotient conversion
              +-- positivity conversion
```

The next theorem is therefore:

```text
TestAndQuotientCompatibility(S,I,lambda).
```

The exploration note states this target at
`docs/ConnesWeilPositivity.md:143121-143132`. It then marks the combined
compatibility as `paper-closed at route-note level` at
`docs/ConnesWeilPositivity.md:143564-143573`. That label is not a proof.

## Target Statement

For every admissible compactly supported route test `g`, define:

```text
F_g = g^* * g.
```

Using the same half-density convention as the CCM restricted Weil form, define
the source-side group test `h(F_g)`. Then the Connes source trace

```text
Trace(R_Lambda U(h(F_g)))
```

must read as:

```text
QW_lambda(g,g)
  +
Tate pole quotient channels
  +
zero-mode rank repair,
```

where the two Tate channels are supported only at:

```text
hat g(+i/2), hat g(-i/2),
```

and the rank repair is supported only at:

```text
hat g(0).
```

No finite-prime phase term, derivative jet, or endpoint-strip `Cdef` term may
enter through the quotient directions.

## Evidence Map

| subclaim | current evidence | audit status |
|---|---|---|
| Connes source operator has the shape `R_Lambda U(h)` with `R_Lambda=P_hat_Lambda P_Lambda` | `docs/ConnesWeilPositivity.md:143027-143052`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:802-810` | source-facing anchor |
| route operator has positive support-square shape | `docs/ConnesWeilPositivity.md:143054-143062`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:812-818` | route-side object |
| half-density conversion uses `F=Delta^(1/2)f`, respects convolution and inversion | `docs/ConnesWeilPositivity.md:143159-143170`; `docs/proofs/fixed-s-no-defect-compact-form-read-off.md` | source-interface read-off package |
| route source test should be `F_g=g^* * g` under the same convention | `docs/ConnesWeilPositivity.md:143185-143203`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:822-830`; `docs/proofs/fixed-s-no-defect-compact-form-read-off.md` | closed at route-evidence level |
| CCM restricted read-off gives the displayed `QW_lambda(g,g)` formula | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:991-1001`, `1129-1130` | source-interface obligation |
| Tate quotient directions map to the pole functional `W_(0,2)` | `docs/ConnesWeilPositivity.md:143381-143431`; `docs/proofs/battle-1-test-quotient-proof-package.md` | source-interface proof package |
| quadratic pole term is `2 Re(hat g(i/2) overline{hat g(-i/2)})` | `docs/ConnesWeilPositivity.md:143446-143460`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:1004-1011` | formula-level target |
| rank repair stays on `hat g(0)` | `docs/ConnesWeilPositivity.md:143491-143558`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:832-840`, `864-878` | weakest Battle 1 leg |

## Proof Skeleton

The proof must display this chain:

```text
route vector g
      |
      v
F_g = g^* * g
      |
      v
h(F_g) in Connes/CCM half-density convention
      |
      v
Trace(R_Lambda U(h(F_g)))
      |
      v
QW_lambda(g,g)
  + W_(0,2)(F_g)
  + C_(S,I)|hat g(0)|^2
```

Then the route may use triple vanishing:

```text
hat g(0)=hat g(+i/2)=hat g(-i/2)=0
```

to remove the finite-dimensional ledgers.

## Subclaim 1. Half-Density Compatibility

Required theorem:

```text
TestHalfDensityCompatibility(lambda):
  h(F_g) is the source-side group test attached to F_g=g^* * g
  in the CCM half-density convention.
```

The exploration note gives the intended convention:

```text
F = Delta^(1/2) f,
F(x)=x^(1/2) f(x),
QW(f,g)=Psi(f^* * g).
```

This part is recorded in the source-normalized read-off package. It cites the
CCM source-interface formula through the manuscript/source-reread anchors
instead of relying only on the route note.

Failure mode:

```text
theta_S(g) uses the unshifted test while QW_lambda uses the half-density test.
```

That would introduce a scalar, inversion, or prime-power normalization error
before any positivity argument begins.

## Subclaim 2. Tate Directions To Pole Ledger

Required theorem:

```text
TateDirectionsToPoleLedger(lambda):
  under the half-density convention and F_g=g^* * g,
  the two Tate directions removed in the Connes trace produce exactly
  W_(0,2)(F_g), with no finite-prime term and no endpoint-strip term.
```

The intended variable change is:

```text
old Mellin variable s = 1/2 + i t

s=0  <->  t=+i/2
s=1  <->  t=-i/2
```

The target pole functional is:

```text
W_(0,2)(F_g)
  =
hat F_g(i/2)+hat F_g(-i/2)
  =
2 Re(hat g(i/2) overline{hat g(-i/2)}).
```

This leg must not import finite-prime terms. Finite primes belong to the
`-sum_p W_p(F)` part of the CCM Weil distribution, not to the two Tate quotient
directions.

## Subclaim 3. Rank Repair To Zero Mode

Required theorem:

```text
RankRepairToZeroModeLedger(S,I):
  every no-strip rank repair from the fixed-S positive compression is a scalar
  multiple of |hat g(0)|^2, while every non-pure fixed-S defect enters Cdef.
```

Target form:

```text
Rank_(S,I)(g)
  =
C_(S,I)|hat g(0)|^2
```

up to terms already charged to endpoint-strip `Cdef`.

This is the weakest Battle 1 leg. The exploration note argues that pure Euler
metric terms act on the zero functional by scalar multiplication and that every
non-pure term contains a projection defect. A proof must replace that argument
with a finite normal-form lemma:

```text
fixed-S rank repair
      |
      +-- pure zero-mode term -> C_(S,I)|hat g(0)|^2
      |
      +-- projection-defect term -> endpoint-strip Cdef
```

## Rejection Tests

Battle 1 fails if any of these occur:

| rejection test | why it kills the route |
|---|---|
| `h(F_g)` differs from `F_g=g^* * g` by an untracked half-density factor | the `QW_lambda` read-off has the wrong test |
| `W_(0,2)` is counted both inside `QW_lambda` and again as `PoleJetExtra` | Theorem 2 would kill a duplicated pole ledger, not the source formula |
| the zero-mode rank repair is identified with a Tate direction | `hat g(0)` and `hat g(+/-i/2)` are different functionals |
| finite-prime terms enter through the Tate quotient directions | the prime sum would bypass the finite-prime visibility condition |
| a projection defect survives outside `Cdef` | Battle 2 and Battle 3 no longer cover all fixed-S errors |

## Acceptance Gate

Battle 1 passes only after the manuscript contains theorem-level proofs for:

```text
TestHalfDensityCompatibility(lambda)
TateDirectionsToPoleLedger(lambda)
RankRepairToZeroModeLedger(S,I)
```

Current proof packages close the first two legs at source-interface level and
reduce the rank-repair leg to:

```text
FixedSNoDefectCompactFormReadOff(S,I).
```

The projection-defect boundary-jet branch is recorded in
`docs/proofs/semilocal-q-compact-form.md`. The no-defect fixed-S compact-form
read-off is recorded in
`docs/proofs/fixed-s-no-defect-compact-form-read-off.md`.

Thus `RankRepairToZeroModeLedger` is closed at route-evidence level,
conditional on the cited source interfaces and Battle 3 endpoint-strip `Cdef`
package.

These packages combine into:

```text
TestAndQuotientCompatibility(S,I,lambda).
```

The current status is:

```text
Battle 1 proof package written,
source- and Cdef-conditional.
```
