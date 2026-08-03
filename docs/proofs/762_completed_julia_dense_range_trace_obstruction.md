# Proof 762: Completed-Julia dense-range trace obstruction

Date: 2026-08-02

Status: exact infinite-dimensional obstruction to transferring a
Hilbert--Schmidt energy bound through dense-range cancellation.  A completed
Julia analysis may be isometric, and the fixed physical source input may be
injective with dense range, while the composed endpoint energy stays bounded
and the uncomposed ordinary trace diverges.

This closes the proposed automatic handoff from the Proof 501/712 completed
history to Proof 756's direct target negatively.  It does not disprove the
actual canonical Gate 3U estimate.  A source-specific bounded observability
factor or a direct estimate of the complete signed scalar could still prove
that estimate.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| completed Julia analysis is an isometry              | retained             |
| fixed physical input is Hilbert--Schmidt             | retained             |
| fixed physical input may have dense range            | retained             |
| composed endpoint energy controls uncomposed trace   | false exactly        |
| dense-range cancellation preserves quantitative norm | false exactly        |
| uniform bounded inverse of the fixed input            | impossible           |
| Proof 756 -> Proof 378 automatic common-input bridge | rejected             |
| Burnol-specific observability theorem                | not rejected         |
| direct canonical signed-scalar estimate              | active route         |
| Gate 3U / finite-S sign / Burnol / RH                 | open / open / open   |
+------------------------------------------------------+----------------------+
```

The rejected inference is

```text
DenseRange(A)
  + uniform Hilbert--Schmidt control of X_S A
  + an isometric completed Julia lift

  -X-> uniform control of Tr(X_S).                    (DR.1)
```

Dense range is a qualitative uniqueness property.  Gate 3U needs a
quantitative observability property.

## 2. Exact diagonal obstruction

Let `H` be an infinite-dimensional separable Hilbert space with orthonormal
basis `(e_n)`.  Choose positive numbers

```text
alpha_n>0,
sum_n alpha_n^2<infinity.                            (DR.2)
```

In particular, `alpha_n -> 0`.  Define the positive diagonal operator

```text
A e_n=alpha_n e_n.                                  (DR.3)
```

Then

```text
norm(A)_2^2=sum_n alpha_n^2<infinity,               (DR.4)
```

so `A` is Hilbert--Schmidt.  Since every finite-support vector belongs to
`Ran(A)`, one also has

```text
closure(Ran(A))=H.                                  (DR.5)
```

Thus `A` is injective and has dense range.

Let `P_n=e_n tensor e_n` be the rank-one orthogonal projection and put

```text
X_n=alpha_n^(-1) P_n.                               (DR.6)
```

Every `X_n` is positive, self-adjoint, finite rank, and trace class.  Direct
calculation gives

```text
X_n A=P_n,
norm(X_n A)_2=1,
Tr(X_n)=alpha_n^(-1) -> infinity.                   (DR.7)
```

No limiting trace cycle or numerical approximation occurs in `(DR.7)`.  It
is an exact calculation on one basis vector.

Consequently, there is no bound for `abs Tr(X)` which depends only on

```text
DenseRange(A), norm(A)_2, and norm(X A)_2.           (DR.8)
```

The conclusion remains false after restricting `X` to positive rank-one
operators.  Self-adjointness and positivity therefore do not repair the
handoff.

## 3. Why a completed Julia isometry does not help

Let

```text
U:H -> K,
U* U=I                                               (DR.9)
```

be any isometry.  Proof 501's completed Julia analysis has exactly this
form: it stores the terminal survivor and every co-defect slot in one `L2`
carrier.

The isometry preserves the singular values and the Hilbert--Schmidt energy
of the fixed input:

```text
norm(U A e_n)=alpha_n,
norm(U A)_2=norm(A)_2.                              (DR.10)
```

Define the readout

```text
Y_n=X_n U*.                                         (DR.11)
```

Then

```text
Y_n U A=X_n A=P_n,
norm(Y_n)=alpha_n^(-1).                             (DR.12)
```

The completed history is lossless, but the quantitative cost has moved into
the readout norm.  Since `alpha_n -> 0`, no family-uniform readout bound can
be inferred from isometry or dense range.

The same fact appears as the bounded-inverse obstruction.  If a bounded map
`Z` satisfied

```text
Z A=I,                                              (DR.13)
```

then

```text
1=norm(e_n)=norm(Z A e_n)
 <=norm(Z) alpha_n,                                 (DR.14)
```

which is impossible as `n -> infinity`.

## 4. Application to the current Gate owner

The relevant repository objects have the following roles:

```text
Proof 501:
  completedJuliaAnalysis is isometric;

Proofs 699--712:
  fixedPhysicalSourceInput may be proved to have dense range after
  full-boundary injectivity and analytic-window hypotheses;

Proof 714:
  replacing that input by `id` makes the Hilbert-basis energy divergent;

Proof 756:
  Target_S=-L_S^dagger B_completed J is an uncomposed source operator;

Proof 761:
  Gate 3U asks for the ordinary real trace of that uncomposed target.
                                                               (DR.15)
```

Proof 762 identifies the quantitative mechanism behind Proof 714.  An
estimate for

```text
Target_S * fixedPhysicalSourceInput                 (DR.16)
```

does not estimate `Tr(Target_S)`.  Dense range can cancel the input from an
exact operator equality, but it cannot transfer a norm or trace bound across
the vanishing singular values of a Hilbert--Schmidt operator.

Likewise, Proof 378's proposed common-input Julia pairing is useful only
after a bounded source-specific factorization has been proved.  Merely
inserting the fixed Hilbert--Schmidt root and invoking dense range would
repeat `(DR.1)`.

## 5. What would escape the obstruction

The diagonal example does not reject either of the following genuinely
stronger source theorems.

First, one could prove a bounded observability factor on the literal physical
range:

```text
Target_S=Z_S A,
sup_S norm(Z_S)<=C(1+B_root)^d.                     (DR.17)
```

Equation `(DR.17)` is a Douglas domination, not a consequence of dense range.
It must use the complete outer, reflected second-support, and prolate
geometry.  Proofs 381 and 388 show that near invariance and abstract Julia
prefix geometry do not manufacture it.

Second, one can avoid cancellation through `A` and estimate the already
completed scalar directly:

```text
abs Re FullCompletedKernelTrace_(canonicalFamily owner)
 <=C(1+B_root)^d norm(g)_(H^r)^2.                  (DR.18)
```

This is Proof 761's actual Gate bottom.  In the relative-displacement
language of Proof 413 it is the support-coupled bound for the complete signed
functional `Lambda_(S_F)`, after simultaneous translation history has been
quotiented and before the first absolute value.

## 6. Route decision

```text
completed history + dense-range cancellation:
  rejected as a quantitative Gate producer by `(DR.7)`;

range-only Julia alignment:
  still requires a new bounded physical observability theorem;

direct completed-kernel owner:
  retained;

next analytic target:
  canonical-family relative-displacement / Burnol boundary estimate
  for the intact signed scalar;

Gate 3U, finite-S sign, Burnol identity, RH:
  unproved.                                         (DR.19)
```

No Lean source is added by Proof 762.  The obstruction is the exact
infinite-dimensional calculation `(DR.2)--(DR.14)`; it does not require a
finite numerical probe.
