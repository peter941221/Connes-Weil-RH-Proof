# 071 M3A Q-Root Algebraic Gate

Date: 2026-07-12

Result: the raw-square owner is rejected, but the natural logarithmic
first-order Q-root survives the first rejection gate.

## Candidate

Let

```text
Q = -d^2/dx^2 + 1/4,
L = d/dx + 1/2,
g = L xi.
```

For a compactly supported smooth `xi`, both `xi` and `g` remain compactly
supported and smooth. The derivative does not enlarge the support, and the
constant multiple has the same support.

## Same-Object Algebra

The additive involution is `f*(x) = conj(f(-x))`. It reverses the derivative:

```text
(d xi)^* = -d(xi^*).
```

Therefore

```text
(L xi)^* = (-d + 1/2) xi^*.
```

Since differentiation is a derivation of additive convolution and the two
factors commute under convolution,

```text
(L xi)^* * (L xi)
  = (-d + 1/2)(d + 1/2)(xi^* * xi)
  = (-d^2 + 1/4)(xi^* * xi)
  = Q(xi^* * xi).
```

This is the required object identity. It is not available for the current
`SelectedWeilSquareOwner`, whose stored square is only `g* * g`.

## What This Does Not Prove

The algebra alone does not prove that the selected finite-node constraints are
preserved. Proof record 072 checks that separate Mellin gate and shows that it
survives as well. The admissible owner must still expose `g = L xi` to the
finite-prime read-off. No theorem in the repository currently proves the
convolution derivative identities on the compact Schwartz domain or supplies
the M0 kernel-action equality.

## Decision

```text
raw owner -> Q-image bridge: rejected (proof guard 070)
L = d/dx + 1/2 Q-root: survives algebraic gate
finite-node compatibility: survives separately by proof record 072
M3A: pending, not accepted
```

The next rejection-first target is the compact-domain convolution derivative
theorem for the same `xi`, followed by the source kernel-action equality.
