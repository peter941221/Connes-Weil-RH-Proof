# 1018 - Lane R D3-root archimedean sign leaf

Date: 2026-08-18.

## Verdict

The first constructive Lean sign leaf is closed for one explicit
triple-vanishing, prime-free root.  The owner module proves

```lean
narrowArchRoot_archimedeanTerm_nonpos :
  C1SameOwnerWeil.archimedeanTerm narrowArchRoot.convolutionSquare <= 0

narrowArchRoot_qw_nonneg :
  0 <= C1SameOwnerWeil.qw narrowArchRoot
```

Both declarations are axiom-clean: the audit reports only
`[propext, Classical.choice, Quot.sound]`.

This is one explicit prime-free witness.  It is not the universal Lane R
sign statement, does not establish strict negativity for a Yoshida detector,
and does not prove RH.

## Construction

`C1LaneRD3Root.lean` defines the compact-support differential construction

```text
D3 = (d/dt) (d/dt + 1/2) (d/dt + 1)
g  = D3 h
```

and proves, for every compact-log test `h`, exact Laplace vanishing at
`0`, `1/2`, and `1`.  The current root is

```text
h = wideTest (narrowArchRadius / 4)
g = tripleVanishingRoot h
```

The support proof keeps a margin: the root is first put in
`Ioo (-R/2, R/2)`, then its convolution square is put in `Ioo (-R, R)`.
The existing `(-log 2, log 2)` support theorem is also used for the
prime-free `qw` readback.

## Archimedean budget

For `A = Re(F(0))`, `F = g.convolutionSquare`, and `C = log(4*pi)+gamma`,
the real integrand is bounded on three regions:

```text
0 < y < R       : f(y) <= A
R <= y <= 1     : f(y) <= -A/(2*y)
1 < y           : f(y) <= 0
```

The exact integral split therefore gives

```text
Re(archimedeanTerm F)
  <= (C + R - (1/2) * log(1/R)) * A.
```

The radius is chosen from the coefficient itself:

```text
R = exp(-4 * (C + 1)).
```

Consequently `log(1/R) = 4*(C+1)` and the scalar budget is nonpositive.
No decimal approximation is used in the formal sign proof.

## Numerical corroboration

`docs/proofs/1017b_lane_r_d3_root_probe.py` independently evaluates the same
D3 construction in WSL2.  With `C = 3.108240`, the reported ratios are:

```text
case                 arch/F0
bell c=0.333         -3.4893
bell c=0.200         -4.0004
flat-top w=0.333     -5.0984
flat-top w=0.250     -5.3854
```

The numerical vanishing residual is between `6.4e-10` and `4.5e-9` after
FFT differentiation.  These numbers support the sign and margin but are
not used by Lean.

## Scope boundary

The formal result covers one explicitly constructed root in the prime-free
subfamily.  The remaining Lane R obligation is universal spectral
nonnegativity over every healthy triple-vanishing square, including the
prime-inclusive case.  That RH-level statement remains open.
