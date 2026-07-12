# Positive Owner Batch Screen

Date: 2026-07-12

Status: three additional self-designed positive-owner variants screened and
rejected at the algebraic level. These are not Lean owners. RH remains
unproved.

## Candidate A: Schur-positive 2x2 block

Try to prescribe the exact Euler-log crossing `K=Q ell_a(U) P` in a positive
block

```text
H = [ I  K ]
    [ K* B ],       H >= 0.
```

The Schur complement forces

```text
B - K* K >= 0.
```

Thus the diagonal block carries at least the positive cost `K*K`. This cost is
not a compact boundary correction. For a test square whose support is shorter
than `log(p)/2`, the linear Weil atom at `p` is zero, but the cross-half-line
operator `Q ell_a(U) P C_h` is nonzero. Its positive square therefore has
strictly positive trace while the desired prime read-off is zero. This is the
same-object contradiction, now expressed directly as a Schur complement.

Conclusion: a positive block cannot retain the exact linear atom without
paying a diagonal bulk. This is not repaired by choosing `B` larger.

## Candidate B: two-ancilla balanced block

Use two copies with opposite off-diagonal channels:

```text
H = [ I  0  K  0 ]
    [ 0  I  0 -K ]
    [ K* 0  B  0 ]
    [ 0 -K* 0  B ],       H >= 0.
```

The opposite signs cancel mixed words in an *indefinite* graded read-off, but
positivity is checked before that read-off. Each Schur complement still
requires `B >= K*K`; the two costs add. Replacing the positive trace by the
grading difference is exactly the forbidden step of measuring an indefinite
observable instead of a positive owner.

Conclusion: ancilla doubling cancels algebraic cross terms only after
positivity has been lost; it does not remove the PSD diagonal cost.

## Candidate C: norm-compressed Cayley block

To respect the projection bound `||K||<=1/2`, replace the Euler logarithm by

```text
K_c = (1/2) tanh(2 ell_a(U)).
```

The first coefficient is correct because `tanh(x)=x+O(x^3)`. However,

```text
(1/2)tanh(2 ell) = ell - (4/3)ell^3 + O(ell^5).
```

Since `ell=aU+(a^2/2)U^2+(a^3/3)U^3+...`, the `U^3` coefficient becomes

```text
1/3 - 4/3 = -1,
```

instead of the required `1/3`. The compression therefore fixes the norm by
destroying the prime-power coefficient at the first nontrivial cubic order.

Conclusion: any scalar Cayley compression with the correct linear coefficient
has a cubic coefficient mismatch unless a new non-scalar correction is added;
that correction returns to the Schur-cost problem.

## Batch verdict

```text
Schur-positive block:       rejected by unavoidable K*K bulk
two-ancilla balance:        rejected by PSD Schur cost
Cayley/tanh compression:    rejected by p^3 coefficient -1 != 1/3
```

The surviving design space is now narrower: a valid owner must use a
non-translation-invariant positive construction whose diagonal cost cancels
inside the same object without an indefinite grading, while preserving all
`a^m/m` coefficients. No such construction has been found in this round.
