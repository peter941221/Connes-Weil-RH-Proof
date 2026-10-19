# Near-collision lower bound for compact Laplace interpolation (record 3062)

Date: 2026-10-19.

Status: exact paper-level necessary cost bound. It is an abstract
interpolation obstruction and does not assert a close pair among the actual
source-zero nodes.

## Two nodes already force inverse-gap cost

Let `f` be a compact-log test supported in `(-B,B)`, with `B>0`, and let

```text
F(s) = laplaceAt(f,s) = integral exp(s*x)*f(x) dx.
```

Choose two distinct nodes `s1,s2` with `0 <= Re(s1), Re(s2) <= A`, where
`A>=0`, and impose `F(s1)=1`, `F(s2)=0`. Write
`delta=|s1-s2|`.

Along the line segment between the nodes, `0<=Re(s)<=A`. Differentiating the
compact Laplace integral gives

```text
F'(s) = integral x*exp(s*x)*f(x) dx,
|F'(s)| <= B*exp(A*B)*||f||_1.
```

The fundamental theorem of calculus along the segment then yields

```text
1 = |F(s1)-F(s2)|
  <= delta * B*exp(A*B)*||f||_1,
||f||_1 >= exp(-A*B)/(B*delta).
```

For the fixed-bump family in record 3060, its support radius is at most
`B=3/4`; the displayed bound already shows that no upper cost depending only
on node count and a bounded node region can hold as `delta -> 0` when the
prescribed values differ.

If the same test carries a quadratic strip-decay constant `C` of the type in
record 1738 and is supported in `(-1,1)`, that record's Plancherel bridge gives

```text
C >= (sqrt(3)/64)*||f||_1
  >= sqrt(3)*exp(-A)/(64*delta).
```

Here `A` bounds the real parts and the support radius is `B=1` in the last
display. Thus inverse-gap sensitivity is not only an artifact of the
determinant upper bound: any correction realizing a unit jump across a close
pair must pay at least order `1/delta` in this norm/decay scale.

## Scope for the healthy owner

In the healthy construction the target node `rho` has value `1`; every
distinct non-target source zero in the prefix has value `0`. A source zero at
distance `delta` from `rho` would therefore force the lower bound above with
`A<=3/2`. More generally, the lemma applies to any close pair in the actual
node set whose prescribed values differ.

No current record proves that such a close pair occurs for a hypothetical
off-line `rho`, nor supplies a uniform lower bound on its distance. This is
not a no-go for the selected owner. It proves the narrower point: an
interpolation cost estimate that only sees `N`, `H`, and `S` cannot be uniform
over arbitrary distinct node sets with differing target values. Either the
actual owner must come with a quantitative gap, or the construction must use
additional structure that avoids interpolating across an uncontrolled
near-collision.

Evidence:

- `ConnesWeilRH/Dev/C1ExplicitFiniteNodeCorrection.lean` defines the exact
  compact-log Laplace transform and the actual node-value correction.
- `docs/proofs/1738_selected_orbit_joint_symbol_and_tail_sampling.md`
  proves the L1-to-strip-constant bridge used in the second inequality.
- `docs/proofs/3061_fixed-bump_actual-owner_parameter-audit.md` records that
  the actual source-zero owner has no quantitative minimum-gap bound in the
  current source interface.
