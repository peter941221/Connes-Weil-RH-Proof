# Proof 776: Causal Local-Root Corner Guard

## Result

Proof 776 adds one exact Lean normal form and one sharp model guard for the
current Gate 3U owner.

With

```text
T_S = finiteEulerTransportOperator,
D_S = finiteEulerDualFrame,
E   = radialSupportProjection,
R   = sourceSoninProjection,
C   = rootConvolution,
```

Lean proves

```text
Target_S
 = D_S* E T_S (I-R) C* C J.                         (776.1)
```

The declarations are:

```text
finiteEulerDualFrame_adjoint_comp_radialSupport_eq_self
finiteEulerDualFrame_adjoint_comp_transport_eq_ambientGramReadback
finiteEulerTargetCommutatorResponse_eq_causalDualFrameRootCorner
```

Equation `(776.1)` is stronger than merely writing the target with
`H_S = T_S* T_S`: the actual radial half-line is inserted before the one
forward Euler transport. The complete source complement `(I-R)` remains
intact. Thus the outer, reflected second-support, and prolate channels have
not been separated before the compact root acts.

```text
source carrier
    |
    J
    v
C* C --> (I-R) --> T_S --> E --> D_S* --> source carrier
```

This is a carrier and ordering result. It is not a Gate 3U estimate.

## Why It Matters

The previous single-corner form was

```text
Target_S = G_S^-1 J* H_S (I-R) W J,
H_S = T_S* T_S,
W   = C* C.
```

The new identity uses two source-specific facts.

```text
D_S* T_S = G_S^-1 J* H_S,
D_S* E   = D_S*.
```

The first is the exact dual-frame readback. The second follows because the
actual transported source frame lies in the radial half-line. Neither fact
licenses a norm estimate for `D_S*`, `T_S`, or `(I-R)` separately.

## Local-Root Guard

The causal form is still not enough by itself. The following exact lattice
model has every property listed below, but its corner trace grows linearly.

Let `H = l2(Z)` with bilateral shift

```text
U e_n = e_(n+1),
E   = projection onto span{e_n : n >= 0}.
```

Fix `0 < a,b < 1` and define

```text
T = I-a U,
C = (I+b U)/(1+b),
W = C* C,
H_a = T* T.
```

For every positive integer `N`, let `R_N` project onto

```text
span{e_3, e_6, ..., e_(3N)},
```

and let `J_N` be its inclusion. These are exact identities on the bilateral
lattice:

```text
T E H subset E H,
T^-1 E H subset E H,
H_a W = W H_a,
H_a > 0,
W >= 0,
norm(W) <= 1,
R_N <= E,
G_N = J_N* H_a J_N = (1+a^2) I_N.
```

The root `C` has only the two translation taps `0` and `1`. Thus it is a
strict local-root analogue of compact convolution support.

For each source vector `e_(3j)`, the two neighboring detector terms survive
the complement, and the two neighboring metric terms return them:

```text
(I-R_N) W e_(3j)
  = b/(1+b)^2 [e_(3j-1)+e_(3j+1)],

J_N* H_a (I-R_N) W J_N e_j
  = -2ab/(1+b)^2 e_j.
```

Consequently the exact finite-rank corner is

```text
G_N^-1 J_N* H_a (I-R_N) W J_N
  = -2ab/((1+a^2)(1+b)^2) I_N,

Tr = -2Nab/((1+a^2)(1+b)^2).                         (776.2)
```

The inverse Gram norm is at most one, while the trace in `(776.2)` is
unbounded as `N` grows.

## Scope Boundary

This is not a counterexample to the CCM24/CC20 source. Its projection
`R_N` is a sparse internal projection, not the actual completed Sonin owner

```text
R = E Q E-K_prol.
```

It has no Fourier-support identity, Mellin transport, or prolate correction.
It proves the narrower statement below.

```text
causal half-line preservation
  + positive local convolution root
  + H_S W = W H_S
  + contractive inverse source Gram
  + arbitrary internal projection R <= E
  does not imply a dimension-free Gate corner bound.
```

Therefore the remaining source theorem must use the actual Fourier/prolate
coupling of the completed Sonin projection. A proof that only uses the outer
half-line, local root support, positivity, and metric/detector commutation
cannot close Gate 3U.

## Verification

The accompanying finite-window calculation verifies the exact local formula
in `(776.2)` away from artificial matrix edges. The infinite-lattice
commutation and half-line invariance above are algebraic identities, not a
claim inferred from that finite window.

```text
python3 -B docs/proofs/776_causal_local_root_corner_probe.py
```

```text
+--------------------------------------------------------------+----------------+
| claim                                                        | status         |
+--------------------------------------------------------------+----------------+
| causal dual-frame compact-root normal form                  | Lean proved    |
| local causal/root/commuting-metric guard                     | exact model    |
| uniform bound from those properties alone                    | disproved      |
| source Fourier/prolate coupled compact-root estimate         | open           |
| Gate 3U / finite-S sign / Burnol identity / RH               | open           |
+--------------------------------------------------------------+----------------+
```
