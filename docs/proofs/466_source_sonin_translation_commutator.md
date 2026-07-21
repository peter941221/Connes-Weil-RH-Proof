# Proof 466: Source-Sonin translation commutator

## Result

Let `P` be the source Sonin projection and `B` its orthogonal quotient band
inside the radial support.  For every bounded transport `A`, Lean proves

```text
P[A,B]B = -[A,P]B.
```

The proof uses only

```text
P B = 0,
B^2 = B.
```

Applied to Proof 465's translation response, this gives

```text
TranslationCommutatorPair(z)
  = -(C_g B)^dagger C_g [U_(-z),P] B.
```

The moving quotient-band commutator has therefore been replaced by the
translation commutator with the fixed source Sonin projection.  Both roots
and the quotient input remain in the completed response.

Writing

```text
S(z)=(C_g B)^dagger C_g[U_(-z),P]B,
```

Proof 465's complete probability law becomes

```text
completeCorner = -sum'_i weight_i S(displacement_i).
```

The analytic response `S(z)` contains no finite-prime family or moving
projection; all finite-Euler dependence is confined to the causal probability
law.

## Boundary

Proof 466 is an exact operator identity.  It does not prove that
`[U_(-z),P]` is Hilbert--Schmidt, give its dependence on `z`, justify an
ordinary trace of an individual response, or prove compact-support
vanishing.  Gate 3U, the finite-S sign, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.
