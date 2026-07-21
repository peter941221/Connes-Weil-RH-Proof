# Proof 467: Detector-Sonin translation law

## Result

For orthogonal corners `B P=P B=0`, the generic noncommutative identity is

```text
B W [U,P] B = -B [W,P] U B.
```

Applying it to Proof 466, with `W=C_g^dagger C_g`, gives

```text
rootCompletedSoninTranslationCommutatorPair(z)
  = -B[W,P]U_(-z)B.
```

The two sign changes from Proofs 466 and 467 cancel.  The complete finite-Euler
corner therefore has the probability-law form

```text
completeCorner
  = sum'_i weight_i B[W,P]U_(-displacement_i)B.
```

The only commutator is now the positive compact-root detector `W` against the
fixed source Sonin projection `P`.  The causal translation is a bounded suffix
and all finite-prime dependence remains in the probability law.

## Boundary

Proof 467 is an exact operator identity.  It does not prove that `[W,P]` is
trace class, justify the ordinary trace of an individual displacement atom,
or prove compact-support vanishing.  An `S_2` detector commutator alone still
needs a second boundary-localized `S_2` factor, or a direct `S_1` kernel
theorem, before Gate 3U can be closed.  The finite-S sign, Burnol's identity,
and `_root_.RiemannHypothesis` remain open.
