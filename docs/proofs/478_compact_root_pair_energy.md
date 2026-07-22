# Proof 478: compact root pair energy

## Result

The result is good: the support-polynomial Hilbert--Schmidt bounds for the
compact continuous kernels now apply to the actual whole-line boundary legs
used by the physical trace pair. It does not yet close Gate 3U or RH.

Let `K_-` and `K_+` be the negative and positive compact root kernel
operators, and let `S_-` and `S_+` restrict whole-line `L2` to their
support-forced compact input windows. The genuine pair legs are

```text
left  = K_- S_-,
right = K_+ S_+.
```

The adjoint of each restriction is norm-preserving zero extension. Therefore

```text
norm(S_-) <= 1,
norm(S_+) <= 1.
```

The Hilbert--Schmidt ideal inequality and the existing continuous-kernel
bounds give, in every named global Hilbert basis,

```text
sum_i norm(left e_i)^2
  <= (c-a)^2 * seminorm_0,0(g)^2,

sum_i norm(right e_i)^2
  <= (c-a)^2 * seminorm_0,0(g)^2.
```

This is the first direct quantitative input for Proof 477's fixed physical
energy. The module also transports both bounds through the genuine CCM24
radial translations. Since those translations are unitary, the same
polynomial controls the two legs of `translatedCompactRootPairData` at every
`lambda`. The bound is independent of every finite visible prime family.

## Boundary

Proof 478 controls the primitive outer compact pair and its radial translate.
The next producer must transport the same energy through the
Hardy--Titchmarsh reflection, then combine it with the fixed prolate factor.
It does not exchange renewal and basis sums, assert the Gate 3U canonical
polynomial, prove the finite-S sign, integrate the negative owner, prove
Burnol's identity, or prove `_root_.RiemannHypothesis`.
