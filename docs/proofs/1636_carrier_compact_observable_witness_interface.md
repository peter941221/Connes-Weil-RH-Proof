# 1636 — compact-observable witness interface for the carrier base

Date: 2026-09-18

Status: formal interface landed; analytic producer still open. This brick serves
the healthy-CompactLog B5 carrier consumer in map 043. It does not claim that
the carrier is nontrivial and does not claim RH.

## 1. The exact compactness obstruction

Let `D : H -> G` be the Toeplitz/Hardy defect operator whose kernel is the
carrier, and let `K : H -> J` be a compact observable. For a bounded sequence
`x_n` with `D x_n -> 0`, the existing source theorem proves:

```text
D injective  ==>  K x_n -> 0
```

The new Dev theorem packages the contrapositive:

```text
bounded x_n
and D x_n -> 0
and NOT (K x_n -> 0)
and K compact
        ==> NOT Injective(D).
```

This is the precise concentration-compactness target. It does not assume a
uniform lower bound, a spectral gap, or a weakly convergent subsequence.

## 2. Formal artifact

`ConnesWeilRH/Dev/C1CarrierCompactObservableWitness.lean` adds
`not_injective_of_compact_observable_survives_approximate_kernel`, with the
paired audit module. The proof is a direct contrapositive use of the already
formalized compact-output theorem, so no analytic conclusion is hidden in the
interface.

Owning and audit build:

```text
Build completed successfully (2350 jobs)
error lines: 0
sorryAx lines: 0
axioms: [propext, Classical.choice, Quot.sound]
```

## 3. What remains to reach the carrier

The next producer must instantiate the interface with the committed carrier
operator, not with an unrelated model:

1. choose bounded finite-section approximate kernels `x_n` for the actual
   Hardy-Toeplitz defect;
2. choose a genuinely compact `K` (for example a finite-rank local probe or a
   compactly compressed convolution observable);
3. prove `D x_n -> 0` in the committed L2 norm;
4. prove `K x_n` does not converge to zero.

The numerical 1633--1635 records only suggest this producer; they do not
prove item 4. In particular, `sigma_min -> 0` alone is insufficient because
the approximate kernels may escape weakly to infinity. This record therefore
closes the logical interface but leaves the carrier base open.
