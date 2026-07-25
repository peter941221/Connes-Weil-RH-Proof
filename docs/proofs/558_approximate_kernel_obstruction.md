# Proof 558: approximate-kernel obstruction

Result: the Gate 3U producer now has a sharp approximate-zero-mode guard.  A
family-uniform raw Douglas bound would force the raw adjoint to vanish along
every sequence whose packed physical analysis tends to zero.

For any sequences `p_n`, `S_n`, and source vectors `x_n`, if there is an
`epsilon > 0` such that

```text
epsilon <= ||Raw(p_n,S_n)^dagger x_n||

||AmbientBoundaryAnalysis(p_n,S_n) x_n|| -> 0,
```

then no finite common bound can satisfy the current raw Douglas contract, and
therefore no finite common physical-domination bound can satisfy it either.
The proof uses the actual packed analysis norm identity, so the ambient and
moving-boundary channels stay summed.

This is stronger than the exact-kernel guard: an exact zero mode is the
constant-sequence special case, but a wave-packet sequence can obstruct a
bounded factor even when the kernel is trivial.

The Lean owner is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaApproximateKernelObstruction.lean
```

The theorem deliberately does not construct an actual sequence on the
finite-S source carrier.  Proof 554's ambient translation wave packets are
not silently promoted to that carrier.  The remaining source question is
therefore concrete:

```text
construct an actual approximate zero mode with nonvanishing raw output;
or prove the actual raw row satisfies the uniform Douglas estimate.
```

No Gate 3U, finite-S sign, Burnol identity, or RH conclusion is claimed.
