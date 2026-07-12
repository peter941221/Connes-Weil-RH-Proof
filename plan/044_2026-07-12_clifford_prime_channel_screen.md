# 044 Clifford Prime-Channel Screen

Date: 2026-07-12

Status: noncommutative channel shortcut rejected by the positive Gram cost.

## Candidate

Attach anticommuting Clifford generators `Gamma_p` to prime translations and
form one positive square.  Anticommutation cancels mixed-prime words and might
replace the linear scalar cost by an Euclidean norm.

## PSD Gate

For a finite visible set, the first prime channels have weights

```text
w_p = log(p) p^(-1/2).
```

Any positive block Gram realization of the signed linear functional
`-sum_p w_p x_p` has a Schur-complement constraint.  In the simplest Clifford
normalization the block is

```text
[ c       w^T ]
[ w       I   ] >= 0,
```

which forces `c >= ||w||_2^2` (or an equivalent spectral shift
`c >= ||w||_2` after normalizing the coupling).  Enlarging the lower block to
reduce the shift simply moves the same cost into an additional diagonal
channel.

The norm diverges over visible primes because

```text
sum_p (log(p)^2/p) = infinity.
```

Clifford anticommutation therefore removes mixed words but not the cofinal
positive cost.  A spinor trace also kills the desired linear terms unless a
state is chosen; choosing that state restores the same Gram constraint.

## Verdict

```text
mixed-prime cancellation: algebraically possible
positive linear Weil read-off: Schur-cost constrained
cofinal prime scalar: divergent
Clifford shortcut: rejected
```

See proof 122.

