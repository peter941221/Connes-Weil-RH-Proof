# Compact crossing operator finite-prime read-off

## Result

Good: the missing compact-kernel operator trace realization of the selected
single-crossing coefficient is now proved in Lean.

This does not prove RH. It removes the earlier gap between the formal paired
diagonal integral and an actual trace of Hilbert--Schmidt-factorized
operators. The remaining route obligation is to identify this compact
factorization with the named whole-line convolution-smoothed crossing and the
semilocal metric variation, then prove the multi-prime sign gate.

## Objects

For `b >= 0`, the source coordinate is `s in [0,b]`. For a compact log test
`h` supported in `[a,c]`, the kernel coordinate is restricted to
`t in [a-b,c+b]`. The two continuous kernels are

```text
right(s,t) = h(t-s)
left(s,t)  = h(t-s+b).
```

`ContinuousKernelHilbertSchmidt.pairData` turns each kernel into an analysis
operator and proves square summability along a common Hilbert basis. The two
trace products are obtained by swapping the two analysis operators.

## Proof chain

```text
continuous compact kernels
        |
        v
Hilbert--Schmidt analysis operators A and B
        |
        v
ordinaryTrace(A^* B)
        = integral_[0,b] <right_s,left_s> ds
        |
        v
support reduction on [a-b,c+b]
        |
        v
<right_s,left_s> = F(b)
<left_s,right_s> = F(-b)
        |
        v
trace_forward + trace_reverse
        = b (F(b) + F(-b))
        |
        v
Euler-log weight 1 / (m sqrt(p^m))
        |
        v
finitePrimeTerm(p^m)
```

The support proof is not stored as a conclusion. It proves directly that the
crossing integrand vanishes outside `[a-b,c+b]`, uses Haar invariance under
`u=s-t`, and unfolds the existing `CompactLogTest.convolutionSquare`.

## Lean evidence

The main declarations are:

```text
section_pair_eq_convolutionSquare
reverse_section_pair_eq_convolutionSquare_neg
pairData_trace_eq_mul_convolutionSquare
reversePairData_trace_eq_mul_convolutionSquare_neg
owner_pair_traces_add_eq_singleCrossingPairDiagonalIntegral
eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow
positiveInterval_eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow
```

The last specialization uses the existing positive-interval Yoshida source
test and its proved log-support interval. It therefore keeps the source test,
compact support, convolution square, crossing kernels, and finite-prime atom
on one object.

Focused `#print axioms` output for the generic and positive-interval final
theorems contains only:

```text
propext
Classical.choice
Quot.sound
```

The import-facing audit is
`ConnesWeilRH/Dev/SelectedCrossingKernelAudit.lean`. Both aggregate builds
`ConnesWeilRH.Source.CC20Concrete` and
`ConnesWeilRH.Source.CCM25Concrete` succeed in the WSL verification mirror.

## Remaining boundary

The theorem proves an actual compact `A^* B` trace with the exact selected
finite-prime value. It does not yet prove that this operator is equal, after
extension/compression, to the whole-line object customarily written
`C_h^* C_h J_b`, nor that the sum over Euler parameters is the first variation
of the semilocal positive metric. Those are the next same-object obligations;
the finite-prime coefficient itself is no longer the bottom.
