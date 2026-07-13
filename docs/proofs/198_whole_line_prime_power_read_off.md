# Proof 198: Whole-line crossing pair equals the selected prime-power atom

Status: accepted crossing-layer milestone. The actual forward and adjoint
whole-line traces now feed the existing finite-prime atom. RH remains unproved.

## Result

Let `owner` be one selected convolution square, let `p` be prime, `m != 0`,
and put

```text
b = m log(p),
T_b = cc20GlobalConvolutionCrossing owner.sourceTest.involution.test b.
```

The theorem
`eulerLog_weighted_global_pair_traces_eq_finitePrimeTerm_pow` proves

```text
1 / (m sqrt(p^m)) * (Tr(T_b) + Tr(T_b†))
  = owner.finitePrimeTerm(p^m).
```

The two traces have different operator owners. `Tr(T_b)` is the forward
`b F(b)` channel and `Tr(T_b†)` is the reverse `b F(-b)` channel. No
commutation of `J_b` through convolution is used.

The specialization
`positiveInterval_eulerLog_weighted_global_pair_traces_eq_finitePrimeTerm_pow`
uses the canonical positive-interval Yoshida source and its existing support
theorem. It keeps the source test, convolution square, support interval,
whole-line crossing pair, and finite-prime evaluation on one object.

## Proof chain

```text
compact forward trace
  = whole-line Tr(T_b)                       proof 196

compact reverse trace
  = whole-line Tr(T_b†)                      proof 197

weighted compact forward + reverse
  = selected finitePrimeTerm(p^m)            proof 192

therefore weighted whole-line pair
  = selected finitePrimeTerm(p^m).           this proof
```

## Source boundary

The next step is not available as a published source theorem. CCM24 proves
the semilocal Sonin-space transport and presents semilocal Weil positivity as
a program, not as a fixed-S trace identity:

```text
https://arxiv.org/abs/2310.18423
```

The subsequent one-prime q-series paper computes moment and Jacobi data but
does not prove a positive trace/Weil equality:

```text
https://arxiv.org/abs/2403.01247
```

Thus no semilocal positive owner is introduced here. The rejected endpoint
metric projection still has the fatal factor-two `p^2` channel recorded in
proof 042.

## Verification

The WSL source build passes with 2978 jobs. The source plus focused audits pass
with 2981 jobs. Both new declarations report only:

```text
propext
Classical.choice
Quot.sound
```
