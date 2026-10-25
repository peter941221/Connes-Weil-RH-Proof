# 3094 - Route A readback normalization and mechanism decision

The pointwise joint-symbol producer is closed by the actual negative-density
witness in record 3093. The complete `qw` readback remains uncertified. This
record adds a strict same-owner normalization check before any global
credit-versus-deficit claim.

1. Exact Fourier measure check

Let `H(xi) = routeAOrbitTransform geometry xi`, and let `F` denote the same
owner's `g.convolutionSquare`. Record 3086 identifies
`H(xi) = Fourier(g.test)(-xi/(2*pi))`. Mathlib's Schwartz Plancherel theorem
and change of variables then give the audited identities:

```text
integral |H(xi)|^2 dxi           = 2*pi * Re(F(0))
integral |H(xi)|^2/(2*pi) dxi    = Re(F(0))
Re(F(0))                       > 0
integral |H(xi)|^2 dxi          != Re(F(0))
```

The strict positivity uses the actual owner's nonzero interpolation value,
not an arbitrary substitute test. Therefore a raw inverse Fourier readback
with coefficient one is false even on this selected owner. The declared
3081 integral uses ordinary real volume and its density has no `1/(2*pi)`
factor. It cannot be accepted by an unscaled inverse-Fourier argument.

2. Complete contract review

```text
+----------------------------+-----------------------------------------------+
| Readback obligation        | Finding                                       |
+----------------------------+-----------------------------------------------+
| Same-owner source identity | Proved in 3086 and retained in 3092-3094.     |
| Fourier normalization      | Inverse reconstruction requires 1/(2*pi);     |
|                            | the coefficient-one channel is disproved.     |
| Archimedean multiplier     | No full-line same-owner readback supplied.    |
| Complete prime powers      | Poisson symbol is defined; equality with      |
|                            | the complete physical prime sum is unproved.  |
| Full-line integrability    | Credit/deficit integrability in 3081 remains  |
|                            | a premise of its contract.                    |
+----------------------------+-----------------------------------------------+
```

This check disproves the unscaled unit-multiplier reconstruction. It does
not prove `qw != routeAFrequencyEnergyIntegral` for a selected geometry:
that is a separate scalar statement requiring all multiplier channels. The
3081 record remains an uninstantiated contract, not an exact readback theorem.

3. Scoped decision

```text
actual owner + 3090-3092
        |
        v
3093: a nonzero frequency has negative density
        |
        +--> pointwise nonnegative-square producer: CLOSED
        |
        +--> correction by 1/(2*pi): negative point survives

3081 complete qw identity: NOT CERTIFIED
        |
        +--> no global credit/deficit campaign is licensed by this density
```

The local no-go does not exclude a signed integral argument. The binding RH
obligation remains the same selected detector's `qw >= 0`, preserving prime
cancellation. Any corrected frequency formulation first needs its complete
same-owner readback and integrability proof. An absolute-value prime allowance
does not discharge that signed obligation.

4. Verification

`python3 scripts/routea_local_screen_audit_3094.py` builds the affected modules,
their audits, the three boundary checks, and the existing master-exit control.
The script rejects build errors, `sorryAx`, missing named checks, and any
reported axiom set other than `[propext, Classical.choice, Quot.sound]`.
The reproducible result is `results/3094_routea_local_screen_audit.json`.
