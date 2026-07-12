# 101 Prime Nulling Versus Xi-Quotient Convergence

Date: 2026-07-12

## Continuity obstruction

Let `q` be the canonical Xi-orbit quotient inverse and let `g_A` be compact
tests converging to `q` in `L2`. For a real translation `T_a`,

```text
|<g_A,T_a g_A> - <q,T_a q>|
  <= (norm(g_A) + norm(q)) * norm(g_A-q).
```

This follows by adding and subtracting `<g_A,T_a q>` and using that translation
is unitary. Hence autocorrelation at every fixed shift is continuous under the
same strong convergence used by the cutoff argument.

If Plan 029 enforces

```text
<g_A,T_(log n) g_A> = 0
```

for all sufficiently large cutoffs, then necessarily

```text
<q,T_(log n) q> = 0.
```

Thus prime nulling cannot be added as a small correction unless the canonical
quotient inverse already has zero autocorrelation at every visible prime log.

## Fourier interpretation

The autocorrelation is the inverse Fourier transform of the critical-line
spectral density `|H|^2`. There is no structural Xi-orbit divisibility reason
forcing that inverse transform to vanish at `log(p^k)`. Exact zeros of `H` at
zeta zeros do not imply zeros of its autocorrelation at prime translations.

## Verdict

```text
finite quadratic nulling in isolation: possible
nulling while converging strongly to canonical quotient: generically obstructed
required escape: prove canonical prime-log autocorrelation zeros, or abandon
                 strong quotient approximation
Plan 029: high risk / next rejection gate
```

No Lean or empirical expansion is justified until this compatibility is
resolved.

