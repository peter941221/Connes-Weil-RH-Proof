# Record 1936: first visible prime-power prefix scout

Date: 2026-09-24.

## Probe

`scripts/fourpoint_prime_prefix_determinant_1936.py` evaluates the prime-only
kernel determinant cumulatively over the visible prime-power list, using the
same kernel-form convention as record 1919 and the certified model cases from
record 1918.

On the available `c = 1.3` certified cases, the first visible prime-power
(`n = 2`) already gives a strict negative prime-only determinant. The later
visible terms preserve negativity in every tested row. Representative values:

```text
case c=1.3, delta=0.05, gamma=14.13
first prefix determinant  = -6.4102e3
full prime determinant    = -1.1241e5

case c=1.3, delta=0.05, gamma=21.02
first prefix determinant  = -3.0980e4
full prime determinant    = -4.8684e5
```

## Meaning and boundary

This is scouting evidence only; it is not an actual-owner proof and does not
change the map. It identifies the shortest plausible analytic certificate:
prove the `n = 2` prime-power contribution gives a negative determinant on
the parameterized owner, then bound the remaining visible-prime tail while
retaining the archimedean and mixed blocks. A prime-only certificate alone is
insufficient for the full determinant because the archimedean/cross blocks can
be positive.

The result is stored in
`results/1936_fourpoint_prime_prefix_determinant.json`.

Classification: NUMERIC scouting toward an explicit finite certificate;
unresolved and not promoted to a route conclusion. RH is not claimed.
