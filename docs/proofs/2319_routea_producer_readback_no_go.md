# 2319 — P-only producer readback and cutoff-growth obstruction

Date: 2026-10-01

Status: `P-ONLY-DIRECT-DETECTOR-IDENTIFICATION-NO-GO`.

Consumer: the same-owner healthy `CompactLog` route

```text
selected detector g -> prove qw(g) >= 0 -> SourceRH -> Mathlib RH
```

Owner: the exact four-point annihilator and the selected negative-orbit
Hermitian square. The record does not replace either owner in the live route.

## Result

The four-point multiplier in `C1FourPointSpectralPrefixTransport` is

```text
P_rho(s) = product over the four centered orbit nodes (node - s).
```

Exact rational arithmetic gives

```text
P_rho(rho - 1/2) = 0
P_rho((1 - conjugate(rho)) - 1/2) = 0
```

Therefore a P-only square has zero Hermitian readback at the marked pair.
The selected detector instead has raw values `1` and `-1`, so its selected
square has value `-1` at the marked centered point and the pair contribution
is `-2`.

This is not a numerical roundoff issue. The two transform shapes have different
exact values at the same marked point. A P-only tail estimate cannot supply the
selected detector's negative prefix by direct object identification.

The orbit-annihilation fact is already formal in record 1914; no novelty is
claimed for it. This record applies that fact to the proposed 2318 producer
readback and proves the incompatible transform values in a focused module.

The exact source check also confirms that the committed numerical screen uses
the same four orbit roots, the `-2*pi*i*xi` transform argument, the half-density
shift, and the squared annihilator product. The check does not assert that the
captured numerical `rho` is a source zero. It also does not prove that the
sampled functional equals the full-line Weil gate of the P-only inverse. The
Fourier/physical-kernel conversion, exact interpolation, and complete-owner
transfer are still separate obligations.

The record-2249 enclosure uses the legacy 52-prime-power kernel, while the
record-2308 weight certificate uses the 41136-prime-power convention. These
certificates retain their own scopes. Their coefficient hashes alone do not
bound a change of kernel or justify applying the old enclosure to the new
functional. This record establishes no lower or upper bound for that change.

## Growth check

For a fixed multiplier coefficient `C`, the geometric shell tail has the form

```text
T_N = 4 * C * (3/4)^N.
```

If the owner-dependent coefficient grows as `(4/3)^N`, then

```text
4 * [C * (4/3)^N] * (3/4)^N = 4 * C.
```

The displayed coefficient-growth sequence is an exact algebra control, not a
measured growth law for the actual owner. Geometric decay alone therefore
does not prove that increasing the cutoff improves `tail / marked gain`.

For the P-only shape the marked-pair gain is exactly zero for every choice of
base/correction transform, hence also for every cutoff-dependent choice. A
nonnegative tail cannot be strictly smaller than that gain. The actual-owner
ratio `C_N / gain_N` is NOT instantiated by this run; the sampled negative
functional magnitude is not substituted for the marked spectral gain.

## Evidence

- Lean target identity: `ConnesWeilRH/Dev/C1FourPointSpectralPrefixTransport.lean`.
- Readback module: `ConnesWeilRH/Dev/C1RouteAProducerReadback.lean`.
- Paired audit: `ConnesWeilRH/Dev/C1RouteAProducerReadbackAudit.lean`.
- Reproducible source check: `scripts/routea_producer_readback_2319.py`.
- Self-test: `scripts/routea_producer_readback_selftest_2319.py`.
- Artifact: `results/2319_producer_readback.json`.

The first import-wide Lean build encountered existing errors in
`C1HealthyYoshidaSpectralNegativity` at lines 371 and 385; the offending source
hash matches between Windows and the mirror. No unrelated source was edited.
The focused module instead imports the healthy detector and selected-owner
definition directly and compares transform functions without importing the
later spectral-negativity consumer. The independent readback build passed;
the final acceptance checks are:

```text
+----------------------+-----------------------------------------------+
| check                | result                                        |
+----------------------+-----------------------------------------------+
| focused module/audit | Build completed successfully (3627 jobs)      |
| focused errors       | 0; no new-source warnings; no sorryAx          |
| audited leaves       | 12; [propext, Classical.choice, Quot.sound]    |
| root control         | Build completed successfully (4148 jobs)      |
| root errors          | 0                                             |
| WSL exact self-tests | 4 passed                                      |
| platform replay      | Windows/WSL artifact bytes identical          |
+----------------------+-----------------------------------------------+
```

Logs: `build_2319_readback_final.log`, `build_2319_root_control.log`,
`2319_exact_selftest_snapshot.log`, `2319_exact_readback_snapshot.log`.
The root control does not certify every optional development leaf: the first
import-wide failure above is retained on record. Missing historical numeric
scripts in the build mirror were not treated as a mathematical failure; the
source check was replayed in a Linux-side snapshot of its explicit inputs.
The first platform comparison exposed CRLF versus LF output bytes; the
instrument now writes LF explicitly, and the rerun is bitwise identical.

## Decision

Do not continue with a P-only auxiliary tail certificate as if it proved the
selected detector sign. The next binding task is the actual selected-square
physical-kernel readback, retaining its nonzero marked pair, followed by a
joint signed margin on that same object. An auxiliary P-only term can be used
only through a proved scalar transfer with all mixed terms and errors priced,
not through equality with the detector. That transfer is not supplied here.

The nonzero four-point span is archival context, not a reopened campaign:
the map-103 family remains `DEAD_ON_CURRENT_FAMILY`. No fixed-lambda or
four-point gate work is authorized by this diagnostic.

No producer GO, no gate sign change, and no RH claim.
