# Proof 711: Fixed Physical Source Dense Range from Analytic Windows

## What is established

Proof 711 composes two already verified bridges:

~~~text
Proof 710:
  translated analytic-window representatives
    -> translated full-boundary injectivity

Proof 702:
  translated full-boundary injectivity
    -> DenseRange fixedPhysicalSourceInput
~~~

The result is a direct dense-range producer for the fixed physical source
input under the same analytic-window source obligations.

## Declarations

~~~text
fixedPhysicalSourceInput_denseRange_of_analytic_window_originalMultiplier
fixedPhysicalSourceInput_denseRange_of_analytic_window_finitePrimeTerm
fixedPhysicalSourceInput_denseRange_of_analytic_window_selectedVisiblePrime
~~~

The first declaration consumes an original-root Fourier multiplier that is
nonzero almost everywhere.  The latter two declarations use the owner-level
Proof 708 entry points: a nonzero finite-prime atom, or a selected visible
prime, plus original-root Fourier analyticity.

## Boundary

This is a dense-range bridge for the Proof 698 completed-history cancellation
input.  It still does not construct the per-vector analytic representatives,
prove original-root Fourier analyticity, prove the signed Gate 3U bound, prove
the finite-S sign, prove Burnol's identity, or prove
_root_.RiemannHypothesis.

The important narrowing is:

~~~text
translated analytic representatives + Fourier/root nondegeneracy
  -> DenseRange fixedPhysicalSourceInput
~~~

so the remaining source obligation is no longer hidden behind the older
kernel-injectivity language.

## Verification

Verification was run in the Ubuntu-24.04 WSL2 ext4 mirror under the shared
Lake lock:

~~~text
source target:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build
    ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalSourceInputAnalyticWindowBridge
  PASS: 3296/3296 jobs

audit target:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build
    ConnesWeilRH.Dev.CCM24FiniteSFixedPhysicalSourceInputAnalyticWindowBridgeAudit
  PASS: 3297/3297 jobs

aggregate:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build
    ConnesWeilRH.Source.CCM25Concrete
  PASS: 3984/3984 jobs

full repository:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build
  PASS: 4065 jobs
~~~

The import-facing audit prints exactly
[propext, Classical.choice, Quot.sound] for all three declarations.  No
sorry, admit, or user axiom was added.  The only warnings observed were
pre-existing repository/package warnings outside the new Proof 711 source.
