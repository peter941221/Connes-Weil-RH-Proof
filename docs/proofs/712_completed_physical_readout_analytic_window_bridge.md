# Proof 712: Completed Physical Readout from Analytic Windows

## What is established

Proof 712 composes Proof 711 with the Proof 698 dense-range cancellation
consumer:

~~~text
translated analytic-window representatives
  + Fourier/root nondegeneracy
  -> DenseRange fixedPhysicalSourceInput
  -> completed physical endpoint readout
~~~

The theorem output is the same completed-history endpoint readout shape as
Proof 698:

~~~text
exists readout,
  norm readout <= bound
  and rightLeg o endpoint
    = readout o completedRectangularBoundaryColumn steps
~~~

## Declarations

~~~text
exists_completed_readout_of_analytic_window_originalMultiplier
exists_completed_readout_of_analytic_window_finitePrimeTerm
exists_completed_readout_of_analytic_window_selectedVisiblePrime
~~~

## Boundary

This proof still consumes the completed physical boundary readout contract,
the terminal survivor identity, the joint norm bound, and the analytic-window
source hypotheses.  It does not prove those inputs, does not prove the signed
Gate 3U bound, does not prove the finite-S sign, does not prove Burnol's
identity, and does not prove _root_.RiemannHypothesis.

The value of this bridge is that the old hdense input in Proof 698 can now be
supplied by the explicit analytic-window source obligations from Proof 711.

## Verification

Verification was run in the Ubuntu-24.04 WSL2 ext4 mirror under the shared
Lake lock:

~~~text
source target:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build
    ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalReadoutAnalyticWindowBridge
  PASS: 3326/3326 jobs

audit target:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build
    ConnesWeilRH.Dev.CCM24FiniteSCompletedPhysicalReadoutAnalyticWindowBridgeAudit
  PASS: 3327/3327 jobs

aggregate:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build
    ConnesWeilRH.Source.CCM25Concrete
  PASS: 3985/3985 jobs

full repository:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build
  PASS: 4066 jobs
~~~

The import-facing audit prints exactly
[propext, Classical.choice, Quot.sound] for all three declarations.  No
sorry, admit, or user axiom was added.  The first focused source attempt
exposed a missing namespace open for juliaSurvivor; after opening the
existing CCM24FiniteSJuliaBessel namespace, the focused source, audit,
aggregate, and full builds all passed.
