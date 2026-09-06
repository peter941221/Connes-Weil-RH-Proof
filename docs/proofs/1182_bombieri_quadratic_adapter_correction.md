# 1182 — Corrected status and adapter for the Bombieri quadratic socket

Date: 2026-09-06

## Classification correction

The contradiction guard from record 1181 is conditional on healthy detector
data.  It does not by itself kill the producer route: every successful P2
producer must likewise imply `qw >= 0`, which contradicts the detector's
formal `qw < 0` and is precisely the desired `SourceRH` exit.

## Formal adapter

`BombieriQuadraticP2BridgeData.of_bombieriP2BridgeData` is an axiom-clean
adapter from the existing Line-B finite eigen/mass contract.  It uses
`lambda_mass_eq_bombieriHMatrix_quadraticForm`, applies `Complex.re`, and
rewrites the `qw_eq_mass` field to obtain the direct quadratic equality.
Therefore the direct form is a valid alternate interface, not a stored
positivity conclusion.  Its per-zero same-owner producer remains open.

The standalone probe elaborated successfully.  A focused source/audit rebuild
is the next acceptance gate; no RH claim is made.
