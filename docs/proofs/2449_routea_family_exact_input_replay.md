# 2449 - Exact stored-input replay and support-branch control

Date: 2026-10-02.

After the formal foundation passed in 2448, an exact-input inspection found
two differences between the 2445 producer and its external replay:

- The producer uses stored binary64 positions. The replay reconstructed their
  decimal display strings. Sixteen of the eighteen rows have different exact
  values under these conventions. For example, stored binary64 0.1 is not the
  exact fraction 1/10. Both values can lie in the same enclosure, so the earlier
  passing replay did not settle this input-identity issue.
- The producer artifact omitted the hash of the reused 2286 MPFR implementation.
  Its arithmetic source was therefore not completely bound by the artifact.

The exact stored-input support check found no branch mismatch on the current
540-term grid. However, the producer's use of a rounded `width * width` for
branch selection can misclassify other boundary points. At
`width = nextafter(1.0, +inf)`, the exact square exceeds its stored rounded
square. Taking the latter as the position produces an interior point, not
an exact zero. This is a regression fixture, not new owner data.

## Repairs

The independent replay now lifts each stored float directly into 80-digit
mpmath arithmetic instead of passing through its decimal string. It does
not import the MPFR evaluator.

The artifact now hashes the 2275 capture, the 2445 producer and the reused
2286 MPFR source. The replay checks all required hashes against the actual
files and rejects a missing hash, a modified source or a mismatched owner
capture hash. Its own source hash and position convention are recorded in
the replay result.

The producer decides support membership with exact fractions of the stored
width and position. For an interior point it derives the radius interval
by directed multiplication of the stored width, rather than rounding the
square first. It requires a strictly positive lower bound for q before
evaluating exp(-30/q). If the interval cannot resolve the sign near the edge,
the producer raises an explicit error instead of claiming an exact zero or
evaluating the singular division.

## Verification

Resource-managed runs in the Linux-side verification environment regenerated
the two 2445 artifacts
and then ran:

    python3 -m unittest discover -s scripts -p 'routea_family_endpoint_*selftest_2445.py'

The outputs are:

    {"status": "INDEPENDENT-MPMATH-CONTAINMENT-REPLAY", "checked_terms": 540, "failure_count": 0}
    Ran 10 tests
    OK

The tests cover the existing grid structure and containment report, direct
binary64 position identity, source/capture hash mutations, missing backend
hashes, exact support branches for all current terms, and refusal to classify
the rounded-square boundary fixture as zero.

Evidence:

- `scripts/routea_family_endpoint_certificate_2445.py`
- `scripts/routea_family_endpoint_certificate_selftest_2445.py`
- `scripts/routea_family_endpoint_independent_replay_2445.py`
- `scripts/routea_family_endpoint_independent_replay_selftest_2445.py`
- `results/2445_routea_family_endpoint_certificate.json`
- `results/2445_routea_family_endpoint_independent_replay.json`
- `results/2449_routea_family_input_validation.json`
- `build-logs/2449_family_input_replay.log`
- `build-logs/2449_family_exact_replay.log`
- `build-logs/2449_family_selftests.log`

This record refreshes the original 2445 artifacts; the original 4-test claim
is historical, and the current acceptance count is 10. Current artifact hashes
are authoritative for later import. The initial two-bug diagnosis in 2445 is
retained, but neither its former position convention nor its incomplete source
manifest is sufficient for exact stored-input acceptance.

## Scope

The result remains an external finite point-box control. High-precision
mpmath containment is not a Lean proof of MPFR transcendental rounding, and
the control does not establish continuum or quadrature bounds. Exact stored
coefficient/modulation identities and actual factor endpoint inequalities
must still be proved before the 2437/2436 Lean consumers are instantiated.
No signed selected-detector budget, producer GO or RH claim follows.
