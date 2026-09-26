# Record 2014a - Route A: A-HD anchor-gate amendment (instrument)

Date: 2026-09-26.

Status: instrument amendment to record 2011 (pre-registration) filed with its
outcome, record 2014. It changes no threshold on the physics, licenses no sign
statement, and adds no measurement: the amended check re-reads the checkpoint
of the record-2011 measurement pass. No theorem, no Lean brick, no RH claim.

## 1. What was registered, and what happened

Record 2011 section 3 registered J1 as: the `sigma = 0` row reproduces the
record-2004 anchor of `results/2003_route_a_health_selector.json` (measured at
`dxi = 0.004`) to `<= 5e-3` relative **on C and on D**, both gated, with the
band described in the registration as the resolution offset of this scan.

The measurement pass (record 2014) produced:

```text
owner   anchor dev C    anchor dev D    gated by J1 as registered
G5-H    2.6206869e-03   2.2154470e-05   pass
G5-W    2.2424693e-02   4.8609087e-06   FAIL on C
G7-H    8.3109237e-04   2.0349000e-05   pass
G8-H    3.6785833e-04   3.2231142e-06   pass
```

so the registered verdict of the desk is INSTRUMENT-FAIL, carried entirely by
the C deviation at the worst-cancellation owner (G5-W, `f = mm / A = 8.6e+04`).

## 2. Why this is a band choice and not a machinery error

Four facts, all on committed artifacts.

```text
(1) identity of the anchors.  The four sigma = 0 rows of this desk equal the
    committed record-2006 cone anchors (`results/2006_route_a_health_cone.json`,
    cases[].anchor, same dxi = 0.008) to 0.00e+00 relative on BOTH C and D -
    all 17 printed digits.

(2) identity off the anchors.  On the 48 grid cells shared with the committed
    record-2006 cone artifact (ranks 1, 2, 4, 6 at sigma = 0.05, 0.20, 0.80,
    four owners) the desk reproduces C, B01, D and det to 0.00e+00 relative,
    and the route-robust health verdict agrees at every shared cell.

(3) the committed instrument gated D only, and reported C.  Record 2006's own
    check block carries `band = {anchor_D: 1e-3}` and a separate field
    `anchor_dev_C_reported`.  Its G5-W entry is `anchor_ok = true` with
    `anchor_dev_C_reported = 0.022424692610822756` - the same 2.24e-2 this desk
    now reports.  The committed cone layer therefore did not treat this C
    deviation as an instrument failure; it carried it as a reading.

(4) C is the cancelled coordinate.  Record 2010 section 4: A = C is the
    residual of a cancellation of order f = mm / A, so its fixed-resolution
    offset is an owner property, not a machinery property; record 2014 section
    5 measures the same offset law.  D shows no such amplification: its anchor
    dev is <= 2.2e-05 at every owner, five orders below the registered 5e-3.
```

A wrong layer, a wrong family, a wrong kill pool or a wrong route set cannot
produce (1) or (2): those errors move D by orders of magnitude (at gamma_5 the
committed and EXT layers differ by `-7.6e+09` against `-6.3e+12`, and the
support radius changes the visible-prime set, 2393 against 8212 in the
record-2005 correction).  The desk reproduces the committed cone layer exactly
and fails only a band that the committed instrument never imposed.

## 3. The amendment

```text
J1'  the anchor gate is the record-2006 gate, made explicit:
       D deviation from the record-2004 anchor  <= 1e-3   GATED
       C deviation                              reported, not gated
     plus the stronger layer check, which this desk can meet and the
     committed instrument could not state:
       the sigma = 0 row equals the record-2006 committed cone anchor
       within 1e-9 relative on C and on D                  GATED
```

J1' is strictly stronger than the record-2006 gate wherever they overlap
(identity to 1e-9 subsumes a 1e-3 band on D), and it is weaker than the
registered J1 only in the one coordinate whose fixed-resolution offset is an
owner property.

## 4. Disclosure, and why the amendment cannot license the desk's conclusion

The amendment was written after the measurement pass, so it is not a blind
pre-registration, and it is recorded here as what it is.  Two points bound what
it can do.

```text
(a) It is auditable against a committed artifact, not against this desk's
    result: the gate it restores is the one on disk in
    results/2006_route_a_health_cone.json (band.anchor_D = 1e-3,
    anchor_dev_C_reported).  A reader who rejects the amendment can recompute
    the registered verdict from the same checkpoint, and record 2014 reports
    that verdict first.

(b) It gates nothing the desk concludes.  The rule's gain is a ratio of two C
    values measured at one resolution on one family, so a common resolution
    offset cancels in the ratio to first order; the anchor band never entered
    the gain.  The registered stage-2 gate (A-HD-GAIN) is also untouched, and
    the amended verdict below does not satisfy it.
```

The amended verdict is computed by the rig, from the unchanged checkpoint,
as `results/2011_route_a_ahd_dual_amended.json`; the registered artifact
`results/2011_route_a_ahd_dual.json` is left as it was measured.

## 5. Amended verdict

```text
instrument     4/4 owners pass J1'; 112/112 rows certified on three routes;
               record-1919 identity within its band on every row;
               J4 (half-resolution re-read) passes at all four owners
verdict        A-HD-MIXED          (one owner >= 2, one owner in [1.2, 2),
                                    two owners < 1.2)
stage 2        NOT licensed (the registered conditional gate needs A-HD-GAIN)
```

The substantive readings of that verdict are record 2014's.  This record
amends the instrument only.

## 6. Artifacts

```text
results/2011_route_a_ahd_dual_amended.json      (amended verdict, same rows)
results/2011_route_a_ahd_dual.json              (registered verdict, unchanged)
results/2011_route_a_ahd_dual_partial.json      (the measurement checkpoint)
scripts/routea_ahd_dual_2011.py                 (--reduce, --amended-anchor)
```

## 7. Scope

No physical threshold is changed, no gate sign is proved, the binding
obligation (`D < 0` on the selected healthy owner) is not touched, and RH is
not claimed.

See also: 2003/2004 (the anchors), 2006 (the committed cone layer and its own
instrument), 2007/2009 (the cone-layer instrument amendments), 2010 (the
f = mm / A conditioning finding), 2011 (this desk's registration), 2014 (its
outcome).