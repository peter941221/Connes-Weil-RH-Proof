# 01 - Reproducible finite-band Gate 3U deliverable (route-A, axiom-clean)

Status: closed and verified for the finite band. RH NOT claimed; the infinite-carrier
Gate stays open (see 02_FRONTIER.md).

## 1. What this is

The constructible, axiom-clean Gate-3U closure is the finite/decaying band of the route
carrier. The theorem

    bandTerminalGate
      (ConnesWeilRH/Dev/RouteATailBandBound.lean:115)

bounds, on ANY finite Hilbert band `b` (`[Fintype b]`) of the real route carrier
`sourceSoninCarrier lambda`, the real-part ordinary trace of the actual library tail
operator by

    |Re Tr_b(Tail)|  <=  (card rho) * || Tail ||
    || Tail ||       <=  C0 * exp(-B/4) * prod_p quarter-mass       (TailBound:751)
    ---------------------------------------------------------------
    |Re Tr_b(Tail)|  <=  (card rho) * C0 * exp(-B/4) * prod_p         (Gate)

assembled by the support-tail split, consumed through `canonicalRealGate3UAt_of_tailNormBound`.

## 2. Files / provenance

    ConnesWeilRH/Dev/RouteATailBandBound.lean      finite Gate (commits 863e41b d677fc2 7a53c11)
    ConnesWeilRH/Dev/EBandFactorSharpProbe.lean   new, factor norm <= 1, verified
    ConnesWeilRH/Dev/CCM24JdaggerOrthogonality.lean  NEW this round (see 4)

## 3. How to reproduce (WSL2)

Windows repo = source of truth; WSL mirror = verification only. Never edit/git in WSL.

    rsync -a --exclude=.git --exclude=.lake <win>/ /tmp/<fresh>/     # fresh verify dir
    cd /tmp/<fresh>
    flock -w 1800 /tmp/connes-weil-lake.lock lake env lean \
        ConnesWeilRH/Dev/CCM24JdaggerOrthogonality.lean             # must EXIT=0
    # focused axiom audit on the target declaration
    flock -w 1800 /tmp/connes-weil-lake.lock lake build \
        ConnesWeilRH.Dev.CCM24JdaggerOrthogonality                  # produce .olean
    # then in a lean buffer: #print axioms ...
    #   => [propext, Classical.choice, Quot.sound]

## 4. New lemma (this round)

`ConnesWeilRH/Dev/CCM24JdaggerOrthogonality.lean`:

    inclusionAdjoint_comp_band_eq_zero :
        (sourceInclusion lambda)^dag oL sourceBandProjection lambda = 0
    dagger_comp_forwardBandCoframe_eq_zero :
        (sourceInclusion lambda)^dag oL sourceActualBandForwardCoframe lambda family = 0
    sonin_comp_forwardBandCoframe_eq_zero :
        sourceSoninProjection lambda oL sourceActualBandForwardCoframe lambda family = 0

Axioms all three: [propext, Classical.choice, Quot.sound], 0 sorry (byte-verified 2026-08-10).
This proves the NECESSARY condition of the infinite Gate in its projector-free form
(docs/931) by pure Leibniz algebra. It is NOT the full operator equality, so it does not
close the infinite Gate.

## 5. Deliverable table

| item | file | axioms | status |
|------|------|--------|--------|
| finite Gate | RouteATailBandBound | [pe, CC, Qs] | closed, verified |
| tail bound | RenewalTailBound:761 | [pe, CC, Qs] | closed |
| prolate factor <= 1 | EBandFactorSharpProbe | [pe, CC, Qs] | closed (improves <=2) |
| J- and P-dual orthogonality | CCM24JdaggerOrthogonality | [pe, CC, Qs] | new, verified |
| infinite Gate | 02_FRONTIER (Wall 1) | -- | OPEN |

RH NOT claimed by any item here.
