# 2792 known-error headroom above repaired-owner charge

The producer's existing `knownError2109` constant is strictly greater than `10000`. Consequently, any repaired-owner total already proved below `10000` is automatically below `knownError2109`.

The remaining bridge is the owner identity identifying `chargeRest` with that repaired-owner total; this theorem does not assert that identity.
