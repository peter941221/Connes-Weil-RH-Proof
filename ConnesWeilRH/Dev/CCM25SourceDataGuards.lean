/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.CC20YoshidaConstruction

/-!
# CCM25 source-data rejection guards (archived)

The former guard `not_nonempty_concreteSourceWeilFormData` asserted that the
old `SourceWeilFormData` (whose `finitePrime.exactSupport` carried a global
`∀ F : A.Test` POST-witness) was uninhabitable over the concrete algebra.  Since
the S2 per-common restructure (`docs/proofs/833/834`) replaced that ∀F backend
with `PerCommonSourceFinitePrimeSupport` scoped to a single `common.sourceTest`,
the concrete type is no longer forced empty by the zero element, so that guard
became obsolete and is now archived.  The structural verdict that motivated it
is preserved self-contained in `Dev/CarrierReplacementFeasibilityProbe`.
-/

namespace ConnesWeilRH
namespace Dev

end Dev
end ConnesWeilRH
