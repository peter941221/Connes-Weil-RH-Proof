import ConnesWeilRH.Dev.C1RouteACellIntegralCharge2675

namespace ConnesWeilRH.Dev

/- Screened exact-rational aggregate outputs, rounded outward to
   160-bit dyadic coordinates. The sum replay and familywise
   continuous containment remain separate proof obligations. -/

def record2676BaseM0AggregateReLo : ℚ :=
  (19343698897402274412078735768938152474972633481826 : ℚ) / (2 : ℚ) ^ 160
def record2676BaseM0AggregateReHi : ℚ :=
  (20916671887856089083055673867404184207429802103690 : ℚ) / (2 : ℚ) ^ 160
def record2676BaseM0AggregateImLo : ℚ :=
  (-3740081323437219887729365884504892205396943836231 : ℚ) / (2 : ℚ) ^ 160
def record2676BaseM0AggregateImHi : ℚ :=
  (2594566826983125558521629589215277950953258491520 : ℚ) / (2 : ℚ) ^ 160
def record2676BaseM0Aggregate : ComplexRect2427 :=
  ComplexRect2427.mk (record2676BaseM0AggregateReLo : ℝ)
    (record2676BaseM0AggregateReHi : ℝ)
    (record2676BaseM0AggregateImLo : ℝ)
    (record2676BaseM0AggregateImHi : ℝ)

theorem record2676BaseM0AggregateSubset :
    record2675BaseM0Rect.reLo ≤ record2676BaseM0Aggregate.reLo ∧
      record2676BaseM0Aggregate.reHi ≤ record2675BaseM0Rect.reHi ∧
      record2675BaseM0Rect.imLo ≤ record2676BaseM0Aggregate.imLo ∧
      record2676BaseM0Aggregate.imHi ≤ record2675BaseM0Rect.imHi := by
  norm_num [record2676BaseM0Aggregate, record2675BaseM0Rect,
    record2676BaseM0AggregateReLo,
    record2676BaseM0AggregateReHi,
    record2676BaseM0AggregateImLo,
    record2676BaseM0AggregateImHi,
    binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674,
    binary64Sign2674]

def record2676BaseD2AggregateReLo : ℚ :=
  (-47464556245325552428197225105561872689682520728007495 : ℚ) / (2 : ℚ) ^ 160
def record2676BaseD2AggregateReHi : ℚ :=
  (-43899376566440535064027484724015857171497370156773836 : ℚ) / (2 : ℚ) ^ 160
def record2676BaseD2AggregateImLo : ℚ :=
  (-4517073618802917211090333977032091839667682765632517 : ℚ) / (2 : ℚ) ^ 160
def record2676BaseD2AggregateImHi : ℚ :=
  (9425977674707179870617052766001813235387076004792076 : ℚ) / (2 : ℚ) ^ 160
def record2676BaseD2Aggregate : ComplexRect2427 :=
  ComplexRect2427.mk (record2676BaseD2AggregateReLo : ℝ)
    (record2676BaseD2AggregateReHi : ℝ)
    (record2676BaseD2AggregateImLo : ℝ)
    (record2676BaseD2AggregateImHi : ℝ)

theorem record2676BaseD2AggregateSubset :
    record2675BaseD2Rect.reLo ≤ record2676BaseD2Aggregate.reLo ∧
      record2676BaseD2Aggregate.reHi ≤ record2675BaseD2Rect.reHi ∧
      record2675BaseD2Rect.imLo ≤ record2676BaseD2Aggregate.imLo ∧
      record2676BaseD2Aggregate.imHi ≤ record2675BaseD2Rect.imHi := by
  norm_num [record2676BaseD2Aggregate, record2675BaseD2Rect,
    record2676BaseD2AggregateReLo,
    record2676BaseD2AggregateReHi,
    record2676BaseD2AggregateImLo,
    record2676BaseD2AggregateImHi,
    binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674,
    binary64Sign2674]

def record2676CorrectionM0AggregateReLo : ℚ :=
  (-4900871782973926782359795333268889843129773498528350 : ℚ) / (2 : ℚ) ^ 160
def record2676CorrectionM0AggregateReHi : ℚ :=
  (4886677035809477431091142008219183062306489806802099 : ℚ) / (2 : ℚ) ^ 160
def record2676CorrectionM0AggregateImLo : ℚ :=
  (-1561874077279933949026598956654569613551601251427336 : ℚ) / (2 : ℚ) ^ 160
def record2676CorrectionM0AggregateImHi : ℚ :=
  (1665142873519930843907211535078782358298141117692664 : ℚ) / (2 : ℚ) ^ 160
def record2676CorrectionM0Aggregate : ComplexRect2427 :=
  ComplexRect2427.mk (record2676CorrectionM0AggregateReLo : ℝ)
    (record2676CorrectionM0AggregateReHi : ℝ)
    (record2676CorrectionM0AggregateImLo : ℝ)
    (record2676CorrectionM0AggregateImHi : ℝ)

theorem record2676CorrectionM0AggregateSubset :
    record2675CorrectionM0Rect.reLo ≤ record2676CorrectionM0Aggregate.reLo ∧
      record2676CorrectionM0Aggregate.reHi ≤ record2675CorrectionM0Rect.reHi ∧
      record2675CorrectionM0Rect.imLo ≤ record2676CorrectionM0Aggregate.imLo ∧
      record2676CorrectionM0Aggregate.imHi ≤ record2675CorrectionM0Rect.imHi := by
  norm_num [record2676CorrectionM0Aggregate, record2675CorrectionM0Rect,
    record2676CorrectionM0AggregateReLo,
    record2676CorrectionM0AggregateReHi,
    record2676CorrectionM0AggregateImLo,
    record2676CorrectionM0AggregateImHi,
    binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674,
    binary64Sign2674]

def record2676CorrectionD2AggregateReLo : ℚ :=
  (-7654390162303155866965477025339160957365455657005749536 : ℚ) / (2 : ℚ) ^ 160
def record2676CorrectionD2AggregateReHi : ℚ :=
  (7650077471848228178032420529128395617464901680377503543 : ℚ) / (2 : ℚ) ^ 160
def record2676CorrectionD2AggregateImLo : ℚ :=
  (-2614439383640598388131277741667519278736060236476337295 : ℚ) / (2 : ℚ) ^ 160
def record2676CorrectionD2AggregateImHi : ℚ :=
  (2448438810872432719688938986745198890719688816346807969 : ℚ) / (2 : ℚ) ^ 160
def record2676CorrectionD2Aggregate : ComplexRect2427 :=
  ComplexRect2427.mk (record2676CorrectionD2AggregateReLo : ℝ)
    (record2676CorrectionD2AggregateReHi : ℝ)
    (record2676CorrectionD2AggregateImLo : ℝ)
    (record2676CorrectionD2AggregateImHi : ℝ)

theorem record2676CorrectionD2AggregateSubset :
    record2675CorrectionD2Rect.reLo ≤ record2676CorrectionD2Aggregate.reLo ∧
      record2676CorrectionD2Aggregate.reHi ≤ record2675CorrectionD2Rect.reHi ∧
      record2675CorrectionD2Rect.imLo ≤ record2676CorrectionD2Aggregate.imLo ∧
      record2676CorrectionD2Aggregate.imHi ≤ record2675CorrectionD2Rect.imHi := by
  norm_num [record2676CorrectionD2Aggregate, record2675CorrectionD2Rect,
    record2676CorrectionD2AggregateReLo,
    record2676CorrectionD2AggregateReHi,
    record2676CorrectionD2AggregateImLo,
    record2676CorrectionD2AggregateImHi,
    binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674,
    binary64Sign2674]

end ConnesWeilRH.Dev
