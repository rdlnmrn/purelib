import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.SquaredCylinderConcentration
import FiniteMeasure.ZeroWeight
import FiniteMeasure.ThresholdEnclosure

/-!
# Threshold stability for squared-sensitive finite CCL probes

Discontinuous threshold events cannot be controlled from a shrinking metric
bound alone when a value may lie on the threshold.  An explicit positive
rational witness margin repairs this constructively.  Squared-probe
sensitivity then requires a finite request at `margin^2`; after that request
every compatible realization has exactly the witness's Boolean
classification, so all resulting finite probabilities are equal.
-/

namespace CCL.FiniteMeasure

private theorem separation_lt_of_sq_lt_sq
    {left right margin : Coordinate} (marginPositive : 0 < margin)
    (small : _root_.FiniteMeasure.rationalSeparation left right ^ 2 <
      margin ^ 2) :
    _root_.FiniteMeasure.rationalSeparation left right < margin := by
  rcases lt_trichotomy
      (_root_.FiniteMeasure.rationalSeparation left right) margin with
    less | equal | greater
  · exact less
  · subst margin
    exact (lt_irrefl _ small).elim
  · have squareOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      marginPositive.le greater.le 2
    exact ((not_lt_of_ge squareOrder) small).elim

private theorem atLeastDecision_eq_of_margin
    {value witness threshold margin : Coordinate}
    (marginPositive : 0 < margin)
    (close : _root_.FiniteMeasure.rationalSeparation value witness < margin)
    (separated : threshold + margin ≤ witness ∨
      witness + margin ≤ threshold) :
    decide (threshold ≤ value) = decide (threshold ≤ witness) := by
  have valueMinusWitnessSmall : value - witness < margin :=
    (le_max_left (value - witness) (witness - value)).trans_lt close
  have witnessMinusValueSmall : witness - value < margin :=
    (le_max_right (value - witness) (witness - value)).trans_lt close
  rcases separated with above | below
  · have witnessInside : threshold ≤ witness := by
      calc
        threshold ≤ threshold + margin :=
          le_add_of_nonneg_right marginPositive.le
        _ ≤ witness := above
    have witnessLtValuePlusMargin : witness < value + margin := by
      have moved := RFAP.ConstructiveFraction.add_lt_add_right_direct
        witnessMinusValueSmall value
      calc
        witness = (witness - value) + value := by ring1
        _ < margin + value := moved
        _ = value + margin := RFAP.ConstructiveFraction.add_comm _ _
    have thresholdMarginLt : threshold + margin < value + margin :=
      above.trans_lt witnessLtValuePlusMargin
    have valueInside : threshold ≤ value :=
      (RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
        thresholdMarginLt).le
    rw [decide_eq_true_eq.mpr valueInside,
      decide_eq_true_eq.mpr witnessInside]
  · have valueLtWitnessPlusMargin : value < witness + margin := by
      have moved := RFAP.ConstructiveFraction.add_lt_add_right_direct
        valueMinusWitnessSmall witness
      calc
        value = (value - witness) + witness := by ring1
        _ < margin + witness := moved
        _ = witness + margin := RFAP.ConstructiveFraction.add_comm _ _
    have valueBelow : value < threshold :=
      valueLtWitnessPlusMargin.trans_le below
    have witnessLtWitnessPlusMargin : witness < witness + margin := by
      have moved :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct marginPositive witness
      simpa only [add_zero] using moved
    have witnessBelow : witness < threshold :=
      witnessLtWitnessPlusMargin.trans_le below
    rw [decide_eq_false_iff_not.mpr (not_le_of_gt valueBelow),
      decide_eq_false_iff_not.mpr (not_le_of_gt witnessBelow)]

/-- A squared-sensitive probe has the same lower-threshold classification at
a canonical cylinder witness and any realization once the squared budget is
strictly below the displayed margin square. -/
theorem realizedSquaredProbe_atLeastDecision_eq_of_margin
    {blocks : List Block} {witness point : Proj}
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (pointRealizes : CCL.Cylinder.Realizes blocks point)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : threshold + margin ≤ probe witness ∨
      probe witness + margin ≤ threshold)
    (budgetSmall : factor * cylinderSpread blocks < margin ^ 2) :
    decide (threshold ≤ probe point) =
      decide (threshold ≤ probe witness) := by
  have squareSmall := (realized_probe_separation_sq_le pointRealizes
    witnessRealizes probe factor factorNonnegative sensitive).trans_lt
      budgetSmall
  exact atLeastDecision_eq_of_margin marginPositive
    (separation_lt_of_sq_lt_sq marginPositive squareSmall) separated

/-- Projectively rescaled encoder traces have the same margin-stable
threshold classification. -/
theorem projectiveRealizedSquaredProbe_atLeastDecision_eq_of_margin
    {blocks : List Block} {witness point : Proj}
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (pointRealizes : CCL.Cylinder.ProjectiveRealizes blocks point)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : threshold + margin ≤ probe witness ∨
      probe witness + margin ≤ threshold)
    (budgetSmall : factor * cylinderSpread blocks < margin ^ 2) :
    decide (threshold ≤ probe point) =
      decide (threshold ≤ probe witness) := by
  have squareSmall :=
    (projectiveRealized_probe_separation_sq_le pointRealizes witnessRealizes
      probe factor factorNonnegative sensitive).trans_lt budgetSmall
  exact atLeastDecision_eq_of_margin marginPositive
    (separation_lt_of_sq_lt_sq marginPositive squareSmall) separated

/-- Sufficient block count for resolving a squared-sensitive threshold event
with a displayed positive rational margin. -/
def requiredSquaredThresholdBlockCount
    (margin factor : Coordinate) : Nat :=
  requiredSquaredVarianceBlockCount (margin ^ 2) factor

/-- Any two canonical realization families of a heterogeneous finite prefix
table have exactly the same threshold probability once every row meets the
computed margin request. -/
theorem prefixFamilySquaredProbe_thresholdProbabilities_eq_of_margin
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe atom.item.witness ∨
        probe atom.item.witness + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredThresholdBlockCount margin factor ≤
        atom.item.blocks.length)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun certificate =>
          probe (leftPoints certificate)) =
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun certificate =>
          probe (rightPoints certificate)) := by
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold _root_.FiniteMeasure.atLeastEvent
  have budgetSmall :=
    scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (margin ^ 2) factor
      (RFAP.ConstructiveFraction.pow_pos_direct marginPositive 2)
      factorPositive (enough atom member)
  have leftEqual := realizedSquaredProbe_atLeastDecision_eq_of_margin
    atom.item.witnessRealizes (leftRealizes atom member)
    probe factor factorPositive.le sensitive threshold margin marginPositive
    (separated atom member) budgetSmall
  have rightEqual := realizedSquaredProbe_atLeastDecision_eq_of_margin
    atom.item.witnessRealizes (rightRealizes atom member)
    probe factor factorPositive.le sensitive threshold margin marginPositive
    (separated atom member) budgetSmall
  exact leftEqual.trans rightEqual.symm

/-- Projectively rescaled finite prefix tables obey the same exact threshold
probability theorem. -/
theorem projectivePrefixFamilySquaredProbe_thresholdProbabilities_eq_of_margin
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedProjectivePrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe atom.item.witness ∨
        probe atom.item.witness + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredThresholdBlockCount margin factor ≤
        atom.item.blocks.length)
    (leftPoints rightPoints : CompletedProjectivePrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes atom.item.blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes atom.item.blocks
        (rightPoints atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun certificate =>
          probe (leftPoints certificate)) =
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun certificate =>
          probe (rightPoints certificate)) := by
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold _root_.FiniteMeasure.atLeastEvent
  have budgetSmall :=
    scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (margin ^ 2) factor
      (RFAP.ConstructiveFraction.pow_pos_direct marginPositive 2)
      factorPositive (enough atom member)
  have leftEqual :=
    projectiveRealizedSquaredProbe_atLeastDecision_eq_of_margin
      atom.item.witnessRealizes (leftRealizes atom member)
      probe factor factorPositive.le sensitive threshold margin marginPositive
      (separated atom member) budgetSmall
  have rightEqual :=
    projectiveRealizedSquaredProbe_atLeastDecision_eq_of_margin
      atom.item.witnessRealizes (rightRealizes atom member)
      probe factor factorPositive.le sensitive threshold margin marginPositive
      (separated atom member) budgetSmall
  exact leftEqual.trans rightEqual.symm

namespace PrefixFamilyProcess

/-- One computed `margin^2` request makes every two compatible realization
families have exactly the same finite threshold probability. -/
theorem request_squaredProbeThreshold_probabilities_eq {index : Type}
    (process : PrefixFamilyProcess index)
    (distribution : _root_.FiniteMeasure.Distribution index)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State)
    (leftPoints rightPoints : index → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          (process.request state
            (requiredSquaredThresholdBlockCount margin factor)) atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          (process.request state
            (requiredSquaredThresholdBlockCount margin factor)) atom.item)
        (rightPoints atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          probe (leftPoints item)) =
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          probe (rightPoints item)) := by
  let requested := process.request state
    (requiredSquaredThresholdBlockCount margin factor)
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold _root_.FiniteMeasure.atLeastEvent
  have budgetSmall :=
    scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (margin ^ 2) factor
      (RFAP.ConstructiveFraction.pow_pos_direct marginPositive 2)
      factorPositive
      (process.request_length state
        (requiredSquaredThresholdBlockCount margin factor) atom.item)
  have leftEqual := realizedSquaredProbe_atLeastDecision_eq_of_margin
    (process.realizes requested atom.item) (leftRealizes atom member)
    probe factor factorPositive.le sensitive threshold margin marginPositive
    (separated atom member) budgetSmall
  have rightEqual := realizedSquaredProbe_atLeastDecision_eq_of_margin
    (process.realizes requested atom.item) (rightRealizes atom member)
    probe factor factorPositive.le sensitive threshold margin marginPositive
    (separated atom member) budgetSmall
  exact leftEqual.trans rightEqual.symm

end PrefixFamilyProcess

/-! ## Concrete finite encoder-table specialization -/

/-- Actual encoder outputs inherit exact threshold-probability stability
relative to margins stated on the original affine Gaussian inputs. -/
theorem encodedSquaredProbe_thresholdProbabilities_eq_of_margin {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤
          probe (CCL.Proj.affine (fraction atom.item).value) ∨
        probe (CCL.Proj.affine (fraction atom.item).value) + margin ≤
          threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredThresholdBlockCount margin factor ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (leftPoints rightPoints : index → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (rightPoints atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          probe (leftPoints item)) =
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          probe (rightPoints item)) := by
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold _root_.FiniteMeasure.atLeastEvent
  let encoding := CCL.Encoder.encodeBlocks (fraction atom.item)
    (numeratorNonzero atom.item)
  have witnessEqual : probe encoding.point =
      probe (CCL.Proj.affine (fraction atom.item).value) :=
    squaredSensitive_probe_eq_of_projectiveEquivalent probe factor sensitive
      encoding.realizes.valid
      (CCL.Chordal.Proj.affine_hasNonzeroCoordinate
        (fraction atom.item).value)
      encoding.reconstruct
  have witnessSeparated : threshold + margin ≤ probe encoding.point ∨
      probe encoding.point + margin ≤ threshold := by
    rw [witnessEqual]
    exact separated atom member
  have budgetSmall :=
    scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (margin ^ 2) factor
      (RFAP.ConstructiveFraction.pow_pos_direct marginPositive 2)
      factorPositive (enough atom member)
  have leftEqual :=
    projectiveRealizedSquaredProbe_atLeastDecision_eq_of_margin
      encoding.realizes (leftRealizes atom member)
      probe factor factorPositive.le sensitive threshold margin marginPositive
      witnessSeparated budgetSmall
  have rightEqual :=
    projectiveRealizedSquaredProbe_atLeastDecision_eq_of_margin
      encoding.realizes (rightRealizes atom member)
      probe factor factorPositive.le sensitive threshold margin marginPositive
      witnessSeparated budgetSmall
  exact leftEqual.trans rightEqual.symm

/-- Under the same finite margin request, the threshold probability of any
compatible realization family equals the exact threshold probability of the
original affine Gaussian inputs. -/
theorem encodedSquaredProbe_thresholdProbability_eq_values_of_margin
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤
          probe (CCL.Proj.affine (fraction atom.item).value) ∨
        probe (CCL.Proj.affine (fraction atom.item).value) + margin ≤
          threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredThresholdBlockCount margin factor ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          probe (points item)) =
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          probe (CCL.Proj.affine (fraction item).value)) := by
  let encodedPoints : index → Proj := fun item =>
    (CCL.Encoder.encodeBlocks (fraction item)
      (numeratorNonzero item)).point
  have compatibleEquality :=
    encodedSquaredProbe_thresholdProbabilities_eq_of_margin distribution
      fraction numeratorNonzero probe factor factorPositive sensitive
      threshold margin marginPositive separated enough points encodedPoints
      pointsRealize (by
        intro atom member
        exact CCL.Encoder.encodeBlocks_realizes
          (fraction atom.item) (numeratorNonzero atom.item))
  calc
    distribution.probability
          (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
            probe (points item)) =
        distribution.probability
          (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
            probe (encodedPoints item)) := compatibleEquality
    _ = distribution.probability
          (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
            probe (CCL.Proj.affine (fraction item).value)) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      apply Or.inr
      unfold _root_.FiniteMeasure.atLeastEvent
      change decide (threshold ≤ probe (encodedPoints atom.item)) =
        decide (threshold ≤
          probe (CCL.Proj.affine (fraction atom.item).value))
      have probeEqual : probe (encodedPoints atom.item) =
          probe (CCL.Proj.affine (fraction atom.item).value) :=
        squaredSensitive_probe_eq_of_projectiveEquivalent probe factor
          sensitive
          (CCL.Encoder.encodeBlocks (fraction atom.item)
            (numeratorNonzero atom.item)).realizes.valid
          (CCL.Chordal.Proj.affine_hasNonzeroCoordinate
            (fraction atom.item).value)
          (CCL.Encoder.encodeBlocks_reconstruct
            (fraction atom.item) (numeratorNonzero atom.item))
      rw [probeEqual]

/-- Concrete nonconstant distance-to-`omega` specialization for actual
finite encoder tables. -/
theorem encodedChordalOmegaProbe_thresholdProbabilities_eq_of_margin
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ chordalOmegaProbe
          (CCL.Proj.affine (fraction atom.item).value) ∨
        chordalOmegaProbe
            (CCL.Proj.affine (fraction atom.item).value) + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredThresholdBlockCount margin 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (leftPoints rightPoints : index → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (rightPoints atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          chordalOmegaProbe (leftPoints item)) =
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          chordalOmegaProbe (rightPoints item)) :=
  encodedSquaredProbe_thresholdProbabilities_eq_of_margin distribution
    fraction numeratorNonzero chordalOmegaProbe 2 (by decide)
    chordalOmegaProbe_squaredSensitive threshold margin marginPositive
    separated enough leftPoints rightPoints leftRealizes rightRealizes

/-- Concrete exact affine-target threshold-probability theorem for the
distance-to-`omega` observable. -/
theorem encodedChordalOmegaProbe_thresholdProbability_eq_values_of_margin
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ chordalOmegaProbe
          (CCL.Proj.affine (fraction atom.item).value) ∨
        chordalOmegaProbe
            (CCL.Proj.affine (fraction atom.item).value) + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredThresholdBlockCount margin 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          chordalOmegaProbe (points item)) =
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          chordalOmegaProbe (CCL.Proj.affine (fraction item).value)) :=
  encodedSquaredProbe_thresholdProbability_eq_values_of_margin distribution
    fraction numeratorNonzero chordalOmegaProbe 2 (by decide)
    chordalOmegaProbe_squaredSensitive threshold margin marginPositive
    separated enough points pointsRealize

end CCL.FiniteMeasure
