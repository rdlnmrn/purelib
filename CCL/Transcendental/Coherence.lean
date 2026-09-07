import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.Coherence
import CCL.Progressive.ExpRange
import CCL.Progressive.LogPositive
import CCL.Transcendental.ComplexLogChart
import CCL.Transcendental.Laws
import CCL.Transcendental.FinitePolynomial

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

namespace CCL.TranscendentalCoherence

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev Equivalent :=
  CCL.OperationalEquivalence.Equivalent
abbrev NamedEquivalent :=
  CCL.OperationalEquivalence.NamedEquivalent
abbrev Coherent := CCL.ProgressiveCoherence.Coherent
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed

open RFAP.ConstructiveGaussian.Gaussian

/-- The local unit-disk exponential output is coherent because its process is
generated from the explicit finite Horner approximation. -/
def localExpCoherent (input : Named)
    (domain : CCL.ProgressiveExp.UnitDisk input) :
    Coherent (CCL.ProgressiveExp.named input domain).process :=
  CCL.ProgressiveCoherence.Coherent.ofApproximation
    (CCL.ProgressiveExp.approximation input domain)

/-- Repeated squaring preserves finite process coherence. -/
def squareIterateCoherent : (exponent : Nat) → (value : Named) →
    Coherent value.process →
      Coherent
        (CCL.ProgressiveExpRange.squareIterate exponent value).process
  | 0, _value, coherent => coherent
  | exponent + 1, value, coherent => by
      let previous :=
        CCL.ProgressiveExpRange.squareIterate exponent value
      let previousCoherent := squareIterateCoherent exponent value coherent
      exact CCL.ProgressiveCoherence.Coherent.mul
        previousCoherent previousCoherent

/-- The total range-reduced and repeatedly squared exponential CCL transform
has a finite coherence certificate for every arithmetic input name. -/
def expNamedCoherent (input : Named) :
    Coherent (CCL.ProgressiveExpRange.named input).process := by
  apply squareIterateCoherent
  exact localExpCoherent
    (CCL.ProgressiveExpRange.scaledInput input)
    (CCL.ProgressiveExpRange.scaledDomain input)

def exp (input : Named) : CoherentNamed :=
  { name := CCL.ProgressiveExpRange.named input
    coherent := expNamedCoherent input }

private theorem sixteenths (target : Coordinate) :
    16 * (target / 16) = target := by
  rw [RFAP.ConstructiveFraction.mul_comm]
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 16 (by decide)

private theorem ten_sixteenths_lt {target : Coordinate}
    (positive : 0 < target) : 10 * (target / 16) < target := by
  have scalarOrder : (10 / 16 : Coordinate) < 1 := by decide
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    scalarOrder positive
  calc
    10 * (target / 16) = (10 / 16 : Coordinate) * target := by
      rw [RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ExplicitField.div_eq_mul_inv]
      ring1
    _ < 1 * target := scaled
    _ = target := RFAP.ConstructiveFraction.one_mul _

/-- The progressive local exponential respects finite operational equality of
unit-disk input names.  One finite synchronized pair of input readings is
compared by the Horner sensitivity theorem; two explicitly bounded finite
depth tails complete the output comparison. -/
def localExpApproximation_respects {left right : Named}
    (leftDomain : CCL.ProgressiveExp.UnitDisk left)
    (rightDomain : CCL.ProgressiveExp.UnitDisk right)
    (equivalent : NamedEquivalent left right) :
    Equivalent
      (CCL.ProgressiveExp.approximation left leftDomain)
      (CCL.ProgressiveExp.approximation right rightDomain) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 16
    have smallPositive : 0 < smallTarget :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    let inputTarget := smallTarget / 16
    have inputPositive : 0 < inputTarget :=
      RFAP.ConstructiveFraction.div_pos_direct smallPositive (by decide)
    let inputComparison :=
      equivalent.compare leftStart rightStart inputTarget inputPositive
    let start := max (max leftStart rightStart)
      (max inputComparison.leftIndex inputComparison.rightIndex)
    let depth := CCL.FiniteGeometric.firstQuarterBelow
      10 start smallTarget
    have startLeDepth : start ≤ depth :=
      CCL.FiniteGeometric.firstQuarterBelow_ge
        10 start smallTarget
    have tailSmall :
        CCL.FiniteGeometric.quarterRadius 10 depth <
          smallTarget :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate
        10 (by decide) start smallTarget smallPositive
    have inputLeftLeDepth : inputComparison.leftIndex ≤ depth :=
      (Nat.le_max_left inputComparison.leftIndex
        inputComparison.rightIndex).trans
        ((Nat.le_max_right (max leftStart rightStart)
          (max inputComparison.leftIndex inputComparison.rightIndex)).trans
          startLeDepth)
    have inputRightLeDepth : inputComparison.rightIndex ≤ depth :=
      (Nat.le_max_right inputComparison.leftIndex
        inputComparison.rightIndex).trans
        ((Nat.le_max_right (max leftStart rightStart)
          (max inputComparison.leftIndex inputComparison.rightIndex)).trans
          startLeDepth)
    exact
      { leftIndex := depth
        rightIndex := depth
        left_ge := (Nat.le_max_left leftStart rightStart).trans
          ((Nat.le_max_left (max leftStart rightStart)
            (max inputComparison.leftIndex inputComparison.rightIndex)).trans
            startLeDepth)
        right_ge := (Nat.le_max_right leftStart rightStart).trans
          ((Nat.le_max_left (max leftStart rightStart)
            (max inputComparison.leftIndex inputComparison.rightIndex)).trans
            startLeDepth)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          let leftInput :=
            CCL.ProgressiveExp.inputSample left leftLater
          let rightInput :=
            CCL.ProgressiveExp.inputSample right rightLater
          have leftInputUnit : normSq leftInput ≤ 1 :=
            CCL.ProgressiveExp.inputSample_unit
              leftDomain leftLater
          have rightInputUnit : normSq rightInput ≤ 1 :=
            CCL.ProgressiveExp.inputSample_unit
              rightDomain rightLater
          have inputClose : normSq (leftInput - rightInput) < inputTarget :=
            inputComparison.close
              (inputLeftLeDepth.trans leftOrder)
              (inputRightLeDepth.trans rightOrder)
          have directLe :=
            CCL.FiniteExp.sample_input_close
              leftInput rightInput leftInputUnit rightInputUnit depth
          have direct :
              normSq
                  (CCL.FiniteExp.sample leftInput depth -
                    CCL.FiniteExp.sample rightInput depth) <
                smallTarget := by
            calc
              normSq
                  (CCL.FiniteExp.sample leftInput depth -
                    CCL.FiniteExp.sample rightInput depth) ≤
                16 * normSq (leftInput - rightInput) := directLe
              _ < 16 * inputTarget :=
                RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                  (by decide) inputClose
              _ = smallTarget := by
                dsimp only [inputTarget]
                exact sixteenths smallTarget
          have leftTail :
              normSq
                  (CCL.FiniteExp.sample leftInput leftLater -
                    CCL.FiniteExp.sample leftInput depth) <
                smallTarget :=
            (CCL.FiniteExp.sample_later_close
              leftInput leftInputUnit leftOrder).trans_lt tailSmall
          have rightTailForward :
              normSq
                  (CCL.FiniteExp.sample rightInput rightLater -
                    CCL.FiniteExp.sample rightInput depth) <
                smallTarget :=
            (CCL.FiniteExp.sample_later_close
              rightInput rightInputUnit rightOrder).trans_lt tailSmall
          have rightTail :
              normSq
                  (CCL.FiniteExp.sample rightInput depth -
                    CCL.FiniteExp.sample rightInput rightLater) <
                smallTarget := by
            have identity :
                CCL.FiniteExp.sample rightInput depth -
                    CCL.FiniteExp.sample rightInput rightLater =
                  -(CCL.FiniteExp.sample rightInput rightLater -
                    CCL.FiniteExp.sample rightInput depth) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [identity, normSq_neg]
            exact rightTailForward
          have middle :
              normSq
                  (CCL.FiniteExp.sample leftInput depth -
                    CCL.FiniteExp.sample rightInput rightLater) <
                2 * (smallTarget + smallTarget) :=
            (normSq_sub_le_via _ _ _).trans_lt
              (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  direct rightTail))
          change normSq
              (CCL.FiniteExp.sample leftInput leftLater -
                CCL.FiniteExp.sample rightInput rightLater) < target
          calc
            normSq
                (CCL.FiniteExp.sample leftInput leftLater -
                  CCL.FiniteExp.sample rightInput rightLater) ≤
              2 *
                (normSq
                    (CCL.FiniteExp.sample leftInput leftLater -
                      CCL.FiniteExp.sample leftInput depth) +
                  normSq
                    (CCL.FiniteExp.sample leftInput depth -
                      CCL.FiniteExp.sample rightInput rightLater)) :=
                normSq_sub_le_via _ _ _
            _ < 2 *
                (smallTarget + 2 * (smallTarget + smallTarget)) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct leftTail middle)
            _ = 10 * smallTarget := by ring1
            _ < target := by
              dsimp only [smallTarget]
              exact ten_sixteenths_lt positive }

/-- Productive-name form of local exponential congruence. -/
def localExpNamed_respects {left right : Named}
    (leftDomain : CCL.ProgressiveExp.UnitDisk left)
    (rightDomain : CCL.ProgressiveExp.UnitDisk right)
    (equivalent : NamedEquivalent left right) :
    NamedEquivalent
      (CCL.ProgressiveExp.named left leftDomain)
      (CCL.ProgressiveExp.named right rightDomain) :=
  CCL.OperationalEquivalence.Equivalent.trans
    (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
      (CCL.ProgressiveExp.approximation left leftDomain))
    (CCL.OperationalEquivalence.Equivalent.trans
      (localExpApproximation_respects leftDomain rightDomain equivalent)
      (CCL.OperationalEquivalence.Equivalent.symm
        (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
          (CCL.ProgressiveExp.approximation right rightDomain))))

/-! ## Connecting approximation products to the actual arithmetic process -/

private theorem approximationMul_refine_component_radius_lt
    (left right : Approximation)
    (state : left.toProcess.State × right.toProcess.State)
    (target : Coordinate) (positive : 0 < target) :
    let refined := (left.toProcess.mul right.toProcess).refine
      state target positive
    left.radiusSq refined.1 < target ∧ right.radiusSq refined.2 < target := by
  let leftName := CCL.ProgressiveEnclosures.Name.centerOnly
    (left.sample state.1) left.centerBound left.centerBound_nonneg
      (left.sample_bounded state.1)
  let rightName := CCL.ProgressiveEnclosures.Name.centerOnly
    (right.sample state.2) right.centerBound right.centerBound_nonneg
      (right.sample_bounded state.2)
  let inputTarget :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget
      leftName rightName target
  have inputPositive : 0 < inputTarget :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget_pos
      leftName rightName positive
  have inputLt : inputTarget < target :=
    CCL.ProgressiveCoherence.Coherent.processMultiplicativeInputTarget_lt_target
      leftName rightName positive
  change left.radiusSq
        (left.refineIndex state.1 inputTarget inputPositive) < target ∧
      right.radiusSq
        (right.refineIndex state.2 inputTarget inputPositive) < target
  exact ⟨(left.refineIndex_accurate state.1 inputTarget inputPositive).trans
      inputLt,
    (right.refineIndex_accurate state.2 inputTarget inputPositive).trans
      inputLt⟩

private theorem approximationMul_stateAt_component_radius_lt
    (left right : Approximation)
    (start : left.toProcess.State × right.toProcess.State) (index : Nat) :
    let state := CCL.ProgressiveSampling.stateAt
      (left.toProcess.mul right.toProcess) start index
    left.radiusSq state.1 <
        CCL.ProgressiveSampling.refinementTarget index ∧
      right.radiusSq state.2 <
        CCL.ProgressiveSampling.refinementTarget index := by
  cases index with
  | zero =>
      exact approximationMul_refine_component_radius_lt left right start _ _
  | succ index =>
      exact approximationMul_refine_component_radius_lt left right
        (CCL.ProgressiveSampling.stateAt
          (left.toProcess.mul right.toProcess) start index) _ _

private theorem approximationMul_witnessAt_eq
    (left right : Approximation)
    (start : left.toProcess.State × right.toProcess.State) (index : Nat) :
    CCL.ProgressiveSampling.witnessAt
        (left.toProcess.mul right.toProcess) start index =
      left.sample
          (CCL.ProgressiveSampling.stateAt
            (left.toProcess.mul right.toProcess) start index).1 *
        right.sample
          (CCL.ProgressiveSampling.stateAt
            (left.toProcess.mul right.toProcess) start index).2 :=
  rfl

def approximationMulBridgeCoefficient
    (left right : Approximation) : Coordinate :=
  8 + 4 * (left.centerBound + right.centerBound)

theorem approximationMulBridgeCoefficient_pos
    (left right : Approximation) :
    0 < approximationMulBridgeCoefficient left right := by
  unfold approximationMulBridgeCoefficient
  exact add_pos_of_pos_of_nonneg (by decide)
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg))

def approximationMulBridgeTarget
    (left right : Approximation) (target : Coordinate) : Coordinate :=
  target / (1 + approximationMulBridgeCoefficient left right)

theorem approximationMulBridgeTarget_pos (left right : Approximation)
    {target : Coordinate} (positive : 0 < target) :
    0 < approximationMulBridgeTarget left right target :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (add_pos_of_pos_of_nonneg (by decide)
      (approximationMulBridgeCoefficient_pos left right).le)

theorem approximationMulBridgeTarget_budget_lt
    (left right : Approximation) {target : Coordinate}
    (positive : 0 < target) :
    approximationMulBridgeTarget left right target *
        approximationMulBridgeCoefficient left right < target := by
  let coefficient := approximationMulBridgeCoefficient left right
  have coefficientPositive : 0 < coefficient :=
    approximationMulBridgeCoefficient_pos left right
  have denominatorPositive : 0 < 1 + coefficient :=
    add_pos (by decide) coefficientPositive
  have fractionLt : coefficient / (1 + coefficient) < 1 := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
    calc
      coefficient = 0 + coefficient :=
        (RFAP.ConstructiveFraction.zero_add coefficient).symm
      _ < 1 + coefficient :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          (by decide) coefficient
      _ = 1 * (1 + coefficient) :=
        (RFAP.ConstructiveFraction.one_mul _).symm
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    positive fractionLt
  calc
    approximationMulBridgeTarget left right target *
        approximationMulBridgeCoefficient left right =
      target * (coefficient / (1 + coefficient)) := by
        dsimp only [approximationMulBridgeTarget, coefficient]
        rw [RFAP.ExplicitField.div_eq_mul_inv,
          RFAP.ExplicitField.div_eq_mul_inv]
        ring1
    _ < target * 1 := scaled
    _ = target := RFAP.ConstructiveFraction.mul_one_direct _

private theorem quarterRadius_four_eq_four_refinementTarget (index : Nat) :
    CCL.FiniteGeometric.quarterRadius 4 index =
      4 * CCL.ProgressiveSampling.refinementTarget index := by
  rw [CCL.ProgressiveSampling.refinementTarget,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  ring1

/-- Multiplying two approximation-generated CCL names with the actual
stateful arithmetic process is operationally equivalent to any explicitly
supplied approximation whose `n`th sample is their pointwise `n`th product.
This is the bridge missing from the earlier local exponential addition law. -/
def mulToNamed_equivalent_pointwise (left right product : Approximation)
    (sample_eq : ∀ index,
      product.sample index = left.sample index * right.sample index) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        left.toNamed right.toNamed)
      product.toNamed := by
  let process := left.toProcess.mul right.toProcess
  let start : process.State :=
    (show left.toProcess.State from (0 : Nat),
      show right.toProcess.State from (0 : Nat))
  let bridge : Equivalent
      (CCL.ProgressiveSampling.approximation
        (CCL.ProgressiveTransducer.Named.mul
          left.toNamed right.toNamed)) product :=
    { compare := by
        intro leftStart rightStart target positive
        let smallTarget := approximationMulBridgeTarget left right target
        have smallPositive : 0 < smallTarget :=
          approximationMulBridgeTarget_pos left right positive
        let leftIndex := CCL.FiniteGeometric.firstQuarterBelow
          1 leftStart smallTarget
        have leftIndexGe : leftStart ≤ leftIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            1 leftStart smallTarget
        have outerSmall :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              smallTarget :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            1 (by decide) leftStart smallTarget smallPositive
        let baseState := CCL.ProgressiveSampling.stateAt
          process start leftIndex
        let baseLeft : Nat := baseState.1
        let baseRight : Nat := baseState.2
        have componentSmall :
            left.radiusSq baseLeft <
                CCL.ProgressiveSampling.refinementTarget leftIndex ∧
              right.radiusSq baseRight <
                CCL.ProgressiveSampling.refinementTarget leftIndex :=
          approximationMul_stateAt_component_radius_lt
            left right start leftIndex
        let rightIndex := max rightStart (max baseLeft baseRight)
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := leftIndexGe
            right_ge := Nat.le_max_left _ _
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have leftComponentOrder : baseLeft ≤ rightLater :=
                (Nat.le_max_left baseLeft baseRight).trans
                  ((Nat.le_max_right rightStart
                    (max baseLeft baseRight)).trans rightOrder)
              have rightComponentOrder : baseRight ≤ rightLater :=
                (Nat.le_max_right baseLeft baseRight).trans
                  ((Nat.le_max_right rightStart
                    (max baseLeft baseRight)).trans rightOrder)
              have leftMovementForward := left.later_close leftComponentOrder
              have rightMovementForward := right.later_close rightComponentOrder
              have leftMovement :
                  normSq
                      (left.sample baseLeft -
                        left.sample rightLater) ≤
                    left.radiusSq baseLeft := by
                have identity :
                    left.sample baseLeft - left.sample rightLater =
                      -(left.sample rightLater - left.sample baseLeft) := by
                  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                    simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
                rw [identity, normSq_neg]
                exact leftMovementForward
              have rightMovement :
                  normSq
                      (right.sample baseRight -
                        right.sample rightLater) ≤
                    right.radiusSq baseRight := by
                have identity :
                    right.sample baseRight - right.sample rightLater =
                      -(right.sample rightLater - right.sample baseRight) := by
                  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                    simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
                rw [identity, normSq_neg]
                exact rightMovementForward
              have firstTerm :
                  normSq
                      ((left.sample baseLeft - left.sample rightLater) *
                        right.sample baseRight) ≤
                    left.radiusSq baseLeft * right.centerBound := by
                rw [normSq_mul]
                exact RFAP.ConstructiveFraction.mul_le_mul_direct
                  leftMovement (right.sample_bounded baseRight)
                  (normSq_nonneg _) (left.radiusSq_nonneg baseLeft)
              have secondTerm :
                  normSq
                      (left.sample rightLater *
                        (right.sample baseRight -
                          right.sample rightLater)) ≤
                    left.centerBound * right.radiusSq baseRight := by
                rw [normSq_mul]
                exact RFAP.ConstructiveFraction.mul_le_mul_direct
                  (left.sample_bounded rightLater) rightMovement
                  (normSq_nonneg _) left.centerBound_nonneg
              have productIdentity :
                  left.sample baseLeft * right.sample baseRight -
                      left.sample rightLater * right.sample rightLater =
                    (left.sample baseLeft - left.sample rightLater) *
                        right.sample baseRight +
                      left.sample rightLater *
                        (right.sample baseRight -
                          right.sample rightLater) := by
                apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                  simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
                    ring1
              have pointwiseBound :
                  normSq
                      (left.sample baseLeft * right.sample baseRight -
                        product.sample rightLater) ≤
                    2 *
                      (CCL.ProgressiveSampling.refinementTarget
                          leftIndex * right.centerBound +
                        left.centerBound *
                          CCL.ProgressiveSampling.refinementTarget
                            leftIndex) := by
                rw [sample_eq, productIdentity]
                calc
                  normSq
                      ((left.sample baseLeft - left.sample rightLater) *
                          right.sample baseRight +
                        left.sample rightLater *
                          (right.sample baseRight -
                            right.sample rightLater)) ≤
                    2 *
                      (normSq
                          ((left.sample baseLeft -
                              left.sample rightLater) *
                            right.sample baseRight) +
                        normSq
                          (left.sample rightLater *
                            (right.sample baseRight -
                              right.sample rightLater))) :=
                    normSq_add_le_two _ _
                  _ ≤ 2 *
                      (left.radiusSq baseLeft * right.centerBound +
                        left.centerBound * right.radiusSq baseRight) :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      (add_le_add firstTerm secondTerm) (by decide)
                  _ ≤ 2 *
                      (CCL.ProgressiveSampling.refinementTarget
                          leftIndex * right.centerBound +
                        left.centerBound *
                          CCL.ProgressiveSampling.refinementTarget
                            leftIndex) :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      (add_le_add
                        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                          componentSmall.1.le right.centerBound_nonneg)
                        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                          componentSmall.2.le left.centerBound_nonneg))
                      (by decide)
              have actualTail :
                  normSq
                      (CCL.ProgressiveSampling.witnessAt
                          process start leftLater -
                        CCL.ProgressiveSampling.witnessAt
                          process start leftIndex) ≤
                    4 * CCL.ProgressiveSampling.refinementTarget
                      leftIndex := by
                rw [← quarterRadius_four_eq_four_refinementTarget]
                exact CCL.ProgressiveSampling.witnessAt_later_close
                  process start leftOrder
              change normSq
                  (CCL.ProgressiveSampling.witnessAt
                      process start leftLater - product.sample rightLater) <
                target
              calc
                normSq
                    (CCL.ProgressiveSampling.witnessAt
                        process start leftLater - product.sample rightLater) ≤
                  2 *
                    (normSq
                        (CCL.ProgressiveSampling.witnessAt
                            process start leftLater -
                          CCL.ProgressiveSampling.witnessAt
                            process start leftIndex) +
                      normSq
                        (CCL.ProgressiveSampling.witnessAt
                            process start leftIndex -
                          product.sample rightLater)) :=
                    normSq_sub_le_via _ _ _
                _ ≤ 2 *
                    (4 *
                        CCL.ProgressiveSampling.refinementTarget
                          leftIndex +
                      2 *
                        (CCL.ProgressiveSampling.refinementTarget
                            leftIndex * right.centerBound +
                          left.centerBound *
                            CCL.ProgressiveSampling.refinementTarget
                              leftIndex)) := by
                  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                  · apply add_le_add actualTail
                    rw [approximationMul_witnessAt_eq]
                    exact pointwiseBound
                  · decide
                _ = CCL.ProgressiveSampling.refinementTarget
                      leftIndex *
                    approximationMulBridgeCoefficient left right := by
                  unfold approximationMulBridgeCoefficient
                  ring1
                _ < smallTarget *
                    approximationMulBridgeCoefficient left right :=
                  RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
                    outerSmall
                    (approximationMulBridgeCoefficient_pos left right)
                _ < target :=
                  approximationMulBridgeTarget_budget_lt left right positive } }
  exact CCL.OperationalEquivalence.Equivalent.trans bridge
    (CCL.OperationalEquivalence.Equivalent.symm
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
        product))

/-- Approximations with identical displayed samples are operationally
equivalent, irrespective of their conservative error bookkeeping. -/
def approximationEquivalentOfSamplesEq (left right : Approximation)
    (samples : ∀ index, left.sample index = right.sample index) :
    Equivalent left right where
  compare := by
    intro leftStart rightStart target positive
    let comparison :=
      (CCL.OperationalEquivalence.Equivalent.refl left).compare
        leftStart rightStart target positive
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          rw [← samples rightLater]
          exact comparison.close leftOrder rightOrder }

/-- Lift an approximation equivalence through both ordinary productive CCL
controllers. -/
def approximationEquivalent_toNamed {left right : Approximation}
    (equivalent : Equivalent left right) :
    NamedEquivalent left.toNamed right.toNamed :=
  CCL.OperationalEquivalence.Equivalent.toNamed equivalent

/-- Every CCL name is operationally equivalent to the productive wrapper of
its own canonical finite sampler. -/
def named_toSamplingNamed (name : Named) :
    NamedEquivalent name
      (CCL.ProgressiveSampling.approximation name).toNamed :=
  CCL.OperationalEquivalence.Equivalent.symm
    (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
      (CCL.ProgressiveSampling.approximation name))

def exactLocalExpApproximation (value : Gaussian)
    (unit : normSq value ≤ 1) : Approximation :=
  CCL.ProgressiveExp.approximation
    (CCL.ProgressiveTransducer.Named.exact value)
    (CCL.ProgressiveExp.UnitDisk.exact value unit)

def exactLocalExpNamed (value : Gaussian) (unit : normSq value ≤ 1) :
    Named :=
  (exactLocalExpApproximation value unit).toNamed

@[simp] theorem exactLocalExpApproximation_sample
    (value : Gaussian) (unit : normSq value ≤ 1) (index : Nat) :
    (exactLocalExpApproximation value unit).sample index =
      CCL.FiniteExp.sample value index :=
  rfl

/-- The local exponential addition theorem now stated for the actual
arithmetic expression tree: the left side is `Named.mul` of the two local
progressive exponential outputs, not a separately wrapped product stream. -/
def localExp_add_actual_named_equivalent {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1)
    (sumUnit : normSq (x + y) ≤ 1) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (exactLocalExpNamed x xUnit) (exactLocalExpNamed y yUnit))
      (exactLocalExpNamed (x + y) sumUnit) := by
  let leftApproximation := exactLocalExpApproximation x xUnit
  let rightApproximation := exactLocalExpApproximation y yUnit
  let productApproximation :=
    CCL.TranscendentalLaws.expProductApproximation
      x y xUnit yUnit
  let sumApproximation :=
    CCL.FiniteExp.approximation (x + y) sumUnit
  have arithmeticBridge :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          leftApproximation.toNamed rightApproximation.toNamed)
        productApproximation.toNamed :=
    mulToNamed_equivalent_pointwise leftApproximation rightApproximation
      productApproximation (by intro index; rfl)
  have analyticLaw :
      NamedEquivalent productApproximation.toNamed sumApproximation.toNamed :=
    CCL.TranscendentalLaws.exp_add_named_equivalent
      xUnit yUnit sumUnit
  have sumSamples : ∀ index,
      sumApproximation.sample index =
        (exactLocalExpApproximation (x + y) sumUnit).sample index := by
    intro index
    rfl
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    arithmeticBridge
    (CCL.OperationalEquivalence.NamedEquivalent.trans analyticLaw
      (approximationEquivalent_toNamed
        (approximationEquivalentOfSamplesEq sumApproximation
          (exactLocalExpApproximation (x + y) sumUnit) sumSamples)))

/-! ## Canonical finite squaring and its congruence -/

def squareApproximationFactor (source : Approximation) : Coordinate :=
  4 * (1 + source.centerBound)

theorem squareApproximationFactor_pos (source : Approximation) :
    0 < squareApproximationFactor source := by
  unfold squareApproximationFactor
  exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg (by decide) source.centerBound_nonneg)

/-- Pointwise squaring of displayed finite samples, with an explicit finite
error transport and refinement request. -/
def squareApproximation (source : Approximation) : Approximation where
  sample index := source.sample index * source.sample index
  radiusSq index := squareApproximationFactor source * source.radiusSq index
  radiusSq_nonneg index :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (squareApproximationFactor_pos source).le
      (source.radiusSq_nonneg index)
  later_close := by
    intro earlier later order
    have movement := source.later_close order
    have firstTerm :
        normSq
            ((source.sample later - source.sample earlier) *
              source.sample later) ≤
          source.radiusSq earlier * source.centerBound := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct movement
        (source.sample_bounded later) (normSq_nonneg _)
        (source.radiusSq_nonneg earlier)
    have secondTerm :
        normSq
            (source.sample earlier *
              (source.sample later - source.sample earlier)) ≤
          source.centerBound * source.radiusSq earlier := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct
        (source.sample_bounded earlier) movement (normSq_nonneg _)
        source.centerBound_nonneg
    have identity :
        source.sample later * source.sample later -
            source.sample earlier * source.sample earlier =
          (source.sample later - source.sample earlier) *
              source.sample later +
            source.sample earlier *
              (source.sample later - source.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
    rw [identity]
    calc
      normSq
          ((source.sample later - source.sample earlier) *
              source.sample later +
            source.sample earlier *
              (source.sample later - source.sample earlier)) ≤
        2 *
          (normSq
              ((source.sample later - source.sample earlier) *
                source.sample later) +
            normSq
              (source.sample earlier *
                (source.sample later - source.sample earlier))) :=
        normSq_add_le_two _ _
      _ ≤ 2 *
          (source.radiusSq earlier * source.centerBound +
            source.centerBound * source.radiusSq earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = 4 * source.centerBound * source.radiusSq earlier := by ring1
      _ ≤ squareApproximationFactor source * source.radiusSq earlier := by
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        · unfold squareApproximationFactor
          have oneNonnegative : (0 : Coordinate) ≤ 1 := by decide
          have boundOrder : source.centerBound ≤ 1 + source.centerBound :=
            le_add_of_nonneg_left oneNonnegative
          exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            boundOrder (by decide)
        · exact source.radiusSq_nonneg earlier
  refineIndex current target positive :=
    source.refineIndex current (target / squareApproximationFactor source)
      (RFAP.ConstructiveFraction.div_pos_direct positive
        (squareApproximationFactor_pos source))
  refineIndex_ge current target positive :=
    source.refineIndex_ge current
      (target / squareApproximationFactor source)
      (RFAP.ConstructiveFraction.div_pos_direct positive
        (squareApproximationFactor_pos source))
  refineIndex_accurate := by
    intro current target positive
    let inputTarget := target / squareApproximationFactor source
    have inputPositive : 0 < inputTarget :=
      RFAP.ConstructiveFraction.div_pos_direct positive
        (squareApproximationFactor_pos source)
    have small := source.refineIndex_accurate current inputTarget inputPositive
    calc
      squareApproximationFactor source *
          source.radiusSq (source.refineIndex current inputTarget inputPositive) <
        squareApproximationFactor source * inputTarget :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (squareApproximationFactor_pos source) small
      _ = target := by
        rw [RFAP.ConstructiveFraction.mul_comm]
        exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne target
          (squareApproximationFactor source)
          (squareApproximationFactor_pos source).ne'
  centerBound := source.centerBound * source.centerBound
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct source.centerBound_nonneg
      source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (source.sample_bounded index) (source.sample_bounded index)
      (normSq_nonneg _) source.centerBound_nonneg

@[simp] theorem squareApproximation_sample (source : Approximation)
    (index : Nat) :
    (squareApproximation source).sample index =
      source.sample index * source.sample index :=
  rfl

/-- Pointwise finite squaring respects operational equivalence of its source
approximations. -/
def squareApproximation_respects {left right : Approximation}
    (equivalent : Equivalent left right) :
    Equivalent (squareApproximation left) (squareApproximation right) where
  compare := by
    intro leftStart rightStart target positive
    let inputTarget := approximationMulBridgeTarget left right target
    have inputPositive : 0 < inputTarget :=
      approximationMulBridgeTarget_pos left right positive
    let comparison := equivalent.compare leftStart rightStart
      inputTarget inputPositive
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have inputClose := comparison.close leftOrder rightOrder
          have firstTerm :
              normSq
                  ((left.sample leftLater - right.sample rightLater) *
                    left.sample leftLater) ≤
                normSq (left.sample leftLater - right.sample rightLater) *
                  left.centerBound := by
            rw [normSq_mul]
            exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (left.sample_bounded leftLater) (normSq_nonneg _)
          have secondTerm :
              normSq
                  (right.sample rightLater *
                    (left.sample leftLater - right.sample rightLater)) ≤
                right.centerBound *
                  normSq (left.sample leftLater - right.sample rightLater) := by
            rw [normSq_mul]
            exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              (right.sample_bounded rightLater) (normSq_nonneg _)
          have identity :
              left.sample leftLater * left.sample leftLater -
                  right.sample rightLater * right.sample rightLater =
                (left.sample leftLater - right.sample rightLater) *
                    left.sample leftLater +
                  right.sample rightLater *
                    (left.sample leftLater - right.sample rightLater) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
                ring1
          change normSq
              (left.sample leftLater * left.sample leftLater -
                right.sample rightLater * right.sample rightLater) < target
          rw [identity]
          calc
            normSq
                ((left.sample leftLater - right.sample rightLater) *
                    left.sample leftLater +
                  right.sample rightLater *
                    (left.sample leftLater - right.sample rightLater)) ≤
              2 *
                (normSq
                    ((left.sample leftLater - right.sample rightLater) *
                      left.sample leftLater) +
                  normSq
                    (right.sample rightLater *
                      (left.sample leftLater - right.sample rightLater))) :=
              normSq_add_le_two _ _
            _ ≤ 2 *
                (normSq (left.sample leftLater - right.sample rightLater) *
                    left.centerBound +
                  right.centerBound *
                    normSq
                      (left.sample leftLater - right.sample rightLater)) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (add_le_add firstTerm secondTerm) (by decide)
            _ = normSq (left.sample leftLater - right.sample rightLater) *
                (2 * (left.centerBound + right.centerBound)) := by ring1
            _ ≤ normSq (left.sample leftLater - right.sample rightLater) *
                approximationMulBridgeCoefficient left right := by
              apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              · unfold approximationMulBridgeCoefficient
                have nonnegative :
                    0 ≤ 8 + 2 * (left.centerBound + right.centerBound) :=
                  add_nonneg (by decide)
                    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                      (add_nonneg left.centerBound_nonneg
                        right.centerBound_nonneg))
                apply sub_nonneg.mp
                convert nonnegative using 1
                ring1
              · exact normSq_nonneg _
            _ < inputTarget *
                approximationMulBridgeCoefficient left right :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
                inputClose
                (approximationMulBridgeCoefficient_pos left right)
            _ < target :=
              approximationMulBridgeTarget_budget_lt left right positive }

private theorem quarterRadius_index_antitone {scale : Coordinate}
    (scaleNonnegative : 0 ≤ scale) {earlier later : Nat}
    (order : earlier ≤ later) :
    CCL.FiniteGeometric.quarterRadius scale later ≤
      CCL.FiniteGeometric.quarterRadius scale earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_add]
  have extraPowerLe : (1 / 4 : Coordinate) ^ extra ≤ 1 := by
    have powerOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      (show (0 : Coordinate) ≤ 1 / 4 by decide)
      (show (1 / 4 : Coordinate) ≤ 1 by decide) extra
    simpa only [one_pow] using powerOrder
  have earlierPowerNonnegative : 0 ≤ (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _
  have scaledNonnegative :
      0 ≤ scale * (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
      earlierPowerNonnegative
  calc
    scale * ((1 / 4 : Coordinate) ^ earlier *
        (1 / 4 : Coordinate) ^ extra) =
      (scale * (1 / 4 : Coordinate) ^ earlier) *
        (1 / 4 : Coordinate) ^ extra := by ring1
    _ ≤ (scale * (1 / 4 : Coordinate) ^ earlier) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        extraPowerLe scaledNonnegative
    _ = scale * (1 / 4 : Coordinate) ^ earlier :=
      RFAP.ConstructiveFraction.mul_one_direct _

private theorem coherentMul_refine_component_allowance_lt
    {process : Process} (coherent : Coherent process)
    (state : process.State × process.State)
    (request : Coordinate) (requestPositive : 0 < request)
    (target : Coordinate) (targetPositive : 0 < target)
    (requestSmall : request < coherent.accuracyRequest target) :
    let refined := (process.mul process).refine
      state request requestPositive
    coherent.allowance refined.1 < target ∧
      coherent.allowance refined.2 < target := by
  let leftName := CCL.ProgressiveEnclosures.Name.centerOnly
    (process.ball state.1).center process.centerBound
      process.centerBound_nonneg (process.center_bounded state.1)
  let rightName := CCL.ProgressiveEnclosures.Name.centerOnly
    (process.ball state.2).center process.centerBound
      process.centerBound_nonneg (process.center_bounded state.2)
  let inputRequest :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget
      leftName rightName request
  have inputPositive : 0 < inputRequest :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget_pos
      leftName rightName requestPositive
  have inputLtRequest : inputRequest < request :=
    CCL.ProgressiveCoherence.Coherent.processMultiplicativeInputTarget_lt_target
      leftName rightName requestPositive
  have inputSmall : inputRequest < coherent.accuracyRequest target :=
    inputLtRequest.trans requestSmall
  change coherent.allowance
        (process.refine state.1 inputRequest inputPositive) < target ∧
      coherent.allowance
        (process.refine state.2 inputRequest inputPositive) < target
  exact ⟨coherent.refine_accurate state.1 target targetPositive
      inputRequest inputPositive inputSmall,
    coherent.refine_accurate state.2 target targetPositive
      inputRequest inputPositive inputSmall⟩

private theorem coherentMul_stateAt_component_allowance_lt
    {process : Process} (coherent : Coherent process)
    (start : process.State × process.State) (index : Nat)
    (target : Coordinate) (targetPositive : 0 < target)
    (requestSmall :
      CCL.ProgressiveSampling.refinementTarget index <
        coherent.accuracyRequest target) :
    let state := CCL.ProgressiveSampling.stateAt
      (process.mul process) start index
    coherent.allowance state.1 < target ∧
      coherent.allowance state.2 < target := by
  cases index with
  | zero =>
      exact coherentMul_refine_component_allowance_lt coherent start _ _
        target targetPositive requestSmall
  | succ index =>
      exact coherentMul_refine_component_allowance_lt coherent
        (CCL.ProgressiveSampling.stateAt
          (process.mul process) start index) _ _ target targetPositive
            requestSmall

def coherentSquareBridgeCoefficient (process : Process) : Coordinate :=
  8 + 4 * (4 * (8 * (1 + process.centerBound)))

theorem coherentSquareBridgeCoefficient_pos (process : Process) :
    0 < coherentSquareBridgeCoefficient process := by
  unfold coherentSquareBridgeCoefficient
  exact add_pos_of_pos_of_nonneg (by decide)
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg (by decide) process.centerBound_nonneg))))

def coherentSquareBridgeTarget (process : Process) (target : Coordinate) :
    Coordinate :=
  target / (target + coherentSquareBridgeCoefficient process)

theorem coherentSquareBridgeTarget_pos (process : Process)
    {target : Coordinate} (positive : 0 < target) :
    0 < coherentSquareBridgeTarget process target :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (add_pos positive (coherentSquareBridgeCoefficient_pos process))

theorem coherentSquareBridgeTarget_lt_one (process : Process)
    {target : Coordinate} (positive : 0 < target) :
    coherentSquareBridgeTarget process target < 1 := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos positive (coherentSquareBridgeCoefficient_pos process))).2
  calc
    target = 0 + target :=
      (RFAP.ConstructiveFraction.zero_add target).symm
    _ < coherentSquareBridgeCoefficient process + target :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct
        (coherentSquareBridgeCoefficient_pos process) target
    _ = target + coherentSquareBridgeCoefficient process :=
      RFAP.ConstructiveFraction.add_comm _ _
    _ = 1 * (target + coherentSquareBridgeCoefficient process) :=
      (RFAP.ConstructiveFraction.one_mul _).symm

theorem coherentSquareBridgeTarget_budget_lt (process : Process)
    {target : Coordinate} (positive : 0 < target) :
    coherentSquareBridgeTarget process target *
        coherentSquareBridgeCoefficient process < target := by
  have denominatorPositive :
      0 < target + coherentSquareBridgeCoefficient process :=
    add_pos positive (coherentSquareBridgeCoefficient_pos process)
  change target /
      (target + coherentSquareBridgeCoefficient process) *
        coherentSquareBridgeCoefficient process < target
  calc
    target / (target + coherentSquareBridgeCoefficient process) *
        coherentSquareBridgeCoefficient process =
      (target * coherentSquareBridgeCoefficient process) /
        (target + coherentSquareBridgeCoefficient process) := by
      change (target *
          (target + coherentSquareBridgeCoefficient process)⁻¹) *
            coherentSquareBridgeCoefficient process =
        (target * coherentSquareBridgeCoefficient process) *
          (target + coherentSquareBridgeCoefficient process)⁻¹
      calc
        (target *
            (target + coherentSquareBridgeCoefficient process)⁻¹) *
              coherentSquareBridgeCoefficient process =
          target *
            ((target + coherentSquareBridgeCoefficient process)⁻¹ *
              coherentSquareBridgeCoefficient process) :=
            _root_.mul_assoc _ _ _
        _ = target *
            (coherentSquareBridgeCoefficient process *
              (target + coherentSquareBridgeCoefficient process)⁻¹) := by
          rw [RFAP.ConstructiveFraction.mul_comm
            (target + coherentSquareBridgeCoefficient process)⁻¹]
        _ = (target * coherentSquareBridgeCoefficient process) *
            (target + coherentSquareBridgeCoefficient process)⁻¹ :=
          (_root_.mul_assoc _ _ _).symm
    _ < target := by
      apply (RFAP.ConstructiveFraction.div_lt_iff_pos
        denominatorPositive).2
      have coefficientLt : coherentSquareBridgeCoefficient process <
          target + coherentSquareBridgeCoefficient process := by
        calc
          coherentSquareBridgeCoefficient process =
              0 + coherentSquareBridgeCoefficient process :=
            (RFAP.ConstructiveFraction.zero_add _).symm
          _ < target + coherentSquareBridgeCoefficient process :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct positive _
      exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive coefficientLt

/-- Actual stateful self-multiplication of a coherent CCL name is
operationally equivalent to the canonical pointwise square of its finite
sampling approximation. -/
def coherentSquare_toNamed (value : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul value.name value.name)
      (squareApproximation
        (CCL.ProgressiveSampling.approximation value.name)).toNamed := by
  let process := value.name.process
  let start : process.State × process.State :=
    (value.name.state, value.name.state)
  let source := CCL.ProgressiveSampling.approximation value.name
  let squared := squareApproximation source
  let bridge : Equivalent
      (CCL.ProgressiveSampling.approximation
        (CCL.ProgressiveTransducer.Named.mul
          value.name value.name)) squared :=
    { compare := by
        intro leftStart rightStart target positive
        let semanticTarget := coherentSquareBridgeTarget process target
        have semanticPositive : 0 < semanticTarget :=
          coherentSquareBridgeTarget_pos process positive
        have semanticLtOne : semanticTarget < 1 :=
          coherentSquareBridgeTarget_lt_one process positive
        let processThreshold := value.coherent.accuracyRequest semanticTarget
        have processThresholdPositive : 0 < processThreshold :=
          value.coherent.accuracyRequest_pos semanticPositive
        let outputThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest
            processThreshold semanticTarget
        have outputThresholdPositive : 0 < outputThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest_pos
            processThresholdPositive semanticPositive
        let leftIndex := CCL.FiniteGeometric.firstQuarterBelow
          1 leftStart outputThreshold
        have leftIndexGe : leftStart ≤ leftIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            1 leftStart outputThreshold
        have outputRequestSmall :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              outputThreshold :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            1 (by decide) leftStart outputThreshold outputThresholdPositive
        have outputRequestLtProcess :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              processThreshold :=
          outputRequestSmall.trans
            (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
              processThresholdPositive semanticPositive)
        have outputRequestLtSemantic :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              semanticTarget :=
          outputRequestSmall.trans
            (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
              processThresholdPositive semanticPositive)
        let rightIndex := CCL.FiniteGeometric.firstQuarterBelow
          1 rightStart processThreshold
        have rightIndexGe : rightStart ≤ rightIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            1 rightStart processThreshold
        have rightRequestSmall :
            CCL.ProgressiveSampling.refinementTarget rightIndex <
              processThreshold :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            1 (by decide) rightStart processThreshold processThresholdPositive
        let baseState := CCL.ProgressiveSampling.stateAt
          (process.mul process) start leftIndex
        have componentSmall :
            value.coherent.allowance baseState.1 < semanticTarget ∧
              value.coherent.allowance baseState.2 < semanticTarget :=
          coherentMul_stateAt_component_allowance_lt value.coherent start
            leftIndex semanticTarget semanticPositive outputRequestLtProcess
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := leftIndexGe
            right_ge := rightIndexGe
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have canonicalRequestSmall :
                  CCL.ProgressiveSampling.refinementTarget
                      rightLater < processThreshold :=
                (quarterRadius_index_antitone (by decide) rightOrder).trans_lt
                  rightRequestSmall
              have canonicalAllowanceSmall :
                  value.coherent.allowance
                      (CCL.ProgressiveSampling.stateAt process
                        value.name.state rightLater) < semanticTarget :=
                CCL.ProgressiveCoherence.Coherent.stateAt_allowance_lt
                  value.coherent value.name.state rightLater semanticTarget
                    semanticPositive canonicalRequestSmall
              let leftReading := (process.witness baseState.1).val
              let rightReading := (process.witness baseState.2).val
              let canonicalReading :=
                CCL.ProgressiveSampling.witnessAt process
                  value.name.state rightLater
              have leftPossible : process.Possible baseState.1 leftReading :=
                (process.witness baseState.1).property
              have rightPossible : process.Possible baseState.2 rightReading :=
                (process.witness baseState.2).property
              have canonicalPossible :
                  process.Possible
                      (CCL.ProgressiveSampling.stateAt process
                        value.name.state rightLater) canonicalReading :=
                CCL.ProgressiveSampling.witnessAt_possible
                  process value.name.state rightLater
              have leftCloseRaw := value.coherent.possible_close
                leftPossible canonicalPossible
              have rightCloseRaw := value.coherent.possible_close
                rightPossible canonicalPossible
              have allowanceSumLeft :
                  value.coherent.allowance baseState.1 +
                      value.coherent.allowance
                        (CCL.ProgressiveSampling.stateAt process
                          value.name.state rightLater) <
                    semanticTarget + semanticTarget :=
                RFAP.ConstructiveFraction.add_lt_add_direct
                  componentSmall.1 canonicalAllowanceSmall
              have allowanceSumRight :
                  value.coherent.allowance baseState.2 +
                      value.coherent.allowance
                        (CCL.ProgressiveSampling.stateAt process
                          value.name.state rightLater) <
                    semanticTarget + semanticTarget :=
                RFAP.ConstructiveFraction.add_lt_add_direct
                  componentSmall.2 canonicalAllowanceSmall
              have leftClose : normSq (leftReading - canonicalReading) ≤
                  8 * semanticTarget := by
                calc
                  normSq (leftReading - canonicalReading) ≤
                    4 *
                      (value.coherent.allowance baseState.1 +
                        value.coherent.allowance
                          (CCL.ProgressiveSampling.stateAt process
                            value.name.state rightLater)) := leftCloseRaw
                  _ ≤ 4 * (semanticTarget + semanticTarget) :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      allowanceSumLeft.le (by decide)
                  _ = 8 * semanticTarget := by ring1
              have rightClose : normSq (rightReading - canonicalReading) ≤
                  8 * semanticTarget := by
                calc
                  normSq (rightReading - canonicalReading) ≤
                    4 *
                      (value.coherent.allowance baseState.2 +
                        value.coherent.allowance
                          (CCL.ProgressiveSampling.stateAt process
                            value.name.state rightLater)) := rightCloseRaw
                  _ ≤ 4 * (semanticTarget + semanticTarget) :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      allowanceSumRight.le (by decide)
                  _ = 8 * semanticTarget := by ring1
              let readingBound := 2 * (1 + process.centerBound)
              have rightAllowanceBound :
                  value.coherent.allowance baseState.2 + process.centerBound ≤
                    1 + process.centerBound := by
                calc
                  value.coherent.allowance baseState.2 + process.centerBound =
                      process.centerBound +
                        value.coherent.allowance baseState.2 :=
                    RFAP.ConstructiveFraction.add_comm _ _
                  _ ≤ process.centerBound + semanticTarget :=
                    add_le_add_right componentSmall.2.le process.centerBound
                  _ ≤ process.centerBound + 1 :=
                    add_le_add_right semanticLtOne.le process.centerBound
                  _ = 1 + process.centerBound :=
                    RFAP.ConstructiveFraction.add_comm _ _
              have canonicalAllowanceBound :
                  value.coherent.allowance
                      (CCL.ProgressiveSampling.stateAt process
                        value.name.state rightLater) + process.centerBound ≤
                    1 + process.centerBound := by
                calc
                  value.coherent.allowance
                        (CCL.ProgressiveSampling.stateAt process
                          value.name.state rightLater) + process.centerBound =
                      process.centerBound +
                        value.coherent.allowance
                          (CCL.ProgressiveSampling.stateAt process
                            value.name.state rightLater) :=
                    RFAP.ConstructiveFraction.add_comm _ _
                  _ ≤ process.centerBound + semanticTarget :=
                    add_le_add_right canonicalAllowanceSmall.le
                      process.centerBound
                  _ ≤ process.centerBound + 1 :=
                    add_le_add_right semanticLtOne.le process.centerBound
                  _ = 1 + process.centerBound :=
                    RFAP.ConstructiveFraction.add_comm _ _
              have rightReadingNorm : normSq rightReading ≤ readingBound :=
                (CCL.ProgressiveCoherence.Coherent.possible_normSq_le
                  value.coherent rightPossible).trans
                    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      rightAllowanceBound (by decide))
              have canonicalReadingNorm :
                  normSq canonicalReading ≤ readingBound :=
                (CCL.ProgressiveCoherence.Coherent.possible_normSq_le
                  value.coherent canonicalPossible).trans
                    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      canonicalAllowanceBound (by decide))
              have firstTerm :
                  normSq
                      ((leftReading - canonicalReading) * rightReading) ≤
                    (8 * semanticTarget) * readingBound := by
                rw [normSq_mul]
                exact RFAP.ConstructiveFraction.mul_le_mul_direct
                  leftClose rightReadingNorm (normSq_nonneg _)
                  (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                    semanticPositive.le)
              have secondTerm :
                  normSq
                      (canonicalReading *
                        (rightReading - canonicalReading)) ≤
                    readingBound * (8 * semanticTarget) := by
                rw [normSq_mul]
                exact RFAP.ConstructiveFraction.mul_le_mul_direct
                  canonicalReadingNorm rightClose (normSq_nonneg _)
                  (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                    (add_nonneg (by decide) process.centerBound_nonneg))
              have productIdentity :
                  leftReading * rightReading -
                      canonicalReading * canonicalReading =
                    (leftReading - canonicalReading) * rightReading +
                      canonicalReading *
                        (rightReading - canonicalReading) := by
                apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                  simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
                    ring1
              have productBound :
                  normSq
                      (leftReading * rightReading -
                        canonicalReading * canonicalReading) ≤
                    32 * semanticTarget * readingBound := by
                rw [productIdentity]
                calc
                  normSq
                      ((leftReading - canonicalReading) * rightReading +
                        canonicalReading *
                          (rightReading - canonicalReading)) ≤
                    2 *
                      (normSq
                          ((leftReading - canonicalReading) * rightReading) +
                        normSq
                          (canonicalReading *
                            (rightReading - canonicalReading))) :=
                    normSq_add_le_two _ _
                  _ ≤ 2 *
                      ((8 * semanticTarget) * readingBound +
                        readingBound * (8 * semanticTarget)) :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      (add_le_add firstTerm secondTerm) (by decide)
                  _ = 32 * semanticTarget * readingBound := by ring1
              have actualTail :
                  normSq
                      (CCL.ProgressiveSampling.witnessAt
                          (process.mul process) start leftLater -
                        CCL.ProgressiveSampling.witnessAt
                          (process.mul process) start leftIndex) ≤
                    4 * CCL.ProgressiveSampling.refinementTarget
                      leftIndex := by
                rw [← quarterRadius_four_eq_four_refinementTarget]
                exact CCL.ProgressiveSampling.witnessAt_later_close
                  (process.mul process) start leftOrder
              have baseWitness :
                  CCL.ProgressiveSampling.witnessAt
                      (process.mul process) start leftIndex =
                    leftReading * rightReading :=
                rfl
              have canonicalSample : source.sample rightLater =
                  canonicalReading :=
                rfl
              change normSq
                  (CCL.ProgressiveSampling.witnessAt
                      (process.mul process) start leftLater -
                    source.sample rightLater * source.sample rightLater) < target
              rw [canonicalSample]
              calc
                normSq
                    (CCL.ProgressiveSampling.witnessAt
                        (process.mul process) start leftLater -
                      canonicalReading * canonicalReading) ≤
                  2 *
                    (normSq
                        (CCL.ProgressiveSampling.witnessAt
                            (process.mul process) start leftLater -
                          CCL.ProgressiveSampling.witnessAt
                            (process.mul process) start leftIndex) +
                      normSq
                        (CCL.ProgressiveSampling.witnessAt
                            (process.mul process) start leftIndex -
                          canonicalReading * canonicalReading)) :=
                    normSq_sub_le_via _ _ _
                _ ≤ 2 *
                    (4 *
                        CCL.ProgressiveSampling.refinementTarget
                          leftIndex +
                      32 * semanticTarget * readingBound) := by
                  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                  · apply add_le_add actualTail
                    rw [baseWitness]
                    exact productBound
                  · decide
                _ ≤ 2 *
                    (4 * semanticTarget +
                      32 * semanticTarget * readingBound) :=
                  RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                    (add_le_add
                      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                        outputRequestLtSemantic.le (by decide)) le_rfl)
                    (by decide)
                _ = semanticTarget * coherentSquareBridgeCoefficient process := by
                  dsimp only [readingBound]
                  unfold coherentSquareBridgeCoefficient
                  ring1
                _ < target :=
                  coherentSquareBridgeTarget_budget_lt process positive } }
  exact CCL.OperationalEquivalence.Equivalent.trans bridge
    (CCL.OperationalEquivalence.Equivalent.symm
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
        squared))

/-- Stateful squaring respects operational equality of coherent CCL names. -/
def coherentSquare_respects (left right : CoherentNamed)
    (equivalent : NamedEquivalent left.name right.name) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul left.name left.name)
      (CCL.ProgressiveTransducer.Named.mul right.name right.name) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentSquare_toNamed left)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (approximationEquivalent_toNamed
        (squareApproximation_respects equivalent))
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (coherentSquare_toNamed right)))

/-- Any fixed finite number of actual repeated CCL squarings respects
operational equality of coherent starting names. -/
def squareIterate_respects : (exponent : Nat) →
    (left right : CoherentNamed) →
    NamedEquivalent left.name right.name →
    NamedEquivalent
      (CCL.ProgressiveExpRange.squareIterate
        exponent left.name)
      (CCL.ProgressiveExpRange.squareIterate
        exponent right.name)
  | 0, _left, _right, equivalent => equivalent
  | exponent + 1, left, right, equivalent => by
      let previousLeft : CoherentNamed :=
        { name := CCL.ProgressiveExpRange.squareIterate
            exponent left.name
          coherent := squareIterateCoherent exponent left.name left.coherent }
      let previousRight : CoherentNamed :=
        { name := CCL.ProgressiveExpRange.squareIterate
            exponent right.name
          coherent := squareIterateCoherent exponent right.name right.coherent }
      exact coherentSquare_respects previousLeft previousRight
        (squareIterate_respects exponent left right equivalent)

/-! ## Canonical two-input sums and products -/

/-- Equal-index addition of two canonical CCL samplers. -/
def sampledSumApproximation (left right : Named) : Approximation where
  sample index :=
    (CCL.ProgressiveSampling.approximation left).sample index +
      (CCL.ProgressiveSampling.approximation right).sample index
  radiusSq := CCL.FiniteGeometric.quarterRadius 16
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg (by decide)
  later_close := by
    intro earlier later order
    let leftSource := CCL.ProgressiveSampling.approximation left
    let rightSource := CCL.ProgressiveSampling.approximation right
    have leftMovement := leftSource.later_close order
    have rightMovement := rightSource.later_close order
    have identity :
        leftSource.sample later + rightSource.sample later -
            (leftSource.sample earlier + rightSource.sample earlier) =
          (leftSource.sample later - leftSource.sample earlier) +
            (rightSource.sample later - rightSource.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im] <;> ring1
    change normSq
        (leftSource.sample later + rightSource.sample later -
          (leftSource.sample earlier + rightSource.sample earlier)) ≤
      CCL.FiniteGeometric.quarterRadius 16 earlier
    rw [identity]
    calc
      normSq
          ((leftSource.sample later - leftSource.sample earlier) +
            (rightSource.sample later - rightSource.sample earlier)) ≤
        2 *
          (normSq (leftSource.sample later - leftSource.sample earlier) +
            normSq
              (rightSource.sample later - rightSource.sample earlier)) :=
        normSq_add_le_two _ _
      _ ≤ 2 *
          (CCL.FiniteGeometric.quarterRadius 4 earlier +
            CCL.FiniteGeometric.quarterRadius 4 earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftMovement rightMovement) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius 16 earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow 16 current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge 16 current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate 16 (by decide)
  centerBound :=
    2 *
      ((CCL.ProgressiveSampling.approximation left).centerBound +
        (CCL.ProgressiveSampling.approximation right).centerBound)
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (CCL.ProgressiveSampling.approximation left).centerBound_nonneg
        (CCL.ProgressiveSampling.approximation right).centerBound_nonneg)
  sample_bounded := by
    intro index
    exact (normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add
          ((CCL.ProgressiveSampling.approximation left).sample_bounded
            index)
          ((CCL.ProgressiveSampling.approximation right).sample_bounded
            index))
        (by decide))

@[simp] theorem sampledSumApproximation_sample
    (left right : Named) (index : Nat) :
    (sampledSumApproximation left right).sample index =
      (CCL.ProgressiveSampling.approximation left).sample index +
        (CCL.ProgressiveSampling.approximation right).sample index :=
  rfl

private theorem two_quarter_sums (target : Coordinate) :
    2 * (target / 4 + target / 4) = target := by
  calc
    2 * (target / 4 + target / 4) = (target / 4) * 4 := by ring1
    _ = target :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 4 (by decide)

/-- Canonical finite sums respect operational equivalence in both operands. -/
def sampledSumApproximation_respects
    {leftOne leftTwo rightOne rightTwo : Named}
    (leftEquivalent : NamedEquivalent leftOne leftTwo)
    (rightEquivalent : NamedEquivalent rightOne rightTwo) :
    Equivalent
      (sampledSumApproximation leftOne rightOne)
      (sampledSumApproximation leftTwo rightTwo) where
  compare := by
    intro firstStart secondStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    let leftComparison := leftEquivalent.compare firstStart secondStart
      smallTarget smallPositive
    let rightComparison := rightEquivalent.compare firstStart secondStart
      smallTarget smallPositive
    let firstIndex := max leftComparison.leftIndex rightComparison.leftIndex
    let secondIndex := max leftComparison.rightIndex rightComparison.rightIndex
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := leftComparison.left_ge.trans (Nat.le_max_left _ _)
        right_ge := leftComparison.right_ge.trans (Nat.le_max_left _ _)
        close := by
          intro firstLater secondLater firstOrder secondOrder
          have leftClose := leftComparison.close
            ((Nat.le_max_left leftComparison.leftIndex
              rightComparison.leftIndex).trans firstOrder)
            ((Nat.le_max_left leftComparison.rightIndex
              rightComparison.rightIndex).trans secondOrder)
          have rightClose := rightComparison.close
            ((Nat.le_max_right leftComparison.leftIndex
              rightComparison.leftIndex).trans firstOrder)
            ((Nat.le_max_right leftComparison.rightIndex
              rightComparison.rightIndex).trans secondOrder)
          have identity :
              (CCL.ProgressiveSampling.approximation leftOne).sample
                    firstLater +
                  (CCL.ProgressiveSampling.approximation rightOne).sample
                    firstLater -
                ((CCL.ProgressiveSampling.approximation leftTwo).sample
                    secondLater +
                  (CCL.ProgressiveSampling.approximation rightTwo).sample
                    secondLater) =
              ((CCL.ProgressiveSampling.approximation leftOne).sample
                    firstLater -
                  (CCL.ProgressiveSampling.approximation leftTwo).sample
                    secondLater) +
                ((CCL.ProgressiveSampling.approximation rightOne).sample
                    firstLater -
                  (CCL.ProgressiveSampling.approximation rightTwo).sample
                    secondLater) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [sub_re, sub_im, add_re, add_im] <;> ring1
          rw [sampledSumApproximation_sample,
            sampledSumApproximation_sample, identity]
          calc
            normSq
                (((CCL.ProgressiveSampling.approximation leftOne).sample
                      firstLater -
                    (CCL.ProgressiveSampling.approximation leftTwo).sample
                      secondLater) +
                  ((CCL.ProgressiveSampling.approximation rightOne).sample
                      firstLater -
                    (CCL.ProgressiveSampling.approximation rightTwo).sample
                      secondLater)) ≤
              2 *
                (normSq
                    ((CCL.ProgressiveSampling.approximation leftOne).sample
                        firstLater -
                      (CCL.ProgressiveSampling.approximation leftTwo).sample
                        secondLater) +
                  normSq
                    ((CCL.ProgressiveSampling.approximation rightOne).sample
                        firstLater -
                      (CCL.ProgressiveSampling.approximation rightTwo).sample
                        secondLater)) :=
              normSq_add_le_two _ _
            _ < 2 * (smallTarget + smallTarget) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  leftClose rightClose)
            _ = target := by
              dsimp only [smallTarget]
              exact two_quarter_sums target }

/-- Pointwise addition transports two approximation equivalences.  The
explicit sample equations allow either side to use a purpose-built finite
approximation instead of a canonical CCL sampler. -/
def pointwiseSumApproximation_respects
    {leftOne leftTwo rightOne rightTwo firstSum secondSum : Approximation}
    (leftEquivalent : Equivalent leftOne leftTwo)
    (rightEquivalent : Equivalent rightOne rightTwo)
    (firstSamples : ∀ index,
      firstSum.sample index = leftOne.sample index + rightOne.sample index)
    (secondSamples : ∀ index,
      secondSum.sample index = leftTwo.sample index + rightTwo.sample index) :
    Equivalent firstSum secondSum where
  compare := by
    intro firstStart secondStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    let leftComparison := leftEquivalent.compare firstStart secondStart
      smallTarget smallPositive
    let rightComparison := rightEquivalent.compare firstStart secondStart
      smallTarget smallPositive
    let firstIndex := max leftComparison.leftIndex rightComparison.leftIndex
    let secondIndex := max leftComparison.rightIndex rightComparison.rightIndex
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := leftComparison.left_ge.trans (Nat.le_max_left _ _)
        right_ge := leftComparison.right_ge.trans (Nat.le_max_left _ _)
        close := by
          intro firstLater secondLater firstOrder secondOrder
          have leftClose := leftComparison.close
            ((Nat.le_max_left leftComparison.leftIndex
              rightComparison.leftIndex).trans firstOrder)
            ((Nat.le_max_left leftComparison.rightIndex
              rightComparison.rightIndex).trans secondOrder)
          have rightClose := rightComparison.close
            ((Nat.le_max_right leftComparison.leftIndex
              rightComparison.leftIndex).trans firstOrder)
            ((Nat.le_max_right leftComparison.rightIndex
              rightComparison.rightIndex).trans secondOrder)
          have identity :
              (leftOne.sample firstLater + rightOne.sample firstLater) -
                  (leftTwo.sample secondLater + rightTwo.sample secondLater) =
                (leftOne.sample firstLater - leftTwo.sample secondLater) +
                  (rightOne.sample firstLater -
                    rightTwo.sample secondLater) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [sub_re, sub_im, add_re, add_im] <;> ring1
          rw [firstSamples, secondSamples, identity]
          calc
            normSq
                ((leftOne.sample firstLater - leftTwo.sample secondLater) +
                  (rightOne.sample firstLater -
                    rightTwo.sample secondLater)) ≤
              2 *
                (normSq
                    (leftOne.sample firstLater - leftTwo.sample secondLater) +
                  normSq
                    (rightOne.sample firstLater -
                      rightTwo.sample secondLater)) :=
              normSq_add_le_two _ _
            _ < 2 * (smallTarget + smallTarget) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  leftClose rightClose)
            _ = target := by
              dsimp only [smallTarget]
              exact two_quarter_sums target }

def sampledProductErrorScale (left right : Named) : Coordinate :=
  8 *
    (CCL.ProgressiveSampling.approximation left).centerBound +
  8 *
    (CCL.ProgressiveSampling.approximation right).centerBound

theorem sampledProductErrorScale_nonneg (left right : Named) :
    0 ≤ sampledProductErrorScale left right := by
  unfold sampledProductErrorScale
  exact add_nonneg
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (CCL.ProgressiveSampling.approximation left).centerBound_nonneg)
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (CCL.ProgressiveSampling.approximation right).centerBound_nonneg)

/-- A canonical product approximation built from equal-index finite samples
of two arbitrary CCL names.  Its geometric radius is explicit because the
canonical source samplers both use the same quarter-power schedule. -/
def sampledProductApproximation (left right : Named) : Approximation where
  sample index :=
    (CCL.ProgressiveSampling.approximation left).sample index *
      (CCL.ProgressiveSampling.approximation right).sample index
  radiusSq := CCL.FiniteGeometric.quarterRadius
    (sampledProductErrorScale left right)
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      (sampledProductErrorScale_nonneg left right)
  later_close := by
    intro earlier later order
    let leftSource := CCL.ProgressiveSampling.approximation left
    let rightSource := CCL.ProgressiveSampling.approximation right
    have leftMovement := leftSource.later_close order
    have rightMovement := rightSource.later_close order
    have firstTerm :
        normSq
            ((leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later) ≤
          CCL.FiniteGeometric.quarterRadius 4 earlier *
            rightSource.centerBound := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct leftMovement
        (rightSource.sample_bounded later) (normSq_nonneg _)
        (CCL.FiniteGeometric.quarterRadius_nonneg (by decide) _)
    have secondTerm :
        normSq
            (leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
          leftSource.centerBound *
            CCL.FiniteGeometric.quarterRadius 4 earlier := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct
        (leftSource.sample_bounded earlier) rightMovement (normSq_nonneg _)
        leftSource.centerBound_nonneg
    have identity :
        leftSource.sample later * rightSource.sample later -
            leftSource.sample earlier * rightSource.sample earlier =
          (leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later +
            leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
    change normSq
        (leftSource.sample later * rightSource.sample later -
          leftSource.sample earlier * rightSource.sample earlier) ≤
      CCL.FiniteGeometric.quarterRadius
        (sampledProductErrorScale left right) earlier
    rw [identity]
    calc
      normSq
          ((leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later +
            leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
        2 *
          (normSq
              ((leftSource.sample later - leftSource.sample earlier) *
                rightSource.sample later) +
            normSq
              (leftSource.sample earlier *
                (rightSource.sample later - rightSource.sample earlier))) :=
        normSq_add_le_two _ _
      _ ≤ 2 *
          (CCL.FiniteGeometric.quarterRadius 4 earlier *
              rightSource.centerBound +
            leftSource.centerBound *
              CCL.FiniteGeometric.quarterRadius 4 earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          (sampledProductErrorScale left right) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        dsimp only [leftSource, rightSource]
        unfold sampledProductErrorScale
        ring1
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      (sampledProductErrorScale left right) current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      (sampledProductErrorScale left right) current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      (sampledProductErrorScale left right)
      (sampledProductErrorScale_nonneg left right)
  centerBound :=
    (CCL.ProgressiveSampling.approximation left).centerBound *
      (CCL.ProgressiveSampling.approximation right).centerBound
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (CCL.ProgressiveSampling.approximation left).centerBound_nonneg
      (CCL.ProgressiveSampling.approximation right).centerBound_nonneg
  sample_bounded := by
    intro index
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      ((CCL.ProgressiveSampling.approximation left).sample_bounded
        index)
      ((CCL.ProgressiveSampling.approximation right).sample_bounded
        index)
      (normSq_nonneg _)
      (CCL.ProgressiveSampling.approximation left).centerBound_nonneg

@[simp] theorem sampledProductApproximation_sample
    (left right : Named) (index : Nat) :
    (sampledProductApproximation left right).sample index =
      (CCL.ProgressiveSampling.approximation left).sample index *
      (CCL.ProgressiveSampling.approximation right).sample index :=
  rfl

def sampledTripleErrorScale (left middle right : Named) : Coordinate :=
  2 *
    (sampledProductErrorScale left middle *
        (CCL.ProgressiveSampling.approximation right).centerBound +
      ((CCL.ProgressiveSampling.approximation left).centerBound *
          (CCL.ProgressiveSampling.approximation middle).centerBound) *
        4)

theorem sampledTripleErrorScale_nonneg (left middle right : Named) :
    0 ≤ sampledTripleErrorScale left middle right := by
  unfold sampledTripleErrorScale
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (sampledProductErrorScale_nonneg left middle)
        (CCL.ProgressiveSampling.approximation right).centerBound_nonneg)
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (CCL.ProgressiveSampling.approximation left).centerBound_nonneg
          (CCL.ProgressiveSampling.approximation middle).centerBound_nonneg)
        (by decide)))

/-- A canonical equal-index approximation to the product of three arbitrary
CCL names.  It is deliberately parenthesized on the left; Gaussian
associativity lets either actual multiplication tree use the same target. -/
def sampledTripleApproximation (left middle right : Named) : Approximation where
  sample index :=
    ((CCL.ProgressiveSampling.approximation left).sample index *
      (CCL.ProgressiveSampling.approximation middle).sample index) *
        (CCL.ProgressiveSampling.approximation right).sample index
  radiusSq := CCL.FiniteGeometric.quarterRadius
    (sampledTripleErrorScale left middle right)
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      (sampledTripleErrorScale_nonneg left middle right)
  later_close := by
    intro earlier later order
    let leftMiddle := sampledProductApproximation left middle
    let rightSource := CCL.ProgressiveSampling.approximation right
    have leftMiddleMovement := leftMiddle.later_close order
    have rightMovement := rightSource.later_close order
    have firstTerm :
        normSq
            ((leftMiddle.sample later - leftMiddle.sample earlier) *
              rightSource.sample later) ≤
          CCL.FiniteGeometric.quarterRadius
              (sampledProductErrorScale left middle) earlier *
            rightSource.centerBound := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct leftMiddleMovement
        (rightSource.sample_bounded later) (normSq_nonneg _)
        (CCL.FiniteGeometric.quarterRadius_nonneg
          (sampledProductErrorScale_nonneg left middle) _)
    have secondTerm :
        normSq
            (leftMiddle.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
          leftMiddle.centerBound *
            CCL.FiniteGeometric.quarterRadius 4 earlier := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct
        (leftMiddle.sample_bounded earlier) rightMovement (normSq_nonneg _)
        leftMiddle.centerBound_nonneg
    have identity :
        leftMiddle.sample later * rightSource.sample later -
            leftMiddle.sample earlier * rightSource.sample earlier =
          (leftMiddle.sample later - leftMiddle.sample earlier) *
              rightSource.sample later +
            leftMiddle.sample earlier *
              (rightSource.sample later - rightSource.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
    change normSq
        (leftMiddle.sample later * rightSource.sample later -
          leftMiddle.sample earlier * rightSource.sample earlier) ≤
      CCL.FiniteGeometric.quarterRadius
        (sampledTripleErrorScale left middle right) earlier
    rw [identity]
    calc
      normSq
          ((leftMiddle.sample later - leftMiddle.sample earlier) *
              rightSource.sample later +
            leftMiddle.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
        2 *
          (normSq
              ((leftMiddle.sample later - leftMiddle.sample earlier) *
                rightSource.sample later) +
            normSq
              (leftMiddle.sample earlier *
                (rightSource.sample later - rightSource.sample earlier))) :=
        normSq_add_le_two _ _
      _ ≤ 2 *
          (CCL.FiniteGeometric.quarterRadius
                (sampledProductErrorScale left middle) earlier *
              rightSource.centerBound +
            leftMiddle.centerBound *
              CCL.FiniteGeometric.quarterRadius 4 earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          (sampledTripleErrorScale left middle right) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        dsimp only [leftMiddle, rightSource, sampledProductApproximation]
        unfold sampledTripleErrorScale
        ring1
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      (sampledTripleErrorScale left middle right) current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      (sampledTripleErrorScale left middle right) current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      (sampledTripleErrorScale left middle right)
      (sampledTripleErrorScale_nonneg left middle right)
  centerBound :=
    ((CCL.ProgressiveSampling.approximation left).centerBound *
      (CCL.ProgressiveSampling.approximation middle).centerBound) *
        (CCL.ProgressiveSampling.approximation right).centerBound
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.ProgressiveSampling.approximation left).centerBound_nonneg
        (CCL.ProgressiveSampling.approximation middle).centerBound_nonneg)
      (CCL.ProgressiveSampling.approximation right).centerBound_nonneg
  sample_bounded := by
    intro index
    rw [normSq_mul, normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (RFAP.ConstructiveFraction.mul_le_mul_direct
        ((CCL.ProgressiveSampling.approximation left).sample_bounded
          index)
        ((CCL.ProgressiveSampling.approximation middle).sample_bounded
          index)
        (normSq_nonneg _)
        (CCL.ProgressiveSampling.approximation left).centerBound_nonneg)
      ((CCL.ProgressiveSampling.approximation right).sample_bounded
        index)
      (normSq_nonneg _)
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.ProgressiveSampling.approximation left).centerBound_nonneg
        (CCL.ProgressiveSampling.approximation middle).centerBound_nonneg)

@[simp] theorem sampledTripleApproximation_sample
    (left middle right : Named) (index : Nat) :
    (sampledTripleApproximation left middle right).sample index =
      ((CCL.ProgressiveSampling.approximation left).sample index *
        (CCL.ProgressiveSampling.approximation middle).sample index) *
          (CCL.ProgressiveSampling.approximation right).sample index :=
  rfl

/-- Canonical finite products respect operational equivalence in both
operands. -/
def sampledProductApproximation_respects
    {leftOne leftTwo rightOne rightTwo : Named}
    (leftEquivalent : NamedEquivalent leftOne leftTwo)
    (rightEquivalent : NamedEquivalent rightOne rightTwo) :
    Equivalent
      (sampledProductApproximation leftOne rightOne)
      (sampledProductApproximation leftTwo rightTwo) where
  compare := by
    intro firstStart secondStart target positive
    let firstLeftSource :=
      CCL.ProgressiveSampling.approximation leftOne
    let secondLeftSource :=
      CCL.ProgressiveSampling.approximation leftTwo
    let firstRightSource :=
      CCL.ProgressiveSampling.approximation rightOne
    let secondRightSource :=
      CCL.ProgressiveSampling.approximation rightTwo
    let inputTarget := approximationMulBridgeTarget
      firstRightSource secondLeftSource target
    have inputPositive : 0 < inputTarget :=
      approximationMulBridgeTarget_pos _ _ positive
    let leftComparison := leftEquivalent.compare firstStart secondStart
      inputTarget inputPositive
    let rightComparison := rightEquivalent.compare firstStart secondStart
      inputTarget inputPositive
    let firstIndex := max leftComparison.leftIndex rightComparison.leftIndex
    let secondIndex := max leftComparison.rightIndex rightComparison.rightIndex
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := leftComparison.left_ge.trans
          (Nat.le_max_left _ _)
        right_ge := leftComparison.right_ge.trans
          (Nat.le_max_left _ _)
        close := by
          intro firstLater secondLater firstOrder secondOrder
          have leftClose := leftComparison.close
            ((Nat.le_max_left leftComparison.leftIndex
              rightComparison.leftIndex).trans firstOrder)
            ((Nat.le_max_left leftComparison.rightIndex
              rightComparison.rightIndex).trans secondOrder)
          have rightClose := rightComparison.close
            ((Nat.le_max_right leftComparison.leftIndex
              rightComparison.leftIndex).trans firstOrder)
            ((Nat.le_max_right leftComparison.rightIndex
              rightComparison.rightIndex).trans secondOrder)
          have firstTerm :
              normSq
                  ((firstLeftSource.sample firstLater -
                      secondLeftSource.sample secondLater) *
                    firstRightSource.sample firstLater) ≤
                normSq
                    (firstLeftSource.sample firstLater -
                      secondLeftSource.sample secondLater) *
                  firstRightSource.centerBound := by
            rw [normSq_mul]
            exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (firstRightSource.sample_bounded firstLater) (normSq_nonneg _)
          have secondTerm :
              normSq
                  (secondLeftSource.sample secondLater *
                    (firstRightSource.sample firstLater -
                      secondRightSource.sample secondLater)) ≤
                secondLeftSource.centerBound *
                  normSq
                    (firstRightSource.sample firstLater -
                      secondRightSource.sample secondLater) := by
            rw [normSq_mul]
            exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              (secondLeftSource.sample_bounded secondLater) (normSq_nonneg _)
          have identity :
              firstLeftSource.sample firstLater *
                    firstRightSource.sample firstLater -
                  secondLeftSource.sample secondLater *
                    secondRightSource.sample secondLater =
                (firstLeftSource.sample firstLater -
                    secondLeftSource.sample secondLater) *
                    firstRightSource.sample firstLater +
                  secondLeftSource.sample secondLater *
                    (firstRightSource.sample firstLater -
                      secondRightSource.sample secondLater) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
                ring1
          change normSq
              (firstLeftSource.sample firstLater *
                    firstRightSource.sample firstLater -
                secondLeftSource.sample secondLater *
                    secondRightSource.sample secondLater) < target
          rw [identity]
          calc
            normSq
                ((firstLeftSource.sample firstLater -
                    secondLeftSource.sample secondLater) *
                    firstRightSource.sample firstLater +
                  secondLeftSource.sample secondLater *
                    (firstRightSource.sample firstLater -
                      secondRightSource.sample secondLater)) ≤
              2 *
                (normSq
                    ((firstLeftSource.sample firstLater -
                        secondLeftSource.sample secondLater) *
                      firstRightSource.sample firstLater) +
                  normSq
                    (secondLeftSource.sample secondLater *
                      (firstRightSource.sample firstLater -
                        secondRightSource.sample secondLater))) :=
              normSq_add_le_two _ _
            _ ≤ 2 *
                (inputTarget * firstRightSource.centerBound +
                  secondLeftSource.centerBound * inputTarget) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (add_le_add
                  (firstTerm.trans
                    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                      leftClose.le firstRightSource.centerBound_nonneg))
                  (secondTerm.trans
                    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      rightClose.le secondLeftSource.centerBound_nonneg)))
                (by decide)
            _ = inputTarget *
                (2 * (firstRightSource.centerBound +
                  secondLeftSource.centerBound)) := by ring1
            _ ≤ inputTarget *
                approximationMulBridgeCoefficient
                  firstRightSource secondLeftSource := by
              apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              · unfold approximationMulBridgeCoefficient
                have nonnegative :
                    0 ≤ 8 +
                        2 * (firstRightSource.centerBound +
                          secondLeftSource.centerBound) :=
                  add_nonneg (by decide)
                    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                      (add_nonneg firstRightSource.centerBound_nonneg
                        secondLeftSource.centerBound_nonneg))
                apply sub_nonneg.mp
                convert nonnegative using 1
                ring1
              · exact inputPositive.le
            _ < target :=
              approximationMulBridgeTarget_budget_lt _ _ positive }

private theorem coherentProduct_refine_component_allowance_lt
    {leftProcess rightProcess : Process}
    (leftCoherent : Coherent leftProcess)
    (rightCoherent : Coherent rightProcess)
    (state : leftProcess.State × rightProcess.State)
    (request : Coordinate) (requestPositive : 0 < request)
    (target : Coordinate) (targetPositive : 0 < target)
    (leftRequestSmall : request < leftCoherent.accuracyRequest target)
    (rightRequestSmall : request < rightCoherent.accuracyRequest target) :
    let refined := (leftProcess.mul rightProcess).refine
      state request requestPositive
    leftCoherent.allowance refined.1 < target ∧
      rightCoherent.allowance refined.2 < target := by
  let leftName := CCL.ProgressiveEnclosures.Name.centerOnly
    (leftProcess.ball state.1).center leftProcess.centerBound
      leftProcess.centerBound_nonneg (leftProcess.center_bounded state.1)
  let rightName := CCL.ProgressiveEnclosures.Name.centerOnly
    (rightProcess.ball state.2).center rightProcess.centerBound
      rightProcess.centerBound_nonneg (rightProcess.center_bounded state.2)
  let inputRequest :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget
      leftName rightName request
  have inputPositive : 0 < inputRequest :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget_pos
      leftName rightName requestPositive
  have inputLtRequest : inputRequest < request :=
    CCL.ProgressiveCoherence.Coherent.processMultiplicativeInputTarget_lt_target
      leftName rightName requestPositive
  change leftCoherent.allowance
        (leftProcess.refine state.1 inputRequest inputPositive) < target ∧
      rightCoherent.allowance
        (rightProcess.refine state.2 inputRequest inputPositive) < target
  exact ⟨leftCoherent.refine_accurate state.1 target targetPositive
      inputRequest inputPositive (inputLtRequest.trans leftRequestSmall),
    rightCoherent.refine_accurate state.2 target targetPositive
      inputRequest inputPositive (inputLtRequest.trans rightRequestSmall)⟩

private theorem coherentProduct_stateAt_component_allowance_lt
    {leftProcess rightProcess : Process}
    (leftCoherent : Coherent leftProcess)
    (rightCoherent : Coherent rightProcess)
    (start : leftProcess.State × rightProcess.State) (index : Nat)
    (target : Coordinate) (targetPositive : 0 < target)
    (leftRequestSmall :
      CCL.ProgressiveSampling.refinementTarget index <
        leftCoherent.accuracyRequest target)
    (rightRequestSmall :
      CCL.ProgressiveSampling.refinementTarget index <
        rightCoherent.accuracyRequest target) :
    let state := CCL.ProgressiveSampling.stateAt
      (leftProcess.mul rightProcess) start index
    leftCoherent.allowance state.1 < target ∧
      rightCoherent.allowance state.2 < target := by
  cases index with
  | zero =>
      exact coherentProduct_refine_component_allowance_lt
        leftCoherent rightCoherent start _ _ target targetPositive
          leftRequestSmall rightRequestSmall
  | succ index =>
      exact coherentProduct_refine_component_allowance_lt
        leftCoherent rightCoherent
          (CCL.ProgressiveSampling.stateAt
            (leftProcess.mul rightProcess) start index) _ _ target
              targetPositive leftRequestSmall rightRequestSmall

def coherentProductBridgeCoefficient (left right : Process) : Coordinate :=
  8 + 4 *
    (8 *
      (2 * (1 + left.centerBound) + 2 * (1 + right.centerBound)))

theorem coherentProductBridgeCoefficient_pos (left right : Process) :
    0 < coherentProductBridgeCoefficient left right := by
  unfold coherentProductBridgeCoefficient
  exact add_pos_of_pos_of_nonneg (by decide)
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg (by decide) left.centerBound_nonneg))
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg (by decide) right.centerBound_nonneg)))))

def coherentProductBridgeTarget (left right : Process)
    (target : Coordinate) : Coordinate :=
  target / (target + coherentProductBridgeCoefficient left right)

theorem coherentProductBridgeTarget_pos (left right : Process)
    {target : Coordinate} (positive : 0 < target) :
    0 < coherentProductBridgeTarget left right target :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (add_pos positive (coherentProductBridgeCoefficient_pos left right))

theorem coherentProductBridgeTarget_lt_one (left right : Process)
    {target : Coordinate} (positive : 0 < target) :
    coherentProductBridgeTarget left right target < 1 := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos positive (coherentProductBridgeCoefficient_pos left right))).2
  calc
    target = 0 + target :=
      (RFAP.ConstructiveFraction.zero_add target).symm
    _ < coherentProductBridgeCoefficient left right + target :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct
        (coherentProductBridgeCoefficient_pos left right) target
    _ = target + coherentProductBridgeCoefficient left right :=
      RFAP.ConstructiveFraction.add_comm _ _
    _ = 1 * (target + coherentProductBridgeCoefficient left right) :=
      (RFAP.ConstructiveFraction.one_mul _).symm

theorem coherentProductBridgeTarget_budget_lt (left right : Process)
    {target : Coordinate} (positive : 0 < target) :
    coherentProductBridgeTarget left right target *
        coherentProductBridgeCoefficient left right < target := by
  have denominatorPositive :
      0 < target + coherentProductBridgeCoefficient left right :=
    add_pos positive (coherentProductBridgeCoefficient_pos left right)
  change target / (target + coherentProductBridgeCoefficient left right) *
      coherentProductBridgeCoefficient left right < target
  calc
    target / (target + coherentProductBridgeCoefficient left right) *
        coherentProductBridgeCoefficient left right =
      (target * coherentProductBridgeCoefficient left right) /
        (target + coherentProductBridgeCoefficient left right) := by
      change (target *
          (target + coherentProductBridgeCoefficient left right)⁻¹) *
            coherentProductBridgeCoefficient left right =
        (target * coherentProductBridgeCoefficient left right) *
          (target + coherentProductBridgeCoefficient left right)⁻¹
      calc
        (target *
            (target + coherentProductBridgeCoefficient left right)⁻¹) *
              coherentProductBridgeCoefficient left right =
          target *
            ((target + coherentProductBridgeCoefficient left right)⁻¹ *
              coherentProductBridgeCoefficient left right) :=
            _root_.mul_assoc _ _ _
        _ = target *
            (coherentProductBridgeCoefficient left right *
              (target + coherentProductBridgeCoefficient left right)⁻¹) := by
          rw [RFAP.ConstructiveFraction.mul_comm
            (target + coherentProductBridgeCoefficient left right)⁻¹]
        _ = (target * coherentProductBridgeCoefficient left right) *
            (target + coherentProductBridgeCoefficient left right)⁻¹ :=
          (_root_.mul_assoc _ _ _).symm
    _ < target := by
      apply (RFAP.ConstructiveFraction.div_lt_iff_pos
        denominatorPositive).2
      have coefficientLt : coherentProductBridgeCoefficient left right <
          target + coherentProductBridgeCoefficient left right := by
        calc
          coherentProductBridgeCoefficient left right =
              0 + coherentProductBridgeCoefficient left right :=
            (RFAP.ConstructiveFraction.zero_add _).symm
          _ < target + coherentProductBridgeCoefficient left right :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct positive _
      exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive coefficientLt

/-- Actual stateful multiplication of two coherent names is operationally
equivalent to their canonical equal-index sampled product. -/
def coherentMul_toNamed (left right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul left.name right.name)
      (sampledProductApproximation left.name right.name).toNamed := by
  let leftProcess := left.name.process
  let rightProcess := right.name.process
  let process := leftProcess.mul rightProcess
  let start : process.State := (left.name.state, right.name.state)
  let product := sampledProductApproximation left.name right.name
  let bridge : Equivalent
      (CCL.ProgressiveSampling.approximation
        (CCL.ProgressiveTransducer.Named.mul
          left.name right.name)) product :=
    { compare := by
        intro leftStart rightStart target positive
        let semanticTarget := coherentProductBridgeTarget
          leftProcess rightProcess target
        have semanticPositive : 0 < semanticTarget :=
          coherentProductBridgeTarget_pos leftProcess rightProcess positive
        have semanticLtOne : semanticTarget < 1 :=
          coherentProductBridgeTarget_lt_one leftProcess rightProcess positive
        let leftThreshold := left.coherent.accuracyRequest semanticTarget
        let rightThreshold := right.coherent.accuracyRequest semanticTarget
        have leftThresholdPositive : 0 < leftThreshold :=
          left.coherent.accuracyRequest_pos semanticPositive
        have rightThresholdPositive : 0 < rightThreshold :=
          right.coherent.accuracyRequest_pos semanticPositive
        let inputThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest
            leftThreshold rightThreshold
        have inputThresholdPositive : 0 < inputThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest_pos
            leftThresholdPositive rightThresholdPositive
        let outputThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest
            inputThreshold semanticTarget
        have outputThresholdPositive : 0 < outputThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest_pos
            inputThresholdPositive semanticPositive
        let leftIndex := CCL.FiniteGeometric.firstQuarterBelow
          1 leftStart outputThreshold
        have leftIndexGe : leftStart ≤ leftIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            1 leftStart outputThreshold
        have outputRequestSmall :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              outputThreshold :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            1 (by decide) leftStart outputThreshold outputThresholdPositive
        have outputRequestLtInput :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              inputThreshold :=
          outputRequestSmall.trans
            (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
              inputThresholdPositive semanticPositive)
        have outputRequestLtSemantic :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              semanticTarget :=
          outputRequestSmall.trans
            (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
              inputThresholdPositive semanticPositive)
        have outputRequestLtLeft :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              leftThreshold :=
          outputRequestLtInput.trans
            (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
              leftThresholdPositive rightThresholdPositive)
        have outputRequestLtRight :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              rightThreshold :=
          outputRequestLtInput.trans
            (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
              leftThresholdPositive rightThresholdPositive)
        let rightIndex := CCL.FiniteGeometric.firstQuarterBelow
          1 rightStart inputThreshold
        have rightIndexGe : rightStart ≤ rightIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            1 rightStart inputThreshold
        have rightRequestSmall :
            CCL.ProgressiveSampling.refinementTarget rightIndex <
              inputThreshold :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            1 (by decide) rightStart inputThreshold inputThresholdPositive
        let baseState := CCL.ProgressiveSampling.stateAt
          process start leftIndex
        have componentSmall :
            left.coherent.allowance baseState.1 < semanticTarget ∧
              right.coherent.allowance baseState.2 < semanticTarget :=
          coherentProduct_stateAt_component_allowance_lt
            left.coherent right.coherent start leftIndex semanticTarget
              semanticPositive outputRequestLtLeft outputRequestLtRight
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := leftIndexGe
            right_ge := rightIndexGe
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have canonicalRequestSmall :
                  CCL.ProgressiveSampling.refinementTarget
                      rightLater < inputThreshold :=
                (quarterRadius_index_antitone (by decide) rightOrder).trans_lt
                  rightRequestSmall
              have canonicalRequestLtLeft :
                  CCL.ProgressiveSampling.refinementTarget
                      rightLater < leftThreshold :=
                canonicalRequestSmall.trans
                  (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
                    leftThresholdPositive rightThresholdPositive)
              have canonicalRequestLtRight :
                  CCL.ProgressiveSampling.refinementTarget
                      rightLater < rightThreshold :=
                canonicalRequestSmall.trans
                  (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
                    leftThresholdPositive rightThresholdPositive)
              have canonicalLeftSmall :
                  left.coherent.allowance
                      (CCL.ProgressiveSampling.stateAt leftProcess
                        left.name.state rightLater) < semanticTarget :=
                CCL.ProgressiveCoherence.Coherent.stateAt_allowance_lt
                  left.coherent left.name.state
                    rightLater semanticTarget semanticPositive
                      canonicalRequestLtLeft
              have canonicalRightSmall :
                  right.coherent.allowance
                      (CCL.ProgressiveSampling.stateAt rightProcess
                        right.name.state rightLater) < semanticTarget :=
                CCL.ProgressiveCoherence.Coherent.stateAt_allowance_lt
                  right.coherent right.name.state
                    rightLater semanticTarget semanticPositive
                      canonicalRequestLtRight
              let leftReading := (leftProcess.witness baseState.1).val
              let rightReading := (rightProcess.witness baseState.2).val
              let canonicalLeft :=
                CCL.ProgressiveSampling.witnessAt leftProcess
                  left.name.state rightLater
              let canonicalRight :=
                CCL.ProgressiveSampling.witnessAt rightProcess
                  right.name.state rightLater
              have leftPossible :
                  leftProcess.Possible baseState.1 leftReading :=
                (leftProcess.witness baseState.1).property
              have rightPossible :
                  rightProcess.Possible baseState.2 rightReading :=
                (rightProcess.witness baseState.2).property
              have canonicalLeftPossible :
                  leftProcess.Possible
                      (CCL.ProgressiveSampling.stateAt leftProcess
                        left.name.state rightLater) canonicalLeft :=
                CCL.ProgressiveSampling.witnessAt_possible
                  leftProcess left.name.state rightLater
              have canonicalRightPossible :
                  rightProcess.Possible
                      (CCL.ProgressiveSampling.stateAt rightProcess
                        right.name.state rightLater) canonicalRight :=
                CCL.ProgressiveSampling.witnessAt_possible
                  rightProcess right.name.state rightLater
              have leftCloseRaw := left.coherent.possible_close
                leftPossible canonicalLeftPossible
              have rightCloseRaw := right.coherent.possible_close
                rightPossible canonicalRightPossible
              have leftClose : normSq (leftReading - canonicalLeft) ≤
                  8 * semanticTarget := by
                calc
                  normSq (leftReading - canonicalLeft) ≤
                    4 *
                      (left.coherent.allowance baseState.1 +
                        left.coherent.allowance
                          (CCL.ProgressiveSampling.stateAt
                            leftProcess left.name.state rightLater)) :=
                    leftCloseRaw
                  _ ≤ 4 * (semanticTarget + semanticTarget) :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      (add_le_add componentSmall.1.le canonicalLeftSmall.le)
                      (by decide)
                  _ = 8 * semanticTarget := by ring1
              have rightClose : normSq (rightReading - canonicalRight) ≤
                  8 * semanticTarget := by
                calc
                  normSq (rightReading - canonicalRight) ≤
                    4 *
                      (right.coherent.allowance baseState.2 +
                        right.coherent.allowance
                          (CCL.ProgressiveSampling.stateAt
                            rightProcess right.name.state rightLater)) :=
                    rightCloseRaw
                  _ ≤ 4 * (semanticTarget + semanticTarget) :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      (add_le_add componentSmall.2.le canonicalRightSmall.le)
                      (by decide)
                  _ = 8 * semanticTarget := by ring1
              let leftBound := 2 * (1 + leftProcess.centerBound)
              let rightBound := 2 * (1 + rightProcess.centerBound)
              have rightAllowanceBound :
                  right.coherent.allowance baseState.2 +
                      rightProcess.centerBound ≤
                    1 + rightProcess.centerBound := by
                calc
                  right.coherent.allowance baseState.2 +
                      rightProcess.centerBound =
                    rightProcess.centerBound +
                      right.coherent.allowance baseState.2 :=
                    RFAP.ConstructiveFraction.add_comm _ _
                  _ ≤ rightProcess.centerBound + semanticTarget :=
                    add_le_add_right componentSmall.2.le _
                  _ ≤ rightProcess.centerBound + 1 :=
                    add_le_add_right semanticLtOne.le _
                  _ = 1 + rightProcess.centerBound :=
                    RFAP.ConstructiveFraction.add_comm _ _
              have canonicalLeftAllowanceBound :
                  left.coherent.allowance
                      (CCL.ProgressiveSampling.stateAt leftProcess
                        left.name.state rightLater) + leftProcess.centerBound ≤
                    1 + leftProcess.centerBound := by
                calc
                  left.coherent.allowance
                        (CCL.ProgressiveSampling.stateAt leftProcess
                          left.name.state rightLater) + leftProcess.centerBound =
                    leftProcess.centerBound +
                      left.coherent.allowance
                        (CCL.ProgressiveSampling.stateAt leftProcess
                          left.name.state rightLater) :=
                    RFAP.ConstructiveFraction.add_comm _ _
                  _ ≤ leftProcess.centerBound + semanticTarget :=
                    add_le_add_right canonicalLeftSmall.le _
                  _ ≤ leftProcess.centerBound + 1 :=
                    add_le_add_right semanticLtOne.le _
                  _ = 1 + leftProcess.centerBound :=
                    RFAP.ConstructiveFraction.add_comm _ _
              have rightReadingNorm : normSq rightReading ≤ rightBound :=
                (CCL.ProgressiveCoherence.Coherent.possible_normSq_le
                  right.coherent rightPossible).trans
                    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      rightAllowanceBound (by decide))
              have canonicalLeftNorm : normSq canonicalLeft ≤ leftBound :=
                (CCL.ProgressiveCoherence.Coherent.possible_normSq_le
                  left.coherent
                    canonicalLeftPossible).trans
                      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                          canonicalLeftAllowanceBound (by decide))
              have firstTerm :
                  normSq ((leftReading - canonicalLeft) * rightReading) ≤
                    (8 * semanticTarget) * rightBound := by
                rw [normSq_mul]
                exact RFAP.ConstructiveFraction.mul_le_mul_direct
                  leftClose rightReadingNorm (normSq_nonneg _)
                  (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                    semanticPositive.le)
              have secondTerm :
                  normSq
                      (canonicalLeft * (rightReading - canonicalRight)) ≤
                    leftBound * (8 * semanticTarget) := by
                rw [normSq_mul]
                exact RFAP.ConstructiveFraction.mul_le_mul_direct
                  canonicalLeftNorm rightClose (normSq_nonneg _)
                  (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                    (add_nonneg (by decide) leftProcess.centerBound_nonneg))
              have productIdentity :
                  leftReading * rightReading -
                      canonicalLeft * canonicalRight =
                    (leftReading - canonicalLeft) * rightReading +
                      canonicalLeft * (rightReading - canonicalRight) := by
                apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                  simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
                    ring1
              have productBound :
                  normSq
                      (leftReading * rightReading -
                        canonicalLeft * canonicalRight) ≤
                    16 * semanticTarget * (leftBound + rightBound) := by
                rw [productIdentity]
                calc
                  normSq
                      ((leftReading - canonicalLeft) * rightReading +
                        canonicalLeft * (rightReading - canonicalRight)) ≤
                    2 *
                      (normSq
                          ((leftReading - canonicalLeft) * rightReading) +
                        normSq
                          (canonicalLeft *
                            (rightReading - canonicalRight))) :=
                    normSq_add_le_two _ _
                  _ ≤ 2 *
                      ((8 * semanticTarget) * rightBound +
                        leftBound * (8 * semanticTarget)) :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      (add_le_add firstTerm secondTerm) (by decide)
                  _ = 16 * semanticTarget * (leftBound + rightBound) := by
                    ring1
              have actualTail :
                  normSq
                      (CCL.ProgressiveSampling.witnessAt process
                          start leftLater -
                        CCL.ProgressiveSampling.witnessAt process
                          start leftIndex) ≤
                    4 * CCL.ProgressiveSampling.refinementTarget
                      leftIndex := by
                rw [← quarterRadius_four_eq_four_refinementTarget]
                exact CCL.ProgressiveSampling.witnessAt_later_close
                  process start leftOrder
              have baseWitness :
                  CCL.ProgressiveSampling.witnessAt process
                      start leftIndex = leftReading * rightReading :=
                rfl
              have canonicalLeftSample :
                  (CCL.ProgressiveSampling.approximation left.name).sample
                      rightLater = canonicalLeft :=
                rfl
              have canonicalRightSample :
                  (CCL.ProgressiveSampling.approximation right.name).sample
                      rightLater = canonicalRight :=
                rfl
              change normSq
                  (CCL.ProgressiveSampling.witnessAt process
                      start leftLater - product.sample rightLater) < target
              rw [sampledProductApproximation_sample,
                canonicalLeftSample, canonicalRightSample]
              calc
                normSq
                    (CCL.ProgressiveSampling.witnessAt process
                        start leftLater - canonicalLeft * canonicalRight) ≤
                  2 *
                    (normSq
                        (CCL.ProgressiveSampling.witnessAt process
                            start leftLater -
                          CCL.ProgressiveSampling.witnessAt process
                            start leftIndex) +
                      normSq
                        (CCL.ProgressiveSampling.witnessAt process
                            start leftIndex -
                          canonicalLeft * canonicalRight)) :=
                    normSq_sub_le_via _ _ _
                _ ≤ 2 *
                    (4 *
                        CCL.ProgressiveSampling.refinementTarget
                          leftIndex +
                      16 * semanticTarget * (leftBound + rightBound)) := by
                  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                  · apply add_le_add actualTail
                    rw [baseWitness]
                    exact productBound
                  · decide
                _ ≤ 2 *
                    (4 * semanticTarget +
                      16 * semanticTarget * (leftBound + rightBound)) :=
                  RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                    (add_le_add
                      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                          outputRequestLtSemantic.le (by decide)) le_rfl)
                    (by decide)
                _ = semanticTarget *
                    coherentProductBridgeCoefficient
                      leftProcess rightProcess := by
                  dsimp only [leftBound, rightBound]
                  unfold coherentProductBridgeCoefficient
                  ring1
                _ < target :=
                  coherentProductBridgeTarget_budget_lt
                    leftProcess rightProcess positive } }
  exact CCL.OperationalEquivalence.Equivalent.trans bridge
    (CCL.OperationalEquivalence.Equivalent.symm
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
        product))

/-- Stateful multiplication respects operational equality independently in
both coherent operands. -/
def coherentMul_respects
    (leftOne leftTwo rightOne rightTwo : CoherentNamed)
    (leftEquivalent : NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : NamedEquivalent rightOne.name rightTwo.name) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        leftOne.name rightOne.name)
      (CCL.ProgressiveTransducer.Named.mul
        leftTwo.name rightTwo.name) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentMul_toNamed leftOne rightOne)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (approximationEquivalent_toNamed
        (sampledProductApproximation_respects
          leftEquivalent rightEquivalent))
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (coherentMul_toNamed leftTwo rightTwo)))

private theorem twenty_four_thirty_seconds_lt {target : Coordinate}
    (positive : 0 < target) : 24 * (target / 32) < target := by
  have scalarOrder : (24 / 32 : Coordinate) < 1 := by decide
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    scalarOrder positive
  calc
    24 * (target / 32) = (24 / 32 : Coordinate) * target := by
      rw [RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ExplicitField.div_eq_mul_inv]
      ring1
    _ < 1 * target := scaled
    _ = target := RFAP.ConstructiveFraction.one_mul _

/-- Actual stateful addition of two coherent names is operationally
equivalent to their canonical equal-index sampled sum. -/
def coherentAdd_toNamed (left right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add left.name right.name)
      (sampledSumApproximation left.name right.name).toNamed := by
  let leftProcess := left.name.process
  let rightProcess := right.name.process
  let process := leftProcess.add rightProcess
  let start : process.State := (left.name.state, right.name.state)
  let coherent := CCL.ProgressiveCoherence.Coherent.add
    left.coherent right.coherent
  let sum := sampledSumApproximation left.name right.name
  let bridge : Equivalent
      (CCL.ProgressiveSampling.approximation
        (CCL.ProgressiveTransducer.Named.add
          left.name right.name)) sum :=
    { compare := by
        intro leftStart rightStart target positive
        let semanticTarget := target / 32
        have semanticPositive : 0 < semanticTarget :=
          RFAP.ConstructiveFraction.div_pos_direct positive
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (n := 32) (by decide))
        let componentTarget := semanticTarget / 4
        have componentPositive : 0 < componentTarget :=
          RFAP.ConstructiveFraction.div_pos_direct semanticPositive
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (n := 4) (by decide))
        let actualThreshold := coherent.accuracyRequest semanticTarget
        let leftThreshold := left.coherent.accuracyRequest componentTarget
        let rightThreshold := right.coherent.accuracyRequest componentTarget
        have actualThresholdPositive : 0 < actualThreshold :=
          coherent.accuracyRequest_pos semanticPositive
        have leftThresholdPositive : 0 < leftThreshold :=
          left.coherent.accuracyRequest_pos componentPositive
        have rightThresholdPositive : 0 < rightThreshold :=
          right.coherent.accuracyRequest_pos componentPositive
        let componentThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest
            leftThreshold rightThreshold
        have componentThresholdPositive : 0 < componentThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest_pos
            leftThresholdPositive rightThresholdPositive
        let inputThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest
            actualThreshold componentThreshold
        have inputThresholdPositive : 0 < inputThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest_pos
            actualThresholdPositive componentThresholdPositive
        let outputThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest
            inputThreshold semanticTarget
        have outputThresholdPositive : 0 < outputThreshold :=
          CCL.ProgressiveCoherence.Coherent.commonRequest_pos
            inputThresholdPositive semanticPositive
        let leftIndex := CCL.FiniteGeometric.firstQuarterBelow
          1 leftStart outputThreshold
        have leftIndexGe : leftStart ≤ leftIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            1 leftStart outputThreshold
        have outputRequestSmall :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              outputThreshold :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            1 (by decide) leftStart outputThreshold outputThresholdPositive
        have outputRequestLtInput :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              inputThreshold :=
          outputRequestSmall.trans
            (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
              inputThresholdPositive semanticPositive)
        have outputRequestLtActual :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              actualThreshold :=
          outputRequestLtInput.trans
            (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
              actualThresholdPositive componentThresholdPositive)
        have outputRequestLtSemantic :
            CCL.ProgressiveSampling.refinementTarget leftIndex <
              semanticTarget :=
          outputRequestSmall.trans
            (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
              inputThresholdPositive semanticPositive)
        let rightIndex := CCL.FiniteGeometric.firstQuarterBelow
          1 rightStart componentThreshold
        have rightIndexGe : rightStart ≤ rightIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            1 rightStart componentThreshold
        have rightRequestSmall :
            CCL.ProgressiveSampling.refinementTarget rightIndex <
              componentThreshold :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            1 (by decide) rightStart componentThreshold
              componentThresholdPositive
        let baseState := CCL.ProgressiveSampling.stateAt
          process start leftIndex
        have baseAllowanceSmall :
            coherent.allowance baseState < semanticTarget :=
          CCL.ProgressiveCoherence.Coherent.stateAt_allowance_lt
            coherent start leftIndex semanticTarget semanticPositive
              outputRequestLtActual
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := leftIndexGe
            right_ge := rightIndexGe
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have canonicalRequestSmall :
                  CCL.ProgressiveSampling.refinementTarget
                      rightLater < componentThreshold :=
                (quarterRadius_index_antitone (by decide) rightOrder).trans_lt
                  rightRequestSmall
              have canonicalRequestLtLeft :
                  CCL.ProgressiveSampling.refinementTarget
                      rightLater < leftThreshold :=
                canonicalRequestSmall.trans
                  (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
                    leftThresholdPositive rightThresholdPositive)
              have canonicalRequestLtRight :
                  CCL.ProgressiveSampling.refinementTarget
                      rightLater < rightThreshold :=
                canonicalRequestSmall.trans
                  (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
                    leftThresholdPositive rightThresholdPositive)
              let canonicalLeftState :=
                CCL.ProgressiveSampling.stateAt leftProcess
                  left.name.state rightLater
              let canonicalRightState :=
                CCL.ProgressiveSampling.stateAt rightProcess
                  right.name.state rightLater
              have canonicalLeftSmall :
                  left.coherent.allowance canonicalLeftState < componentTarget :=
                CCL.ProgressiveCoherence.Coherent.stateAt_allowance_lt
                  left.coherent left.name.state rightLater componentTarget
                    componentPositive canonicalRequestLtLeft
              have canonicalRightSmall :
                  right.coherent.allowance canonicalRightState < componentTarget :=
                CCL.ProgressiveCoherence.Coherent.stateAt_allowance_lt
                  right.coherent right.name.state rightLater componentTarget
                    componentPositive canonicalRequestLtRight
              have canonicalAllowanceSmall :
                  coherent.allowance
                      (canonicalLeftState, canonicalRightState) <
                    semanticTarget := by
                change 2 *
                    (left.coherent.allowance canonicalLeftState +
                      right.coherent.allowance canonicalRightState) <
                  semanticTarget
                calc
                  2 *
                      (left.coherent.allowance canonicalLeftState +
                        right.coherent.allowance canonicalRightState) <
                    2 * (componentTarget + componentTarget) :=
                    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                      (by decide)
                      (RFAP.ConstructiveFraction.add_lt_add_direct
                        canonicalLeftSmall canonicalRightSmall)
                  _ = semanticTarget := by
                    dsimp only [componentTarget]
                    exact two_quarter_sums semanticTarget
              let baseReading := (process.witness baseState).val
              let canonicalLeft :=
                CCL.ProgressiveSampling.witnessAt leftProcess
                  left.name.state rightLater
              let canonicalRight :=
                CCL.ProgressiveSampling.witnessAt rightProcess
                  right.name.state rightLater
              have basePossible : process.Possible baseState baseReading :=
                (process.witness baseState).property
              have canonicalLeftPossible :
                  leftProcess.Possible canonicalLeftState canonicalLeft :=
                CCL.ProgressiveSampling.witnessAt_possible
                  leftProcess left.name.state rightLater
              have canonicalRightPossible :
                  rightProcess.Possible canonicalRightState canonicalRight :=
                CCL.ProgressiveSampling.witnessAt_possible
                  rightProcess right.name.state rightLater
              have canonicalPossible :
                  process.Possible (canonicalLeftState, canonicalRightState)
                    (canonicalLeft + canonicalRight) :=
                ⟨canonicalLeft, canonicalRight, canonicalLeftPossible,
                  canonicalRightPossible, rfl⟩
              have baseCanonicalRaw := coherent.possible_close
                basePossible canonicalPossible
              have baseCanonical :
                  normSq (baseReading - (canonicalLeft + canonicalRight)) <
                    8 * semanticTarget := by
                calc
                  normSq (baseReading - (canonicalLeft + canonicalRight)) ≤
                    4 *
                      (coherent.allowance baseState +
                        coherent.allowance
                          (canonicalLeftState, canonicalRightState)) :=
                    baseCanonicalRaw
                  _ < 4 * (semanticTarget + semanticTarget) :=
                    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                      (by decide)
                      (RFAP.ConstructiveFraction.add_lt_add_direct
                        baseAllowanceSmall canonicalAllowanceSmall)
                  _ = 8 * semanticTarget := by ring1
              have actualTail :
                  normSq
                      (CCL.ProgressiveSampling.witnessAt process
                          start leftLater -
                        CCL.ProgressiveSampling.witnessAt process
                          start leftIndex) <
                    4 * semanticTarget := by
                calc
                  normSq
                      (CCL.ProgressiveSampling.witnessAt process
                          start leftLater -
                        CCL.ProgressiveSampling.witnessAt process
                          start leftIndex) ≤
                    4 * CCL.ProgressiveSampling.refinementTarget
                      leftIndex := by
                    rw [← quarterRadius_four_eq_four_refinementTarget]
                    exact
                      CCL.ProgressiveSampling.witnessAt_later_close
                        process start leftOrder
                  _ < 4 * semanticTarget :=
                    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                      (by decide) outputRequestLtSemantic
              have baseWitness :
                  CCL.ProgressiveSampling.witnessAt process
                      start leftIndex = baseReading :=
                rfl
              change normSq
                  (CCL.ProgressiveSampling.witnessAt process
                      start leftLater - sum.sample rightLater) < target
              rw [sampledSumApproximation_sample]
              calc
                normSq
                    (CCL.ProgressiveSampling.witnessAt process
                        start leftLater - (canonicalLeft + canonicalRight)) ≤
                  2 *
                    (normSq
                        (CCL.ProgressiveSampling.witnessAt process
                            start leftLater -
                          CCL.ProgressiveSampling.witnessAt process
                            start leftIndex) +
                      normSq
                        (CCL.ProgressiveSampling.witnessAt process
                            start leftIndex -
                          (canonicalLeft + canonicalRight))) :=
                    normSq_sub_le_via _ _ _
                _ < 2 *
                    (4 * semanticTarget + 8 * semanticTarget) :=
                  RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                    (by decide)
                    (RFAP.ConstructiveFraction.add_lt_add_direct actualTail
                      (by rw [baseWitness]; exact baseCanonical))
                _ = 24 * semanticTarget := by ring1
                _ < target := by
                  dsimp only [semanticTarget]
                  exact twenty_four_thirty_seconds_lt positive } }
  exact CCL.OperationalEquivalence.Equivalent.trans bridge
    (CCL.OperationalEquivalence.Equivalent.symm
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
        sum))

/-- Stateful addition respects operational equality independently in both
coherent operands. -/
def coherentAdd_respects
    (leftOne leftTwo rightOne rightTwo : CoherentNamed)
    (leftEquivalent : NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : NamedEquivalent rightOne.name rightTwo.name) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        leftOne.name rightOne.name)
      (CCL.ProgressiveTransducer.Named.add
        leftTwo.name rightTwo.name) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentAdd_toNamed leftOne rightOne)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (approximationEquivalent_toNamed
        (sampledSumApproximation_respects leftEquivalent rightEquivalent))
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (coherentAdd_toNamed leftTwo rightTwo)))

/-- A unit-disk certificate for an actual coherent sum transfers to the
canonical equal-index sampled-sum wrapper.  Every possible wrapper value is
one explicitly witnessed later sum of possible operand readings. -/
theorem sampledSumUnitDisk (left right : CoherentNamed)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add
        left.name right.name)) :
    CCL.ProgressiveExp.UnitDisk
      (sampledSumApproximation left.name right.name).toNamed where
  possible_unit := by
    intro value possible
    change (sampledSumApproximation left.name right.name).Possible 0 value at possible
    rcases possible with ⟨later, _order, rfl⟩
    rw [sampledSumApproximation_sample]
    apply sumDomain.possible_unit
    exact
      ⟨(CCL.ProgressiveSampling.approximation left.name).sample
          later,
        (CCL.ProgressiveSampling.approximation right.name).sample
          later,
        CCL.ProgressiveSampling.witnessAt_possible_start
          left.name.process left.name.state later,
        CCL.ProgressiveSampling.witnessAt_possible_start
          right.name.process right.name.state later,
        rfl⟩

/-- Local exponential evaluation on an actual coherent sum may be replaced
by evaluation on its canonical sampled-sum wrapper. -/
def localExp_sum_toSampled (left right : CoherentNamed)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add
        left.name right.name)) :
    NamedEquivalent
      (CCL.ProgressiveExp.named
        (CCL.ProgressiveTransducer.Named.add
          left.name right.name) sumDomain)
      (CCL.ProgressiveExp.named
        (sampledSumApproximation left.name right.name).toNamed
        (sampledSumUnitDisk left right sumDomain)) :=
  localExpNamed_respects sumDomain (sampledSumUnitDisk left right sumDomain)
    (coherentAdd_toNamed left right)

def dynamicExpProductErrorScale : Coordinate :=
  40 * CCL.ProgressiveExp.errorScale

theorem dynamicExpProductErrorScale_nonneg :
    0 ≤ dynamicExpProductErrorScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 40) (by decide)).le
    CCL.ProgressiveExp.errorScale_nonneg

/-- Pointwise product of the two dynamic local Horner programs. -/
def dynamicExpProductApproximation {left right : Named}
    (leftDomain : CCL.ProgressiveExp.UnitDisk left)
    (rightDomain : CCL.ProgressiveExp.UnitDisk right) :
    Approximation where
  sample index :=
    (CCL.ProgressiveExp.approximation left leftDomain).sample index *
      (CCL.ProgressiveExp.approximation right rightDomain).sample
        index
  radiusSq := CCL.FiniteGeometric.quarterRadius
    dynamicExpProductErrorScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      dynamicExpProductErrorScale_nonneg
  later_close := by
    intro earlier later order
    let leftSource :=
      CCL.ProgressiveExp.approximation left leftDomain
    let rightSource :=
      CCL.ProgressiveExp.approximation right rightDomain
    have leftMovement := leftSource.later_close order
    have rightMovement := rightSource.later_close order
    have firstTerm :
        normSq
            ((leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later) ≤
          CCL.FiniteGeometric.quarterRadius
              CCL.ProgressiveExp.errorScale earlier * 10 := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct leftMovement
        (rightSource.sample_bounded later) (normSq_nonneg _)
        (CCL.FiniteGeometric.quarterRadius_nonneg
          CCL.ProgressiveExp.errorScale_nonneg _)
    have secondTerm :
        normSq
            (leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
          10 * CCL.FiniteGeometric.quarterRadius
            CCL.ProgressiveExp.errorScale earlier := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct
        (leftSource.sample_bounded earlier) rightMovement (normSq_nonneg _)
        (by decide)
    have identity :
        leftSource.sample later * rightSource.sample later -
            leftSource.sample earlier * rightSource.sample earlier =
          (leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later +
            leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
    change normSq
        (leftSource.sample later * rightSource.sample later -
          leftSource.sample earlier * rightSource.sample earlier) ≤
      CCL.FiniteGeometric.quarterRadius
        dynamicExpProductErrorScale earlier
    rw [identity]
    calc
      normSq
          ((leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later +
            leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
        2 *
          (normSq
              ((leftSource.sample later - leftSource.sample earlier) *
                rightSource.sample later) +
            normSq
              (leftSource.sample earlier *
                (rightSource.sample later - rightSource.sample earlier))) :=
        normSq_add_le_two _ _
      _ ≤ 2 *
          (CCL.FiniteGeometric.quarterRadius
                CCL.ProgressiveExp.errorScale earlier * 10 +
            10 * CCL.FiniteGeometric.quarterRadius
              CCL.ProgressiveExp.errorScale earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          dynamicExpProductErrorScale earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        unfold dynamicExpProductErrorScale
        ring1
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      dynamicExpProductErrorScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      dynamicExpProductErrorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      dynamicExpProductErrorScale dynamicExpProductErrorScale_nonneg
  centerBound := 10 * 10
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide)
  sample_bounded := by
    intro index
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      ((CCL.ProgressiveExp.approximation left leftDomain).sample_bounded
        index)
      ((CCL.ProgressiveExp.approximation right rightDomain).sample_bounded
        index)
      (normSq_nonneg _) (by decide)

@[simp] theorem dynamicExpProductApproximation_sample
    {left right : Named}
    (leftDomain : CCL.ProgressiveExp.UnitDisk left)
    (rightDomain : CCL.ProgressiveExp.UnitDisk right)
    (index : Nat) :
    (dynamicExpProductApproximation leftDomain rightDomain).sample index =
      (CCL.ProgressiveExp.approximation left leftDomain).sample
          index *
        (CCL.ProgressiveExp.approximation right rightDomain).sample
          index :=
  rfl

/-- Actual multiplication of the two local progressive exponential names is
operationally their dynamic pointwise Horner product. -/
def localExpMul_toDynamic {left right : Named}
    (leftDomain : CCL.ProgressiveExp.UnitDisk left)
    (rightDomain : CCL.ProgressiveExp.UnitDisk right) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExp.named left leftDomain)
        (CCL.ProgressiveExp.named right rightDomain))
      (dynamicExpProductApproximation leftDomain rightDomain).toNamed :=
  mulToNamed_equivalent_pointwise
    (CCL.ProgressiveExp.approximation left leftDomain)
    (CCL.ProgressiveExp.approximation right rightDomain)
    (dynamicExpProductApproximation leftDomain rightDomain)
    (by intro index; rfl)

def dynamicInputSum (left right : Named) (index : Nat) : Gaussian :=
  CCL.ProgressiveExp.inputSample left index +
    CCL.ProgressiveExp.inputSample right index

theorem dynamicInputSum_unit (left right : Named)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add left right))
    (index : Nat) : normSq (dynamicInputSum left right index) ≤ 1 := by
  apply sumDomain.possible_unit
  exact
    ⟨CCL.ProgressiveExp.inputSample left index,
      CCL.ProgressiveExp.inputSample right index,
      CCL.ProgressiveExp.inputSample_possible_start left index,
      CCL.ProgressiveExp.inputSample_possible_start right index,
      rfl⟩

theorem dynamicInputSum_later_close (left right : Named)
    {earlier later : Nat} (order : earlier ≤ later) :
    normSq
        (dynamicInputSum left right later -
          dynamicInputSum left right earlier) ≤
      CCL.FiniteGeometric.quarterRadius 16 earlier := by
  have leftMovement :=
    CCL.ProgressiveSampling.witnessAt_later_close
      left.process left.state order
  have rightMovement :=
    CCL.ProgressiveSampling.witnessAt_later_close
      right.process right.state order
  have identity :
      dynamicInputSum left right later - dynamicInputSum left right earlier =
        (CCL.ProgressiveExp.inputSample left later -
          CCL.ProgressiveExp.inputSample left earlier) +
        (CCL.ProgressiveExp.inputSample right later -
          CCL.ProgressiveExp.inputSample right earlier) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [dynamicInputSum,
        CCL.ProgressiveExp.inputSample,
        sub_re, sub_im, add_re, add_im] <;> ring1
  rw [identity]
  calc
    normSq
        ((CCL.ProgressiveExp.inputSample left later -
            CCL.ProgressiveExp.inputSample left earlier) +
          (CCL.ProgressiveExp.inputSample right later -
            CCL.ProgressiveExp.inputSample right earlier)) ≤
      2 *
        (normSq
            (CCL.ProgressiveExp.inputSample left later -
              CCL.ProgressiveExp.inputSample left earlier) +
          normSq
            (CCL.ProgressiveExp.inputSample right later -
              CCL.ProgressiveExp.inputSample right earlier)) :=
      normSq_add_le_two _ _
    _ ≤ 2 *
        (CCL.FiniteGeometric.quarterRadius 4 earlier +
          CCL.FiniteGeometric.quarterRadius 4 earlier) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftMovement rightMovement) (by decide)
    _ = CCL.FiniteGeometric.quarterRadius 16 earlier := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      ring1

def dynamicExpSumErrorScale : Coordinate := 2 * (10 + 16 * 16)

theorem dynamicExpSumErrorScale_nonneg : 0 ≤ dynamicExpSumErrorScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide)))

/-- Dynamic local Horner program evaluated at the explicit equal-index sums
of the two operand readings. -/
def dynamicExpSumApproximation (left right : Named)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add left right)) :
    Approximation where
  sample index := CCL.FiniteExp.sample
    (dynamicInputSum left right index) index
  radiusSq := CCL.FiniteGeometric.quarterRadius
    dynamicExpSumErrorScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      dynamicExpSumErrorScale_nonneg
  later_close := by
    intro earlier later order
    let earlierInput := dynamicInputSum left right earlier
    let laterInput := dynamicInputSum left right later
    have earlierUnit := dynamicInputSum_unit left right sumDomain earlier
    have laterUnit := dynamicInputSum_unit left right sumDomain later
    have truncation := CCL.FiniteExp.sample_later_close
      laterInput laterUnit order
    have inputMovement := dynamicInputSum_later_close left right order
    have inputEffect := CCL.FiniteExp.sample_input_close
      laterInput earlierInput laterUnit earlierUnit earlier
    change normSq
        (CCL.FiniteExp.sample laterInput later -
          CCL.FiniteExp.sample earlierInput earlier) ≤
      CCL.FiniteGeometric.quarterRadius
        dynamicExpSumErrorScale earlier
    calc
      normSq
          (CCL.FiniteExp.sample laterInput later -
            CCL.FiniteExp.sample earlierInput earlier) ≤
        2 *
          (normSq
              (CCL.FiniteExp.sample laterInput later -
                CCL.FiniteExp.sample laterInput earlier) +
            normSq
              (CCL.FiniteExp.sample laterInput earlier -
                CCL.FiniteExp.sample earlierInput earlier)) :=
        normSq_sub_le_via _ _ _
      _ ≤ 2 *
          (CCL.FiniteGeometric.quarterRadius 10 earlier +
            16 * CCL.FiniteGeometric.quarterRadius 16 earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add truncation
            (inputEffect.trans
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                inputMovement (by decide))))
          (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          dynamicExpSumErrorScale earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        unfold dynamicExpSumErrorScale
        ring1
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      dynamicExpSumErrorScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      dynamicExpSumErrorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      dynamicExpSumErrorScale dynamicExpSumErrorScale_nonneg
  centerBound := 10
  centerBound_nonneg := by decide
  sample_bounded := by
    intro index
    exact CCL.FiniteExp.sample_bounded _
      (dynamicInputSum_unit left right sumDomain index) index

@[simp] theorem dynamicExpSumApproximation_sample
    (left right : Named)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add left right))
    (index : Nat) :
    (dynamicExpSumApproximation left right sumDomain).sample index =
      CCL.FiniteExp.sample
        (dynamicInputSum left right index) index :=
  rfl

private theorem quarterRadius_scale_le {small large : Coordinate}
    (scaleOrder : small ≤ large) (index : Nat) :
    CCL.FiniteGeometric.quarterRadius small index ≤
      CCL.FiniteGeometric.quarterRadius large index := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct scaleOrder
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)

def dynamicExpAdditionMasterScale : Coordinate :=
  dynamicExpProductErrorScale + dynamicExpSumErrorScale + 16

theorem dynamicExpAdditionMasterScale_nonneg :
    0 ≤ dynamicExpAdditionMasterScale :=
  add_nonneg
    (add_nonneg dynamicExpProductErrorScale_nonneg
      dynamicExpSumErrorScale_nonneg)
    (by decide)

theorem dynamicExpProductErrorScale_le_master :
    dynamicExpProductErrorScale ≤ dynamicExpAdditionMasterScale := by
  unfold dynamicExpAdditionMasterScale
  calc
    dynamicExpProductErrorScale ≤
        dynamicExpProductErrorScale + dynamicExpSumErrorScale :=
      le_add_of_nonneg_right dynamicExpSumErrorScale_nonneg
    _ ≤ dynamicExpProductErrorScale + dynamicExpSumErrorScale + 16 :=
      le_add_of_nonneg_right (show (0 : Coordinate) ≤ 16 by decide)

theorem dynamicExpSumErrorScale_le_master :
    dynamicExpSumErrorScale ≤ dynamicExpAdditionMasterScale := by
  unfold dynamicExpAdditionMasterScale
  calc
    dynamicExpSumErrorScale ≤
        dynamicExpProductErrorScale + dynamicExpSumErrorScale :=
      le_add_of_nonneg_left dynamicExpProductErrorScale_nonneg
    _ ≤ dynamicExpProductErrorScale + dynamicExpSumErrorScale + 16 :=
      le_add_of_nonneg_right (show (0 : Coordinate) ≤ 16 by decide)

theorem sixteen_le_dynamicExpAdditionMasterScale :
    (16 : Coordinate) ≤ dynamicExpAdditionMasterScale := by
  unfold dynamicExpAdditionMasterScale
  calc
    (16 : Coordinate) ≤
        16 + (dynamicExpProductErrorScale + dynamicExpSumErrorScale) :=
      le_add_of_nonneg_right
        (add_nonneg dynamicExpProductErrorScale_nonneg
          dynamicExpSumErrorScale_nonneg)
    _ = dynamicExpProductErrorScale + dynamicExpSumErrorScale + 16 := by
      ring1

/-- Dynamic finite Horner addition law.  At one computed odd depth the exact
finite polynomial estimate is instantiated with the displayed operand
readings at that depth; explicit tails absorb all later dynamic readings. -/
def dynamicLocalExp_add_equivalent {left right : Named}
    (leftDomain : CCL.ProgressiveExp.UnitDisk left)
    (rightDomain : CCL.ProgressiveExp.UnitDisk right)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add left right)) :
    Equivalent
      (dynamicExpProductApproximation leftDomain rightDomain)
      (dynamicExpSumApproximation left right sumDomain) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 16
    have smallPositive : 0 < smallTarget :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    let start := max leftStart rightStart
    let index := CCL.FiniteGeometric.firstQuarterBelow
      dynamicExpAdditionMasterScale start smallTarget
    let synchronized := 2 * index + 1
    have indexGe : start ≤ index :=
      CCL.FiniteGeometric.firstQuarterBelow_ge
        dynamicExpAdditionMasterScale start smallTarget
    have synchronizedGeIndex : index ≤ synchronized := by
      dsimp only [synchronized]
      omega
    have masterSmall :
        CCL.FiniteGeometric.quarterRadius
            dynamicExpAdditionMasterScale index < smallTarget :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate
        dynamicExpAdditionMasterScale dynamicExpAdditionMasterScale_nonneg
          start smallTarget smallPositive
    exact
      { leftIndex := synchronized
        rightIndex := synchronized
        left_ge := (Nat.le_max_left _ _).trans
          (indexGe.trans synchronizedGeIndex)
        right_ge := (Nat.le_max_right _ _).trans
          (indexGe.trans synchronizedGeIndex)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have masterAtSynchronized :
              CCL.FiniteGeometric.quarterRadius
                  dynamicExpAdditionMasterScale synchronized ≤
                CCL.FiniteGeometric.quarterRadius
                  dynamicExpAdditionMasterScale index :=
            quarterRadius_index_antitone
              dynamicExpAdditionMasterScale_nonneg synchronizedGeIndex
          have productTail :
              normSq
                  ((dynamicExpProductApproximation leftDomain rightDomain).sample
                      leftLater -
                    (dynamicExpProductApproximation leftDomain rightDomain).sample
                      synchronized) < smallTarget :=
            by
              have movement :=
                (dynamicExpProductApproximation leftDomain rightDomain).later_close
                  leftOrder
              change normSq
                  ((dynamicExpProductApproximation leftDomain rightDomain).sample
                      leftLater -
                    (dynamicExpProductApproximation leftDomain rightDomain).sample
                      synchronized) ≤
                CCL.FiniteGeometric.quarterRadius
                  dynamicExpProductErrorScale synchronized at movement
              exact movement.trans_lt
                ((quarterRadius_scale_le
                    dynamicExpProductErrorScale_le_master synchronized).trans_lt
                  (masterAtSynchronized.trans_lt masterSmall))
          have sumTailForward :
              normSq
                  ((dynamicExpSumApproximation left right sumDomain).sample
                      rightLater -
                    (dynamicExpSumApproximation left right sumDomain).sample
                      synchronized) < smallTarget :=
            by
              have movement :=
                (dynamicExpSumApproximation left right sumDomain).later_close
                  rightOrder
              change normSq
                  ((dynamicExpSumApproximation left right sumDomain).sample
                      rightLater -
                    (dynamicExpSumApproximation left right sumDomain).sample
                      synchronized) ≤
                CCL.FiniteGeometric.quarterRadius
                  dynamicExpSumErrorScale synchronized at movement
              exact movement.trans_lt
                ((quarterRadius_scale_le
                    dynamicExpSumErrorScale_le_master synchronized).trans_lt
                  (masterAtSynchronized.trans_lt masterSmall))
          have sumTailReverse :
              normSq
                  ((dynamicExpSumApproximation left right sumDomain).sample
                      synchronized -
                    (dynamicExpSumApproximation left right sumDomain).sample
                      rightLater) < smallTarget := by
            have reverseIdentity :
                (dynamicExpSumApproximation left right sumDomain).sample
                      synchronized -
                    (dynamicExpSumApproximation left right sumDomain).sample
                      rightLater =
                  -((dynamicExpSumApproximation left right sumDomain).sample
                      rightLater -
                    (dynamicExpSumApproximation left right sumDomain).sample
                      synchronized) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [reverseIdentity, normSq_neg]
            exact sumTailForward
          have directLe :=
            CCL.TranscendentalLaws.expProductSample_addition_error_odd
              (CCL.ProgressiveExp.inputSample_unit
                leftDomain synchronized)
              (CCL.ProgressiveExp.inputSample_unit
                rightDomain synchronized)
              index
          have direct :
              normSq
                  ((dynamicExpProductApproximation leftDomain rightDomain).sample
                      synchronized -
                    (dynamicExpSumApproximation left right sumDomain).sample
                      synchronized) < smallTarget := by
            have directBound :
                normSq
                    ((dynamicExpProductApproximation leftDomain rightDomain).sample
                        synchronized -
                      (dynamicExpSumApproximation left right sumDomain).sample
                        synchronized) ≤
                  CCL.FiniteGeometric.quarterRadius 16 index := by
              simpa only [dynamicExpProductApproximation_sample,
                dynamicExpSumApproximation_sample,
                CCL.ProgressiveExp.approximation,
                CCL.ProgressiveExp.domainSample,
                CCL.ProgressiveExp.sampleFrom,
                CCL.ProgressiveExp.unitDiskSamples,
                CCL.TranscendentalLaws.expProductSample,
                dynamicInputSum] using directLe
            exact directBound.trans_lt
              ((quarterRadius_scale_le
                  sixteen_le_dynamicExpAdditionMasterScale index).trans_lt
                masterSmall)
          have middle :
              normSq
                  ((dynamicExpProductApproximation leftDomain rightDomain).sample
                      synchronized -
                    (dynamicExpSumApproximation left right sumDomain).sample
                      rightLater) <
                2 * (smallTarget + smallTarget) :=
            (normSq_sub_le_via _ _ _).trans_lt
              (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  direct sumTailReverse))
          calc
            normSq
                ((dynamicExpProductApproximation leftDomain rightDomain).sample
                    leftLater -
                  (dynamicExpSumApproximation left right sumDomain).sample
                    rightLater) ≤
              2 *
                (normSq
                    ((dynamicExpProductApproximation leftDomain rightDomain).sample
                        leftLater -
                      (dynamicExpProductApproximation leftDomain rightDomain).sample
                        synchronized) +
                  normSq
                    ((dynamicExpProductApproximation leftDomain rightDomain).sample
                        synchronized -
                      (dynamicExpSumApproximation left right sumDomain).sample
                        rightLater)) :=
              normSq_sub_le_via _ _ _
            _ < 2 *
                (smallTarget + 2 * (smallTarget + smallTarget)) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  productTail middle)
            _ = 10 * smallTarget := by ring1
            _ < target := by
              dsimp only [smallTarget]
              exact ten_sixteenths_lt positive }

/-- CCL-name form of the dynamic finite Horner addition law. -/
def dynamicLocalExp_add_named_equivalent {left right : Named}
    (leftDomain : CCL.ProgressiveExp.UnitDisk left)
    (rightDomain : CCL.ProgressiveExp.UnitDisk right)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add left right)) :
    NamedEquivalent
      (dynamicExpProductApproximation leftDomain rightDomain).toNamed
      (dynamicExpSumApproximation left right sumDomain).toNamed :=
  approximationEquivalent_toNamed
    (dynamicLocalExp_add_equivalent leftDomain rightDomain sumDomain)

/-- The actual multiplication tree of the two arbitrary local exponential
outputs reaches the canonical dynamic sum-Horner name. -/
def localExpMul_toDynamicSum {left right : Named}
    (leftDomain : CCL.ProgressiveExp.UnitDisk left)
    (rightDomain : CCL.ProgressiveExp.UnitDisk right)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add left right)) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExp.named left leftDomain)
        (CCL.ProgressiveExp.named right rightDomain))
      (dynamicExpSumApproximation left right sumDomain).toNamed :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (localExpMul_toDynamic leftDomain rightDomain)
    (dynamicLocalExp_add_named_equivalent
      leftDomain rightDomain sumDomain)

def dynamicSumReindexDirectScale : Coordinate := 2 * (10 + 16)

theorem dynamicSumReindexDirectScale_nonneg :
    0 ≤ dynamicSumReindexDirectScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (by decide))

def dynamicSumReindexMasterScale : Coordinate :=
  dynamicExpSumErrorScale + CCL.ProgressiveExp.errorScale +
    dynamicSumReindexDirectScale

theorem dynamicSumReindexMasterScale_nonneg :
    0 ≤ dynamicSumReindexMasterScale :=
  add_nonneg
    (add_nonneg dynamicExpSumErrorScale_nonneg
      CCL.ProgressiveExp.errorScale_nonneg)
    dynamicSumReindexDirectScale_nonneg

private theorem coordinate_le_add_of_nonneg_right
    (a b : Coordinate) (nonnegative : 0 ≤ b) : a ≤ a + b := by
  calc
    a = 0 + a := (RFAP.ConstructiveFraction.zero_add _).symm
    _ ≤ b + a :=
      RFAP.ConstructiveFraction.add_le_add_right_direct nonnegative a
    _ = a + b := add_comm _ _

private theorem coordinate_le_add_of_nonneg_left
    (a b : Coordinate) (nonnegative : 0 ≤ b) : a ≤ b + a := by
  calc
    a = 0 + a := (RFAP.ConstructiveFraction.zero_add _).symm
    _ ≤ b + a :=
      RFAP.ConstructiveFraction.add_le_add_right_direct nonnegative a

private theorem dynamicSumScale_le_reindexMaster :
    dynamicExpSumErrorScale ≤ dynamicSumReindexMasterScale := by
  unfold dynamicSumReindexMasterScale
  calc
    dynamicExpSumErrorScale ≤
        dynamicExpSumErrorScale +
          CCL.ProgressiveExp.errorScale :=
      coordinate_le_add_of_nonneg_right _ _
        CCL.ProgressiveExp.errorScale_nonneg
    _ ≤ dynamicExpSumErrorScale +
          CCL.ProgressiveExp.errorScale +
            dynamicSumReindexDirectScale :=
      coordinate_le_add_of_nonneg_right _ _
        dynamicSumReindexDirectScale_nonneg

private theorem progressiveExpScale_le_reindexMaster :
    CCL.ProgressiveExp.errorScale ≤
      dynamicSumReindexMasterScale := by
  unfold dynamicSumReindexMasterScale
  calc
    CCL.ProgressiveExp.errorScale ≤
      dynamicExpSumErrorScale + CCL.ProgressiveExp.errorScale :=
      coordinate_le_add_of_nonneg_left _ _ dynamicExpSumErrorScale_nonneg
    _ ≤ dynamicExpSumErrorScale + CCL.ProgressiveExp.errorScale +
          dynamicSumReindexDirectScale :=
      coordinate_le_add_of_nonneg_right _ _
        dynamicSumReindexDirectScale_nonneg

private theorem reindexDirectScale_le_master :
    dynamicSumReindexDirectScale ≤ dynamicSumReindexMasterScale := by
  unfold dynamicSumReindexMasterScale
  calc
    dynamicSumReindexDirectScale ≤
        (dynamicExpSumErrorScale +
          CCL.ProgressiveExp.errorScale) +
            dynamicSumReindexDirectScale :=
      coordinate_le_add_of_nonneg_left _ _
        (add_nonneg dynamicExpSumErrorScale_nonneg
          CCL.ProgressiveExp.errorScale_nonneg)

private theorem twice_add_lt_twice_add_of_le_of_lt
    {a b c d : Coordinate} (first : a ≤ c) (second : b < d) :
    2 * (a + b) < 2 * (c + d) := by
  apply RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct (by decide)
  exact
    (RFAP.ConstructiveFraction.add_le_add_right_direct first b).trans_lt
      (RFAP.ConstructiveFraction.add_lt_add_left_direct second c)

/-- Finite resampling bridge from the canonical dynamic sum-Horner program to
local exponential evaluation on the productive sampled-sum input wrapper. -/
def dynamicExpSumReindexEquivalent (left right : CoherentNamed)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add
        left.name right.name)) :
    Equivalent
      (dynamicExpSumApproximation left.name right.name sumDomain)
      (CCL.ProgressiveExp.approximation
        (sampledSumApproximation left.name right.name).toNamed
        (sampledSumUnitDisk left right sumDomain)) := by
  let source := sampledSumApproximation left.name right.name
  let wrapperDomain := sampledSumUnitDisk left right sumDomain
  let wrapperExp := CCL.ProgressiveExp.approximation
    source.toNamed wrapperDomain
  exact
    { compare := by
        intro leftStart rightStart target positive
        let smallTarget := target / 16
        have smallPositive : 0 < smallTarget :=
          RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
        let start := max leftStart rightStart
        let rightIndex := CCL.FiniteGeometric.firstQuarterBelow
          dynamicSumReindexMasterScale start smallTarget
        have startLeRight : start ≤ rightIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            dynamicSumReindexMasterScale start smallTarget
        have masterSmall :
            CCL.FiniteGeometric.quarterRadius
                dynamicSumReindexMasterScale rightIndex < smallTarget :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            dynamicSumReindexMasterScale
              dynamicSumReindexMasterScale_nonneg start smallTarget
                smallPositive
        let sourceIndex :=
          CCL.OperationalEquivalence.emittedSampleIndex
            source rightIndex
        let leftIndex := max rightIndex sourceIndex
        have rightLeLeft : rightIndex ≤ leftIndex := Nat.le_max_left _ _
        have sourceLeLeft : sourceIndex ≤ leftIndex := Nat.le_max_right _ _
        have sourceRadiusSmall :
            source.radiusSq sourceIndex <
              CCL.ProgressiveSampling.refinementTarget rightIndex :=
          CCL.ProgressiveSampling.stateAt_accurate
            source.toProcess (show source.toProcess.State from (0 : Nat))
              rightIndex
        have sourceMovement := source.later_close sourceLeLeft
        have inputMovement :
            normSq (source.sample leftIndex - source.sample sourceIndex) <
              CCL.ProgressiveSampling.refinementTarget rightIndex :=
          sourceMovement.trans_lt sourceRadiusSmall
        have leftInputUnit : normSq (source.sample leftIndex) ≤ 1 := by
          rw [sampledSumApproximation_sample]
          exact dynamicInputSum_unit left.name right.name sumDomain leftIndex
        have rightInputUnit : normSq (source.sample sourceIndex) ≤ 1 := by
          rw [sampledSumApproximation_sample]
          exact dynamicInputSum_unit left.name right.name sumDomain sourceIndex
        have truncation := CCL.FiniteExp.sample_later_close
          (source.sample leftIndex) leftInputUnit rightLeLeft
        have inputEffect := CCL.FiniteExp.sample_input_close
          (source.sample leftIndex) (source.sample sourceIndex)
            leftInputUnit rightInputUnit rightIndex
        have inputStrict :
            normSq
                (CCL.FiniteExp.sample
                    (source.sample leftIndex) rightIndex -
                  CCL.FiniteExp.sample
                    (source.sample sourceIndex) rightIndex) <
              16 * CCL.ProgressiveSampling.refinementTarget
                rightIndex :=
          inputEffect.trans_lt
            (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              (by decide) inputMovement)
        have direct :
            normSq
                (CCL.FiniteExp.sample
                    (source.sample leftIndex) leftIndex -
                  CCL.FiniteExp.sample
                    (source.sample sourceIndex) rightIndex) <
              CCL.FiniteGeometric.quarterRadius
                dynamicSumReindexDirectScale rightIndex := by
          calc
            normSq
                (CCL.FiniteExp.sample
                    (source.sample leftIndex) leftIndex -
                  CCL.FiniteExp.sample
                    (source.sample sourceIndex) rightIndex) ≤
              2 *
                (normSq
                    (CCL.FiniteExp.sample
                        (source.sample leftIndex) leftIndex -
                      CCL.FiniteExp.sample
                        (source.sample leftIndex) rightIndex) +
                  normSq
                    (CCL.FiniteExp.sample
                        (source.sample leftIndex) rightIndex -
                      CCL.FiniteExp.sample
                        (source.sample sourceIndex) rightIndex)) :=
              normSq_sub_le_via _ _ _
            _ < 2 *
                (CCL.FiniteGeometric.quarterRadius 10 rightIndex +
                  16 * CCL.ProgressiveSampling.refinementTarget
                    rightIndex) :=
              twice_add_lt_twice_add_of_le_of_lt truncation inputStrict
            _ = CCL.FiniteGeometric.quarterRadius
                dynamicSumReindexDirectScale rightIndex := by
              unfold dynamicSumReindexDirectScale
              rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
                CCL.ProgressiveSampling.refinementTarget,
                CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
                CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
              ring1
        have directSmall :
            normSq
                (CCL.FiniteExp.sample
                    (source.sample leftIndex) leftIndex -
                  CCL.FiniteExp.sample
                    (source.sample sourceIndex) rightIndex) < smallTarget :=
          direct.trans
            ((quarterRadius_scale_le reindexDirectScale_le_master
              rightIndex).trans_lt masterSmall)
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := (Nat.le_max_left leftStart rightStart).trans
              (startLeRight.trans rightLeLeft)
            right_ge := (Nat.le_max_right leftStart rightStart).trans startLeRight
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have leftTail :=
                (dynamicExpSumApproximation left.name right.name
                  sumDomain).later_close leftOrder
              have leftRadiusToMaster :
                  CCL.FiniteGeometric.quarterRadius
                      dynamicExpSumErrorScale leftIndex ≤
                    CCL.FiniteGeometric.quarterRadius
                      dynamicSumReindexMasterScale rightIndex :=
                (quarterRadius_scale_le dynamicSumScale_le_reindexMaster
                  leftIndex).trans
                    (quarterRadius_index_antitone
                      dynamicSumReindexMasterScale_nonneg rightLeLeft)
              have leftTailSmall := leftTail.trans_lt
                (leftRadiusToMaster.trans_lt masterSmall)
              have rightTail := wrapperExp.later_close rightOrder
              have rightTailSmall := rightTail.trans_lt
                ((quarterRadius_scale_le progressiveExpScale_le_reindexMaster
                  rightIndex).trans_lt masterSmall)
              have rightTailReverse :
                  normSq
                      (wrapperExp.sample rightIndex -
                        wrapperExp.sample rightLater) < smallTarget := by
                have identity : wrapperExp.sample rightIndex -
                      wrapperExp.sample rightLater =
                    -(wrapperExp.sample rightLater -
                      wrapperExp.sample rightIndex) := by
                  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                    simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
                rw [identity, normSq_neg]
                exact rightTailSmall
              have baseIdentity :
                  (dynamicExpSumApproximation left.name right.name
                    sumDomain).sample leftIndex =
                    CCL.FiniteExp.sample
                      (source.sample leftIndex) leftIndex := by
                rfl
              have wrapperIdentity : wrapperExp.sample rightIndex =
                  CCL.FiniteExp.sample
                    (source.sample sourceIndex) rightIndex := rfl
              rw [← baseIdentity, ← wrapperIdentity] at directSmall
              have middle := (normSq_sub_le_via _ _ _).trans_lt
                (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                  (by decide)
                  (RFAP.ConstructiveFraction.add_lt_add_direct
                    directSmall rightTailReverse))
              calc
                normSq
                    ((dynamicExpSumApproximation left.name right.name
                      sumDomain).sample leftLater -
                        wrapperExp.sample rightLater) ≤
                  2 *
                    (normSq
                        ((dynamicExpSumApproximation left.name right.name
                            sumDomain).sample leftLater -
                          (dynamicExpSumApproximation left.name right.name
                            sumDomain).sample leftIndex) +
                      normSq
                        ((dynamicExpSumApproximation left.name right.name
                            sumDomain).sample leftIndex -
                          wrapperExp.sample rightLater)) :=
                  normSq_sub_le_via _ _ _
                _ < 2 *
                    (smallTarget + 2 * (smallTarget + smallTarget)) :=
                  RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                    (by decide)
                    (RFAP.ConstructiveFraction.add_lt_add_direct
                      leftTailSmall middle)
                _ = 10 * smallTarget := by ring1
                _ < target := by
                  dsimp only [smallTarget]
                  exact ten_sixteenths_lt positive } }

/-- Named form of the finite resampling bridge. -/
def dynamicExpSum_toSampledLocalExp (left right : CoherentNamed)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add
        left.name right.name)) :
    NamedEquivalent
      (dynamicExpSumApproximation left.name right.name sumDomain).toNamed
      (CCL.ProgressiveExp.named
        (sampledSumApproximation left.name right.name).toNamed
        (sampledSumUnitDisk left right sumDomain)) :=
  approximationEquivalent_toNamed
    (dynamicExpSumReindexEquivalent left right sumDomain)

/-- The local exponential addition law for arbitrary coherent productive
CCL inputs.  All three unit-disk hypotheses concern possible finite readings;
the conclusion compares the actual multiplication, addition, and local
exponential processes rather than idealized pointwise streams. -/
def coherentLocalExp_add_named_equivalent (left right : CoherentNamed)
    (leftDomain : CCL.ProgressiveExp.UnitDisk left.name)
    (rightDomain : CCL.ProgressiveExp.UnitDisk right.name)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add
        left.name right.name)) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExp.named left.name leftDomain)
        (CCL.ProgressiveExp.named right.name rightDomain))
      (CCL.ProgressiveExp.named
        (CCL.ProgressiveTransducer.Named.add
          left.name right.name) sumDomain) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (localExpMul_toDynamicSum leftDomain rightDomain sumDomain)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (dynamicExpSum_toSampledLocalExp left right sumDomain)
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (localExp_sum_toSampled left right sumDomain)))

/-- Actual multiplication of coherent CCL names is operationally
commutative.  The proof compares their common equal-index product samples. -/
def coherentMul_comm (left right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        left.name right.name)
      (CCL.ProgressiveTransducer.Named.mul
        right.name left.name) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentMul_toNamed left right)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (approximationEquivalent_toNamed
        (approximationEquivalentOfSamplesEq
          (sampledProductApproximation left.name right.name)
          (sampledProductApproximation right.name left.name)
          (by
            intro index
            rw [sampledProductApproximation_sample,
              sampledProductApproximation_sample]
            exact RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _)))
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (coherentMul_toNamed right left)))

/-- Actual multiplication of three coherent CCL names is operationally
associative.  Both process trees are reduced, by finite congruence, to the
same equal-index triple-product approximation. -/
def coherentMul_assoc (left middle right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveTransducer.Named.mul
          left.name middle.name)
        right.name)
      (CCL.ProgressiveTransducer.Named.mul
        left.name
        (CCL.ProgressiveTransducer.Named.mul
          middle.name right.name)) := by
  let leftSource := CCL.ProgressiveSampling.approximation left.name
  let middleSource :=
    CCL.ProgressiveSampling.approximation middle.name
  let rightSource :=
    CCL.ProgressiveSampling.approximation right.name
  let leftMiddle := sampledProductApproximation left.name middle.name
  let middleRight := sampledProductApproximation middle.name right.name
  let triple := sampledTripleApproximation left.name middle.name right.name
  let sampledLeft : CoherentNamed :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      leftSource
  let sampledRight : CoherentNamed :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      rightSource
  let canonicalLeftMiddle : CoherentNamed :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      leftMiddle
  let canonicalMiddleRight : CoherentNamed :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      middleRight
  have normalizeLeft :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          (CCL.ProgressiveTransducer.Named.mul
            left.name middle.name)
          right.name)
        (CCL.ProgressiveTransducer.Named.mul
          canonicalLeftMiddle.name sampledRight.name) :=
    coherentMul_respects
      (CCL.ProgressiveCoherence.CoherentNamed.mul left middle)
      canonicalLeftMiddle right sampledRight
      (coherentMul_toNamed left middle)
      (named_toSamplingNamed right.name)
  have leftPointwise :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          canonicalLeftMiddle.name sampledRight.name)
        triple.toNamed :=
    mulToNamed_equivalent_pointwise leftMiddle rightSource triple
      (by intro index; rfl)
  have normalizeRight :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          left.name
          (CCL.ProgressiveTransducer.Named.mul
            middle.name right.name))
        (CCL.ProgressiveTransducer.Named.mul
          sampledLeft.name canonicalMiddleRight.name) :=
    coherentMul_respects left sampledLeft
      (CCL.ProgressiveCoherence.CoherentNamed.mul middle right)
      canonicalMiddleRight
      (named_toSamplingNamed left.name)
      (coherentMul_toNamed middle right)
  have rightPointwise :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          sampledLeft.name canonicalMiddleRight.name)
        triple.toNamed :=
    mulToNamed_equivalent_pointwise leftSource middleRight triple (by
      intro index
      rw [sampledTripleApproximation_sample,
        sampledProductApproximation_sample]
      exact RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    normalizeLeft
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      leftPointwise
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          rightPointwise)
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          normalizeRight)))

/-- The two square trees can be interleaved constructively:
`(left*left)*(right*right)` and `(left*right)*(left*right)` are operationally
equivalent for coherent CCL names. -/
def coherentMul_squares_interchange (left right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveTransducer.Named.mul
          left.name left.name)
        (CCL.ProgressiveTransducer.Named.mul
          right.name right.name))
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveTransducer.Named.mul
          left.name right.name)
        (CCL.ProgressiveTransducer.Named.mul
          left.name right.name)) := by
  let leftRight :=
    CCL.ProgressiveCoherence.CoherentNamed.mul left right
  let rightLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.mul right left
  let rightSquare :=
    CCL.ProgressiveCoherence.CoherentNamed.mul right right
  let leftRightRight :=
    CCL.ProgressiveCoherence.CoherentNamed.mul leftRight right
  let rightLeftRight :=
    CCL.ProgressiveCoherence.CoherentNamed.mul rightLeft right
  let leftRightSquare :=
    CCL.ProgressiveCoherence.CoherentNamed.mul left rightSquare
  let rightLeftProduct :=
    CCL.ProgressiveCoherence.CoherentNamed.mul rightLeft right
  let rightLeftRightAssociated :=
    CCL.ProgressiveCoherence.CoherentNamed.mul right leftRight
  have first := coherentMul_assoc left left rightSquare
  have innerSecond : NamedEquivalent leftRightSquare.name leftRightRight.name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (coherentMul_assoc left right right)
  have second :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          left.name leftRightSquare.name)
        (CCL.ProgressiveTransducer.Named.mul
          left.name leftRightRight.name) :=
    coherentMul_respects left left leftRightSquare leftRightRight
      (CCL.OperationalEquivalence.NamedEquivalent.refl left.name)
      innerSecond
  have innerThird : NamedEquivalent leftRightRight.name rightLeftRight.name :=
    coherentMul_respects leftRight rightLeft right right
      (coherentMul_comm left right)
      (CCL.OperationalEquivalence.NamedEquivalent.refl right.name)
  have third :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          left.name leftRightRight.name)
        (CCL.ProgressiveTransducer.Named.mul
          left.name rightLeftRight.name) :=
    coherentMul_respects left left leftRightRight rightLeftRight
      (CCL.OperationalEquivalence.NamedEquivalent.refl left.name)
      innerThird
  have innerFourth :
      NamedEquivalent rightLeftProduct.name rightLeftRightAssociated.name :=
    coherentMul_assoc right left right
  have fourth :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          left.name rightLeftProduct.name)
        (CCL.ProgressiveTransducer.Named.mul
          left.name rightLeftRightAssociated.name) :=
    coherentMul_respects left left rightLeftProduct rightLeftRightAssociated
      (CCL.OperationalEquivalence.NamedEquivalent.refl left.name)
      innerFourth
  have fifth :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          left.name rightLeftRightAssociated.name)
        (CCL.ProgressiveTransducer.Named.mul
          leftRight.name leftRight.name) :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (coherentMul_assoc left right leftRight)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans first
    (CCL.OperationalEquivalence.NamedEquivalent.trans second
      (CCL.OperationalEquivalence.NamedEquivalent.trans third
        (CCL.OperationalEquivalence.NamedEquivalent.trans fourth
          fifth)))

/-- A fixed finite number of repeated squarings commutes with coherent
multiplication.  This is the algebraic lift needed after a common dyadic
range exponent has reduced both exponential inputs to the local chart. -/
def squareIterate_mul_equivalent : (exponent : Nat) →
    (left right : CoherentNamed) →
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.squareIterate
          exponent left.name)
        (CCL.ProgressiveExpRange.squareIterate
          exponent right.name))
      (CCL.ProgressiveExpRange.squareIterate exponent
        (CCL.ProgressiveTransducer.Named.mul
          left.name right.name))
  | 0, left, right =>
      CCL.OperationalEquivalence.NamedEquivalent.refl
        (CCL.ProgressiveTransducer.Named.mul
          left.name right.name)
  | exponent + 1, left, right => by
      let previousLeft : CoherentNamed :=
        { name := CCL.ProgressiveExpRange.squareIterate
            exponent left.name
          coherent := squareIterateCoherent exponent left.name left.coherent }
      let previousRight : CoherentNamed :=
        { name := CCL.ProgressiveExpRange.squareIterate
            exponent right.name
          coherent := squareIterateCoherent exponent right.name right.coherent }
      let product :=
        CCL.ProgressiveCoherence.CoherentNamed.mul left right
      let previousProduct : CoherentNamed :=
        { name := CCL.ProgressiveExpRange.squareIterate
            exponent product.name
          coherent := squareIterateCoherent exponent product.name
            product.coherent }
      let previousFactors :=
        CCL.ProgressiveCoherence.CoherentNamed.mul
          previousLeft previousRight
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (coherentMul_squares_interchange previousLeft previousRight)
        (coherentSquare_respects previousFactors previousProduct
          (squareIterate_mul_equivalent exponent left right))

/-- The arbitrary coherent-input local exponential addition law survives any
common displayed number of actual CCL squarings. -/
def coherentLocalExp_add_after_squareIterate (exponent : Nat)
    (left right : CoherentNamed)
    (leftDomain : CCL.ProgressiveExp.UnitDisk left.name)
    (rightDomain : CCL.ProgressiveExp.UnitDisk right.name)
    (sumDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add
        left.name right.name)) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.squareIterate exponent
          (CCL.ProgressiveExp.named left.name leftDomain))
        (CCL.ProgressiveExpRange.squareIterate exponent
          (CCL.ProgressiveExp.named right.name rightDomain)))
      (CCL.ProgressiveExpRange.squareIterate exponent
        (CCL.ProgressiveExp.named
          (CCL.ProgressiveTransducer.Named.add
            left.name right.name) sumDomain)) := by
  let leftExp : CoherentNamed :=
    { name := CCL.ProgressiveExp.named left.name leftDomain
      coherent := localExpCoherent left.name leftDomain }
  let rightExp : CoherentNamed :=
    { name := CCL.ProgressiveExp.named right.name rightDomain
      coherent := localExpCoherent right.name rightDomain }
  let sumInput := CCL.ProgressiveCoherence.CoherentNamed.add
    left right
  let sumExp : CoherentNamed :=
    { name := CCL.ProgressiveExp.named sumInput.name sumDomain
      coherent := localExpCoherent sumInput.name sumDomain }
  let productExp :=
    CCL.ProgressiveCoherence.CoherentNamed.mul leftExp rightExp
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (squareIterate_mul_equivalent exponent leftExp rightExp)
    (squareIterate_respects exponent productExp sumExp
      (coherentLocalExp_add_named_equivalent left right
        leftDomain rightDomain sumDomain))

/-- The exact local exponential addition law survives any common displayed
number of actual CCL squarings.  This specializes the arbitrary coherent law
to displayed rational operands. -/
def exactLocalExp_add_after_squareIterate (exponent : Nat)
    {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1)
    (sumUnit : normSq (x + y) ≤ 1) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.squareIterate exponent
          (exactLocalExpNamed x xUnit))
        (CCL.ProgressiveExpRange.squareIterate exponent
          (exactLocalExpNamed y yUnit)))
      (CCL.ProgressiveExpRange.squareIterate exponent
        (exactLocalExpNamed (x + y) sumUnit)) := by
  let leftExp : CoherentNamed :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      (exactLocalExpApproximation x xUnit)
  let rightExp : CoherentNamed :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      (exactLocalExpApproximation y yUnit)
  let sumExp : CoherentNamed :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      (exactLocalExpApproximation (x + y) sumUnit)
  let productExp :=
    CCL.ProgressiveCoherence.CoherentNamed.mul leftExp rightExp
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (squareIterate_mul_equivalent exponent leftExp rightExp)
    (squareIterate_respects exponent productExp sumExp
      (localExp_add_actual_named_equivalent xUnit yUnit sumUnit))

/-- One additional dyadic range-reduction step is exactly compensated by
one actual output squaring, after any fixed finite squaring tail. -/
def exactLocalExp_doubling_after_squareIterate (exponent : Nat)
    (value : Gaussian) (unit : normSq value ≤ 1)
    (doubleUnit : normSq (value + value) ≤ 1) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.squareIterate (exponent + 1)
        (exactLocalExpNamed value unit))
      (CCL.ProgressiveExpRange.squareIterate exponent
      (exactLocalExpNamed (value + value) doubleUnit)) :=
  exactLocalExp_add_after_squareIterate exponent unit unit doubleUnit

def dyadicHalf : Gaussian := ⟨1 / 2, 0⟩

/-- Recursive dyadic range reduction, expressed without a logarithm or an
unbounded search. -/
def dyadicScale : Nat → Gaussian → Gaussian
  | 0, value => value
  | exponent + 1, value => dyadicHalf * dyadicScale exponent value

private theorem half_mul_inversePower (exponent : Nat) :
    (1 / 2 : Coordinate) * (1 / (2 : Coordinate) ^ exponent) =
      1 / (2 : Coordinate) ^ (exponent + 1) := by
  rw [pow_succ]
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.one_mul]
  rw [RFAP.ConstructiveFraction.inv_mul_direct,
    RFAP.ConstructiveFraction.mul_comm]

theorem dyadicScale_eq_inversePower (exponent : Nat) (value : Gaussian) :
    dyadicScale exponent value =
      (⟨1 / (2 : Coordinate) ^ exponent, 0⟩ : Gaussian) * value := by
  induction exponent with
  | zero =>
      change value = (⟨1 / (1 : Coordinate), 0⟩ : Gaussian) * value
      have oneDivOne : (1 / (1 : Coordinate)) = 1 := by
        have canceled :
            ((1 : Coordinate) / (1 : Coordinate)) * (1 : Coordinate) = 1 :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne
            (1 : Coordinate) (1 : Coordinate) (by decide)
        calc
          (1 : Coordinate) / 1 = (1 / 1) * 1 :=
            (RFAP.ConstructiveFraction.mul_one_direct _).symm
          _ = 1 := canceled
      rw [oneDivOne]
      exact (RFAP.ConstructiveGaussian.Gaussian.one_mul value).symm
  | succ exponent inductionHypothesis =>
      rw [dyadicScale, inductionHypothesis]
      have scaleProduct :
          dyadicHalf * (⟨1 / (2 : Coordinate) ^ exponent, 0⟩ : Gaussian) =
            (⟨1 / (2 : Coordinate) ^ (exponent + 1), 0⟩ : Gaussian) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · change (1 / 2 : Coordinate) * (1 / 2 ^ exponent) - 0 * 0 =
            1 / 2 ^ (exponent + 1)
          rw [RFAP.ConstructiveFraction.mul_zero_direct,
            half_mul_inversePower]
          ring1
        · change (1 / 2 : Coordinate) * 0 + 0 * (1 / 2 ^ exponent) = 0
          ring1
      calc
        dyadicHalf *
            ((⟨1 / (2 : Coordinate) ^ exponent, 0⟩ : Gaussian) * value) =
          (dyadicHalf *
            (⟨1 / (2 : Coordinate) ^ exponent, 0⟩ : Gaussian)) * value :=
          (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
        _ = (⟨1 / (2 : Coordinate) ^ (exponent + 1), 0⟩ : Gaussian) *
            value := by rw [scaleProduct]

@[simp] theorem normSq_dyadicHalf : normSq dyadicHalf = 1 / 4 := by
  change (1 / 2 : Coordinate) ^ 2 + 0 ^ 2 = 1 / 4
  rw [pow_two, show (0 : Coordinate) ^ 2 = 0 by decide,
    RFAP.ConstructiveFraction.add_comm _ 0,
    RFAP.ConstructiveFraction.zero_add]
  calc
    (1 / 2 : Coordinate) * (1 / 2) = (1 * 1) / (2 * 2) :=
      RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
    _ = 1 / 4 := rfl

@[simp] theorem dyadicScale_succ_add_self (exponent : Nat)
    (value : Gaussian) :
    dyadicScale (exponent + 1) value + dyadicScale (exponent + 1) value =
      dyadicScale exponent value := by
  change dyadicHalf * dyadicScale exponent value +
      dyadicHalf * dyadicScale exponent value = dyadicScale exponent value
  have halfDouble : (1 / 2 : Coordinate) * 2 = 1 :=
    RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 2 (by decide)
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [dyadicHalf, mul_re, add_re]
    calc
      (1 / 2 * (dyadicScale exponent value).re -
            0 * (dyadicScale exponent value).im) +
          (1 / 2 * (dyadicScale exponent value).re -
            0 * (dyadicScale exponent value).im) =
        ((1 / 2 : Coordinate) * 2) *
          (dyadicScale exponent value).re := by ring1
      _ = (dyadicScale exponent value).re := by
        rw [halfDouble, RFAP.ConstructiveFraction.one_mul]
  · simp only [dyadicHalf, mul_im, add_im]
    calc
      (1 / 2 * (dyadicScale exponent value).im +
            0 * (dyadicScale exponent value).re) +
          (1 / 2 * (dyadicScale exponent value).im +
            0 * (dyadicScale exponent value).re) =
        ((1 / 2 : Coordinate) * 2) *
          (dyadicScale exponent value).im := by ring1
      _ = (dyadicScale exponent value).im := by
        rw [halfDouble, RFAP.ConstructiveFraction.one_mul]

/-- The displayed Gaussian coefficient for division by `2^exponent`. -/
def inverseDyadicAt (exponent : Nat) : Gaussian :=
  ⟨1 / (2 : Coordinate) ^ exponent, 0⟩

@[simp] theorem normSq_inverseDyadicAt (exponent : Nat) :
    normSq (inverseDyadicAt exponent) =
      CCL.FiniteGeometric.quarterRadius 1 exponent := by
  change (1 / (2 : Coordinate) ^ exponent) ^ 2 + 0 ^ 2 =
    1 / (4 : Coordinate) ^ exponent
  rw [show (0 : Coordinate) ^ 2 = 0 by decide,
    RFAP.ConstructiveFraction.add_comm _ 0,
    RFAP.ConstructiveFraction.zero_add, pow_two]
  calc
    (1 / (2 : Coordinate) ^ exponent) * (1 / (2 : Coordinate) ^ exponent) =
        (1 * 1) / ((2 : Coordinate) ^ exponent * 2 ^ exponent) :=
      RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
    _ = 1 / (4 : Coordinate) ^ exponent := by
      rw [RFAP.ConstructiveFraction.one_mul, ← mul_pow]
      rw [show (2 : Coordinate) * 2 = 4 by decide]

theorem normSq_inverseDyadicAt_le_one (exponent : Nat) :
    normSq (inverseDyadicAt exponent) ≤ 1 := by
  rw [normSq_inverseDyadicAt]
  exact CCL.FiniteGeometric.quarterRadius_le_scale
    (by decide) exponent

/-- Multiplication by an explicitly contractive Gaussian rational, applied
directly to every sample of a finite approximation. -/
def contractiveScaleApproximation (factor : Gaussian)
    (contractive : normSq factor ≤ 1) (source : Approximation) :
    Approximation where
  sample index := factor * source.sample index
  radiusSq := source.radiusSq
  radiusSq_nonneg := source.radiusSq_nonneg
  later_close := by
    intro earlier later order
    have identity :
        factor * source.sample later - factor * source.sample earlier =
          factor * (source.sample later - source.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    rw [identity, normSq_mul]
    calc
      normSq factor * normSq (source.sample later - source.sample earlier) ≤
          1 * normSq (source.sample later - source.sample earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          contractive (normSq_nonneg _)
      _ ≤ 1 * source.radiusSq earlier :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (source.later_close order) (by decide)
      _ = source.radiusSq earlier :=
        RFAP.ConstructiveFraction.one_mul _
  refineIndex := source.refineIndex
  refineIndex_ge := source.refineIndex_ge
  refineIndex_accurate := source.refineIndex_accurate
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [normSq_mul]
    calc
      normSq factor * normSq (source.sample index) ≤
          1 * normSq (source.sample index) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          contractive (normSq_nonneg _)
      _ ≤ 1 * source.centerBound :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (source.sample_bounded index) (by decide)
      _ = source.centerBound := RFAP.ConstructiveFraction.one_mul _

@[simp] theorem contractiveScaleApproximation_sample
    (factor : Gaussian) (contractive : normSq factor ≤ 1)
    (source : Approximation) (index : Nat) :
    (contractiveScaleApproximation factor contractive source).sample index =
      factor * source.sample index :=
  rfl

/-- Contractive pointwise scaling preserves finite operational equality. -/
def contractiveScaleApproximation_respects (factor : Gaussian)
    (contractive : normSq factor ≤ 1) {left right : Approximation}
    (equivalent : Equivalent left right) :
    Equivalent
      (contractiveScaleApproximation factor contractive left)
      (contractiveScaleApproximation factor contractive right) where
  compare := by
    intro leftStart rightStart target positive
    let comparison := equivalent.compare leftStart rightStart target positive
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have sourceClose := comparison.close leftOrder rightOrder
          have identity :
              factor * left.sample leftLater - factor * right.sample rightLater =
                factor *
                  (left.sample leftLater - right.sample rightLater) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
          rw [contractiveScaleApproximation_sample,
            contractiveScaleApproximation_sample, identity, normSq_mul]
          exact
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              contractive (normSq_nonneg _)).trans_lt
                (by simpa only [RFAP.ConstructiveFraction.one_mul]
                  using sourceClose) }

/-- Canonical finite approximation of an arbitrary name scaled by one
displayed inverse dyadic. -/
def dyadicScaledApproximation (exponent : Nat) (input : Named) :
    Approximation :=
  contractiveScaleApproximation (inverseDyadicAt exponent)
    (normSq_inverseDyadicAt_le_one exponent)
    (CCL.ProgressiveSampling.approximation input)

@[simp] theorem dyadicScaledApproximation_sample
    (exponent : Nat) (input : Named) (index : Nat) :
    (dyadicScaledApproximation exponent input).sample index =
      inverseDyadicAt exponent *
        (CCL.ProgressiveSampling.approximation input).sample index :=
  rfl

@[simp] theorem inverseDyadicAt_zero : inverseDyadicAt 0 = 1 := by
  decide

theorem inverseDyadicAt_succ (exponent : Nat) :
    dyadicHalf * inverseDyadicAt exponent =
      inverseDyadicAt (exponent + 1) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change (1 / 2 : Coordinate) * (1 / 2 ^ exponent) - 0 * 0 =
      1 / 2 ^ (exponent + 1)
    rw [RFAP.ConstructiveFraction.mul_zero_direct,
      half_mul_inversePower]
    ring1
  · change (1 / 2 : Coordinate) * 0 + 0 * (1 / 2 ^ exponent) = 0
    ring1

/-- The exact-name process and the constant finite approximation for the same
displayed rational are operationally equal. -/
def exact_toConstantNamed (value : Gaussian) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.exact value)
      (CCL.TranscendentalLaws.constantApproximation value).toNamed :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (named_toSamplingNamed
      (CCL.ProgressiveTransducer.Named.exact value))
    (approximationEquivalent_toNamed
      (approximationEquivalentOfSamplesEq
        (CCL.ProgressiveSampling.approximation
          (CCL.ProgressiveTransducer.Named.exact value))
        (CCL.TranscendentalLaws.constantApproximation value)
        (by intro index; rfl)))

/-- One explicit halving of an arbitrary coherent progressive input. -/
def halfScaled (input : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.mul
    (CCL.ProgressiveCoherence.CoherentNamed.exact dyadicHalf)
    input

theorem halfScaled_possible_quarter (input : CoherentNamed)
    (domain : CCL.ProgressiveExp.UnitDisk input.name)
    {value : Gaussian}
    (possible : (halfScaled input).name.process.Possible
      (halfScaled input).name.state value) :
    normSq value ≤ 1 / 4 := by
  rcases possible with ⟨scaleValue, sourceValue,
    scalePossible, sourcePossible, rfl⟩
  change scaleValue = dyadicHalf at scalePossible
  subst scaleValue
  rw [normSq_mul, normSq_dyadicHalf]
  calc
    (1 / 4 : Coordinate) * normSq sourceValue ≤ (1 / 4 : Coordinate) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (domain.possible_unit sourcePossible) (by decide)
    _ = 1 / 4 := RFAP.ConstructiveFraction.mul_one_direct _

/-- Halving preserves the local unit-disk contract. -/
theorem halfScaledUnitDisk (input : CoherentNamed)
    (domain : CCL.ProgressiveExp.UnitDisk input.name) :
    CCL.ProgressiveExp.UnitDisk (halfScaled input).name where
  possible_unit := by
    intro value possible
    exact (halfScaled_possible_quarter input domain possible).trans (by decide)

/-- The sum of two independently refined half-scaled readings remains in the
unit disk.  The proof uses their separate quarter-quadrance bounds and does
not identify the two readings. -/
theorem halfScaledSelfSumUnitDisk (input : CoherentNamed)
    (domain : CCL.ProgressiveExp.UnitDisk input.name) :
    CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add
        (halfScaled input).name (halfScaled input).name) where
  possible_unit := by
    intro value possible
    rcases possible with ⟨leftValue, rightValue,
      leftPossible, rightPossible, rfl⟩
    calc
      normSq (leftValue + rightValue) ≤
          2 * (normSq leftValue + normSq rightValue) :=
        normSq_add_le_two _ _
      _ ≤ 2 * ((1 / 4 : Coordinate) + 1 / 4) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add
            (halfScaled_possible_quarter input domain leftPossible)
            (halfScaled_possible_quarter input domain rightPossible))
          (by decide)
      _ = 1 := by decide

/-- Adding two actual, independently scheduled half-scaled copies is
operationally the original coherent input.  The comparison passes through
only finite canonical samplers. -/
def halfScaledSelfAdd_equivalent (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (halfScaled input).name (halfScaled input).name)
      input.name := by
  let halfExact :=
    CCL.ProgressiveCoherence.CoherentNamed.exact dyadicHalf
  let half := halfScaled input
  let halfProduct := sampledProductApproximation halfExact.name input.name
  let halfProductName :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      halfProduct
  let inputApproximation :=
    CCL.ProgressiveSampling.approximation input.name
  have halfToProduct : NamedEquivalent half.name halfProductName.name :=
    coherentMul_toNamed halfExact input
  have addToProductAdd :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.add half.name half.name)
        (CCL.ProgressiveTransducer.Named.add
          halfProductName.name halfProductName.name) :=
    coherentAdd_respects half halfProductName half halfProductName
      halfToProduct halfToProduct
  have productAddToSampled :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.add
          halfProductName.name halfProductName.name)
        (sampledSumApproximation
          halfProductName.name halfProductName.name).toNamed :=
    coherentAdd_toNamed halfProductName halfProductName
  have sampledToInput :
      NamedEquivalent
        (sampledSumApproximation
          halfProductName.name halfProductName.name).toNamed
        inputApproximation.toNamed :=
    approximationEquivalent_toNamed
      (pointwiseSumApproximation_respects
        (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
          halfProduct)
        (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
          halfProduct)
        (by intro index; rfl)
        (by
          intro index
          change inputApproximation.sample index =
            dyadicHalf * inputApproximation.sample index +
              dyadicHalf * inputApproximation.sample index
          exact (dyadicScale_succ_add_self 0
            (inputApproximation.sample index)).symm))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    addToProductAdd
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      productAddToSampled
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        sampledToInput
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          (named_toSamplingNamed input.name))))

/-- For an arbitrary coherent progressive input, one additional finite input
halving followed by one additional actual output squaring preserves the
restored local exponential name. -/
def coherentDyadicExp_step (exponent : Nat) (input : CoherentNamed)
    (domain : CCL.ProgressiveExp.UnitDisk input.name) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.squareIterate (exponent + 1)
        (CCL.ProgressiveExp.named (halfScaled input).name
          (halfScaledUnitDisk input domain)))
      (CCL.ProgressiveExpRange.squareIterate exponent
        (CCL.ProgressiveExp.named input.name domain)) := by
  let half := halfScaled input
  let halfDomain := halfScaledUnitDisk input domain
  let sumDomain := halfScaledSelfSumUnitDisk input domain
  let halfExp : CoherentNamed :=
    { name := CCL.ProgressiveExp.named half.name halfDomain
      coherent := localExpCoherent half.name halfDomain }
  let sumInput :=
    CCL.ProgressiveCoherence.CoherentNamed.add half half
  let sumExp : CoherentNamed :=
    { name := CCL.ProgressiveExp.named sumInput.name sumDomain
      coherent := localExpCoherent sumInput.name sumDomain }
  let inputExp : CoherentNamed :=
    { name := CCL.ProgressiveExp.named input.name domain
      coherent := localExpCoherent input.name domain }
  have localLaw := coherentLocalExp_add_after_squareIterate exponent
    half half halfDomain halfDomain sumDomain
  have sumToInput : NamedEquivalent sumExp.name inputExp.name :=
    localExpNamed_respects sumDomain domain
      (halfScaledSelfAdd_equivalent input)
  have restoredSumToInput := squareIterate_respects exponent
    sumExp inputExp sumToInput
  dsimp only [half, halfDomain, sumDomain, sumInput, sumExp] at localLaw
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by simpa only [CCL.ProgressiveExpRange.squareIterate,
        sumExp, sumInput, half,
        CCL.ProgressiveCoherence.CoherentNamed.add]
      using localLaw)
    restoredSumToInput

/-- A finite chain of explicit input halvings. -/
def halfIterate : Nat → CoherentNamed → CoherentNamed
  | 0, input => input
  | extra + 1, input => halfScaled (halfIterate extra input)

/-- Every finite halving chain preserves a supplied unit-disk certificate. -/
theorem halfIterateUnitDisk : (extra : Nat) → (input : CoherentNamed) →
    CCL.ProgressiveExp.UnitDisk input.name →
      CCL.ProgressiveExp.UnitDisk (halfIterate extra input).name
  | 0, _input, domain => domain
  | extra + 1, input, domain =>
      halfScaledUnitDisk (halfIterate extra input)
        (halfIterateUnitDisk extra input domain)

/-- Normalize a finite halving chain to one explicit dyadic-scaled sampler,
starting from any name already equivalent to the sampler at `base`. -/
def halfIterate_to_dyadicScaledFrom (base : Nat) :
    (extra : Nat) → (original start : CoherentNamed) →
      NamedEquivalent start.name
        (dyadicScaledApproximation base original.name).toNamed →
      NamedEquivalent
        (halfIterate extra start).name
        (dyadicScaledApproximation (base + extra) original.name).toNamed
  | 0, _original, _start, startEquivalent => startEquivalent
  | extra + 1, original, start, startEquivalent => by
      let previous := halfIterate extra start
      let previousApproximation :=
        dyadicScaledApproximation (base + extra) original.name
      let previousApproximationName :=
        CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
          previousApproximation
      let halfExact :=
        CCL.ProgressiveCoherence.CoherentNamed.exact dyadicHalf
      let halfConstant :=
        CCL.TranscendentalLaws.constantApproximation dyadicHalf
      let halfConstantName :=
        CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
          halfConstant
      let nextApproximation :=
        dyadicScaledApproximation ((base + extra) + 1) original.name
      have previousEquivalent :
          NamedEquivalent previous.name previousApproximationName.name :=
        halfIterate_to_dyadicScaledFrom base extra original start
          startEquivalent
      have actualToApproximationFactors :
          NamedEquivalent
            (CCL.ProgressiveTransducer.Named.mul
              halfExact.name previous.name)
            (CCL.ProgressiveTransducer.Named.mul
              halfConstantName.name previousApproximationName.name) :=
        coherentMul_respects halfExact halfConstantName
          previous previousApproximationName
          (exact_toConstantNamed dyadicHalf) previousEquivalent
      have factorsToNext :
          NamedEquivalent
            (CCL.ProgressiveTransducer.Named.mul
              halfConstantName.name previousApproximationName.name)
            nextApproximation.toNamed :=
        mulToNamed_equivalent_pointwise halfConstant previousApproximation
          nextApproximation (by
            intro index
            change inverseDyadicAt ((base + extra) + 1) *
                (CCL.ProgressiveSampling.approximation
                  original.name).sample index =
              dyadicHalf *
                (inverseDyadicAt (base + extra) *
                  (CCL.ProgressiveSampling.approximation
                    original.name).sample index)
            rw [← inverseDyadicAt_succ]
            exact RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _)
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        actualToApproximationFactors factorsToNext

/-- Every finite halving chain has the explicit inverse-dyadic sampler of its
original coherent input. -/
def halfIterate_to_dyadicScaled (extra : Nat) (input : CoherentNamed) :
    NamedEquivalent
      (halfIterate extra input).name
      (dyadicScaledApproximation extra input.name).toNamed := by
  let source := CCL.ProgressiveSampling.approximation input.name
  have baseEquivalent : NamedEquivalent input.name
      (dyadicScaledApproximation 0 input.name).toNamed :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (named_toSamplingNamed input.name)
      (approximationEquivalent_toNamed
        (approximationEquivalentOfSamplesEq source
          (dyadicScaledApproximation 0 input.name)
          (by
            intro index
            rw [dyadicScaledApproximation_sample, inverseDyadicAt_zero,
              RFAP.ConstructiveGaussian.Gaussian.one_mul])))
  simpa only [Nat.zero_add] using
    halfIterate_to_dyadicScaledFrom 0 extra input input baseEquivalent

/-- At one displayed inverse-dyadic scale, the two canonical operand
samplers add operationally to the canonical sampler of the actual input sum. -/
def dyadicScaledAdd_equivalent (exponent : Nat)
    (left right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (dyadicScaledApproximation exponent left.name).toNamed
        (dyadicScaledApproximation exponent right.name).toNamed)
      (dyadicScaledApproximation exponent
        (CCL.ProgressiveCoherence.CoherentNamed.add
          left right).name).toNamed := by
  let leftScaled := dyadicScaledApproximation exponent left.name
  let rightScaled := dyadicScaledApproximation exponent right.name
  let leftScaledName :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      leftScaled
  let rightScaledName :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      rightScaled
  let sumInput :=
    CCL.ProgressiveCoherence.CoherentNamed.add left right
  let sourceSum := sampledSumApproximation left.name right.name
  let directScaledSum := contractiveScaleApproximation
    (inverseDyadicAt exponent) (normSq_inverseDyadicAt_le_one exponent)
      sourceSum
  let sumScaled := dyadicScaledApproximation exponent sumInput.name
  have addToSampled :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.add
          leftScaledName.name rightScaledName.name)
        (sampledSumApproximation
          leftScaledName.name rightScaledName.name).toNamed :=
    coherentAdd_toNamed leftScaledName rightScaledName
  have sampledToDirect :
      NamedEquivalent
        (sampledSumApproximation
          leftScaledName.name rightScaledName.name).toNamed
        directScaledSum.toNamed :=
    approximationEquivalent_toNamed
      (pointwiseSumApproximation_respects
        (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
          leftScaled)
        (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
          rightScaled)
        (by intro index; rfl)
        (by
          intro index
          change inverseDyadicAt exponent *
                ((CCL.ProgressiveSampling.approximation
                    left.name).sample index +
                  (CCL.ProgressiveSampling.approximation
                    right.name).sample index) =
              inverseDyadicAt exponent *
                  (CCL.ProgressiveSampling.approximation
                    left.name).sample index +
                inverseDyadicAt exponent *
                  (CCL.ProgressiveSampling.approximation
                    right.name).sample index
          exact RFAP.ConstructiveGaussian.Gaussian.left_distrib _ _ _))
  have sumSamplerToDirect : Equivalent
      (CCL.ProgressiveSampling.approximation sumInput.name)
      sourceSum :=
    CCL.OperationalEquivalence.Equivalent.trans
      (coherentAdd_toNamed left right)
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
        sourceSum)
  have sumScaledToDirect : Equivalent sumScaled directScaledSum :=
    contractiveScaleApproximation_respects
      (inverseDyadicAt exponent) (normSq_inverseDyadicAt_le_one exponent)
      sumSamplerToDirect
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    addToSampled
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      sampledToDirect
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (approximationEquivalent_toNamed sumScaledToDirect)))

theorem inverseDyadicAt_mul (base extra : Nat) :
    inverseDyadicAt extra * inverseDyadicAt base =
      inverseDyadicAt (base + extra) := by
  induction extra with
  | zero =>
      rw [inverseDyadicAt_zero,
        RFAP.ConstructiveGaussian.Gaussian.one_mul, Nat.add_zero]
  | succ extra inductionHypothesis =>
      calc
        inverseDyadicAt (extra + 1) * inverseDyadicAt base =
            (dyadicHalf * inverseDyadicAt extra) * inverseDyadicAt base := by
          rw [inverseDyadicAt_succ]
        _ = dyadicHalf *
              (inverseDyadicAt extra * inverseDyadicAt base) :=
          RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
        _ = dyadicHalf * inverseDyadicAt (base + extra) := by
          rw [inductionHypothesis]
        _ = inverseDyadicAt ((base + extra) + 1) :=
          inverseDyadicAt_succ (base + extra)
        _ = inverseDyadicAt (base + (extra + 1)) :=
          congrArg inverseDyadicAt (Nat.add_succ base extra).symm

/-- A possible reading after finitely many actual halvings is an explicitly
displayed inverse-dyadic multiple of a possible original reading. -/
theorem halfIterate_possible (extra : Nat) (input : CoherentNamed)
    {value : Gaussian}
    (possible : (halfIterate extra input).name.process.Possible
      (halfIterate extra input).name.state value) :
    ∃ sourceValue,
      input.name.process.Possible input.name.state sourceValue ∧
        value = inverseDyadicAt extra * sourceValue := by
  induction extra generalizing value with
  | zero =>
      exact ⟨value, possible, by rw [inverseDyadicAt_zero,
        RFAP.ConstructiveGaussian.Gaussian.one_mul]⟩
  | succ extra inductionHypothesis =>
      rcases possible with ⟨scaleValue, previousValue,
        scalePossible, previousPossible, rfl⟩
      change scaleValue = dyadicHalf at scalePossible
      subst scaleValue
      rcases inductionHypothesis previousPossible with
        ⟨sourceValue, sourcePossible, previousEqual⟩
      refine ⟨sourceValue, sourcePossible, ?_⟩
      rw [previousEqual, ← RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
        inverseDyadicAt_succ]

/-- The actual automatically selected scaled input, with its coherence
certificate. -/
def automaticScaled (input : CoherentNamed) : CoherentNamed :=
  { name := CCL.ProgressiveExpRange.scaledInput input.name
    coherent :=
      CCL.ProgressiveCoherence.Coherent.mul
        (CCL.ProgressiveCoherence.Coherent.exact
          (CCL.ProgressiveExpRange.inverseDyadic input.name))
        input.coherent }

theorem automaticScaled_inverse_eq (input : Named) :
    CCL.ProgressiveExpRange.inverseDyadic input =
      inverseDyadicAt
        (CCL.ProgressiveExpRange.rangeExponent input) :=
  rfl

/-- The actual automatic scaling process is operationally its explicit
inverse-dyadic sampler. -/
def automaticScaled_to_dyadicScaled (input : CoherentNamed) :
    NamedEquivalent
      (automaticScaled input).name
      (dyadicScaledApproximation
        (CCL.ProgressiveExpRange.rangeExponent input.name)
        input.name).toNamed := by
  let scale := CCL.ProgressiveCoherence.CoherentNamed.exact
    (CCL.ProgressiveExpRange.inverseDyadic input.name)
  let product := sampledProductApproximation scale.name input.name
  let target := dyadicScaledApproximation
    (CCL.ProgressiveExpRange.rangeExponent input.name) input.name
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentMul_toNamed scale input)
    (approximationEquivalent_toNamed
      (approximationEquivalentOfSamplesEq product target
        (by intro index; rfl)))

/-- Automatic scaling followed by any finite number of halvings normalizes to
the one sampler at the sum of the two displayed exponents. -/
def halfIterateAutomatic_to_dyadicScaled (extra : Nat)
    (input : CoherentNamed) :
    NamedEquivalent
      (halfIterate extra (automaticScaled input)).name
      (dyadicScaledApproximation
        (CCL.ProgressiveExpRange.rangeExponent input.name + extra)
        input.name).toNamed :=
  halfIterate_to_dyadicScaledFrom
    (CCL.ProgressiveExpRange.rangeExponent input.name)
    extra input (automaticScaled input)
      (automaticScaled_to_dyadicScaled input)

/-- Semantic form of the same normalization, used only to transfer the
finite unit-disk certificate to the common-scale sum process. -/
theorem halfIterateAutomatic_possible (extra : Nat)
    (input : CoherentNamed) {value : Gaussian}
    (possible :
      (halfIterate extra (automaticScaled input)).name.process.Possible
        (halfIterate extra (automaticScaled input)).name.state value) :
    ∃ sourceValue,
      input.name.process.Possible input.name.state sourceValue ∧
        value = inverseDyadicAt
          (CCL.ProgressiveExpRange.rangeExponent input.name + extra) *
            sourceValue := by
  rcases halfIterate_possible extra (automaticScaled input) possible with
    ⟨scaledValue, scaledPossible, valueEqual⟩
  rcases scaledPossible with ⟨scaleValue, sourceValue,
    scalePossible, sourcePossible, scaledEqual⟩
  change scaleValue =
    CCL.ProgressiveExpRange.inverseDyadic input.name at scalePossible
  subst scaleValue
  subst scaledValue
  refine ⟨sourceValue, sourcePossible, ?_⟩
  rw [valueEqual, automaticScaled_inverse_eq,
    ← RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
    inverseDyadicAt_mul]

/-- The actual sum of two independently scheduled automatically scaled names
at one common exponent satisfies the local unit-disk contract. -/
theorem automaticCommonAddUnitDisk
    (xExtra yExtra sumExtra common : Nat)
    (left right : CoherentNamed)
    (xCommon :
      CCL.ProgressiveExpRange.rangeExponent left.name + xExtra =
        common)
    (yCommon :
      CCL.ProgressiveExpRange.rangeExponent right.name + yExtra =
        common)
    (sumCommon :
      CCL.ProgressiveExpRange.rangeExponent
          (CCL.ProgressiveCoherence.CoherentNamed.add
            left right).name + sumExtra = common) :
    CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add
        (halfIterate xExtra (automaticScaled left)).name
        (halfIterate yExtra (automaticScaled right)).name) where
  possible_unit := by
    intro value possible
    let sumInput :=
      CCL.ProgressiveCoherence.CoherentNamed.add left right
    rcases possible with ⟨leftValue, rightValue,
      leftPossible, rightPossible, rfl⟩
    rcases halfIterateAutomatic_possible xExtra left leftPossible with
      ⟨leftSource, leftSourcePossible, leftEqual⟩
    rcases halfIterateAutomatic_possible yExtra right rightPossible with
      ⟨rightSource, rightSourcePossible, rightEqual⟩
    rw [xCommon] at leftEqual
    rw [yCommon] at rightEqual
    rw [leftEqual, rightEqual]
    have sumPossible :
        sumInput.name.process.Possible sumInput.name.state
          (leftSource + rightSource) :=
      ⟨leftSource, rightSource, leftSourcePossible, rightSourcePossible, rfl⟩
    have sumBound :=
      CCL.ProgressiveExpRange.possible_normSq_le_inputBound
        sumInput.name sumPossible
    have sumBaseLeCommon :
        CCL.ProgressiveExpRange.rangeExponent sumInput.name ≤
          common := by
      rw [← sumCommon]
      exact Nat.le_add_right _ _
    have radiusOrder :
        CCL.FiniteGeometric.quarterRadius
            (CCL.ProgressiveExpRange.inputBound sumInput.name)
            common ≤
          CCL.FiniteGeometric.quarterRadius
            (CCL.ProgressiveExpRange.inputBound sumInput.name)
            (CCL.ProgressiveExpRange.rangeExponent
              sumInput.name) :=
      quarterRadius_index_antitone
        (CCL.ProgressiveExpRange.inputBound_nonneg sumInput.name)
        sumBaseLeCommon
    have identity :
        inverseDyadicAt common * leftSource +
            inverseDyadicAt common * rightSource =
          inverseDyadicAt common * (leftSource + rightSource) :=
      (RFAP.ConstructiveGaussian.Gaussian.left_distrib _ _ _).symm
    rw [identity, normSq_mul, normSq_inverseDyadicAt]
    calc
      CCL.FiniteGeometric.quarterRadius 1 common *
          normSq (leftSource + rightSource) ≤
        CCL.FiniteGeometric.quarterRadius 1 common *
          CCL.ProgressiveExpRange.inputBound sumInput.name :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct sumBound
          (CCL.FiniteGeometric.quarterRadius_nonneg (by decide) _)
      _ = CCL.FiniteGeometric.quarterRadius
          (CCL.ProgressiveExpRange.inputBound sumInput.name)
          common := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
      _ ≤ CCL.FiniteGeometric.quarterRadius
          (CCL.ProgressiveExpRange.inputBound sumInput.name)
          (CCL.ProgressiveExpRange.rangeExponent sumInput.name) :=
        radiusOrder
      _ ≤ 1 :=
        (CCL.ProgressiveExpRange.rangeExponent_accurate
          sumInput.name).le

/-- The three independently automatic scaling paths become operationally
additive after a finite maximum raises them to one common exponent. -/
def automaticCommonScaledAdd_equivalent
    (xExtra yExtra sumExtra common : Nat)
    (left right : CoherentNamed)
    (xCommon :
      CCL.ProgressiveExpRange.rangeExponent left.name + xExtra =
        common)
    (yCommon :
      CCL.ProgressiveExpRange.rangeExponent right.name + yExtra =
        common)
    (sumCommon :
      CCL.ProgressiveExpRange.rangeExponent
          (CCL.ProgressiveCoherence.CoherentNamed.add
            left right).name + sumExtra = common) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (halfIterate xExtra (automaticScaled left)).name
        (halfIterate yExtra (automaticScaled right)).name)
      (halfIterate sumExtra
        (automaticScaled
          (CCL.ProgressiveCoherence.CoherentNamed.add
            left right))).name := by
  let sumInput :=
    CCL.ProgressiveCoherence.CoherentNamed.add left right
  let xNormalized := halfIterate xExtra (automaticScaled left)
  let yNormalized := halfIterate yExtra (automaticScaled right)
  let sumNormalized := halfIterate sumExtra (automaticScaled sumInput)
  let xScaledApproximation := dyadicScaledApproximation common left.name
  let yScaledApproximation := dyadicScaledApproximation common right.name
  let sumScaledApproximation := dyadicScaledApproximation common sumInput.name
  let xScaled :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      xScaledApproximation
  let yScaled :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      yScaledApproximation
  have xEquivalent : NamedEquivalent xNormalized.name xScaled.name := by
    simpa only [xNormalized, xScaled, xScaledApproximation, xCommon,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      halfIterateAutomatic_to_dyadicScaled xExtra left
  have yEquivalent : NamedEquivalent yNormalized.name yScaled.name := by
    simpa only [yNormalized, yScaled, yScaledApproximation, yCommon,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      halfIterateAutomatic_to_dyadicScaled yExtra right
  have sumEquivalent : NamedEquivalent
      sumNormalized.name sumScaledApproximation.toNamed := by
    simpa only [sumNormalized, sumScaledApproximation, sumInput, sumCommon]
      using halfIterateAutomatic_to_dyadicScaled sumExtra sumInput
  have inputsToScaled :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.add
          xNormalized.name yNormalized.name)
        (CCL.ProgressiveTransducer.Named.add
          xScaled.name yScaled.name) :=
    coherentAdd_respects xNormalized xScaled yNormalized yScaled
      xEquivalent yEquivalent
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    inputsToScaled
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (dyadicScaledAdd_equivalent common left right)
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        sumEquivalent))

/-- Raising the displayed restoration exponent by any finite amount while
halving the arbitrary coherent input the same number of times preserves the
global exponential name operationally. -/
def coherentDyadicExp_raise (base extra : Nat) (input : CoherentNamed)
    (domain : CCL.ProgressiveExp.UnitDisk input.name) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.squareIterate (base + extra)
        (CCL.ProgressiveExp.named (halfIterate extra input).name
          (halfIterateUnitDisk extra input domain)))
      (CCL.ProgressiveExpRange.squareIterate base
        (CCL.ProgressiveExp.named input.name domain)) := by
  induction extra with
  | zero =>
      exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  | succ extra inductionHypothesis =>
      have step := coherentDyadicExp_step (base + extra)
        (halfIterate extra input) (halfIterateUnitDisk extra input domain)
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (by simpa only [Nat.add_succ, halfIterate] using step)
        inductionHypothesis

/-- Coherent restored local exponential at an explicitly supplied finite
range exponent. -/
def restoredLocalExp (exponent : Nat) (input : CoherentNamed)
    (domain : CCL.ProgressiveExp.UnitDisk input.name) :
    CoherentNamed :=
  { name := CCL.ProgressiveExpRange.squareIterate exponent
      (CCL.ProgressiveExp.named input.name domain)
    coherent := squareIterateCoherent exponent _
      (localExpCoherent input.name domain) }

/-- Global exponential addition with three independent starting exponents,
reduced to one explicit finite compatibility certificate between the three
common-scale input names.  All exponent raising and output algebra is proved
here; no completed operand value is selected. -/
def coherentDyadicExp_add_independent
    (xBase xExtra yBase yExtra sumBase sumExtra common : Nat)
    (xInput yInput sumInput : CoherentNamed)
    (xDomain : CCL.ProgressiveExp.UnitDisk xInput.name)
    (yDomain : CCL.ProgressiveExp.UnitDisk yInput.name)
    (sumDomain : CCL.ProgressiveExp.UnitDisk sumInput.name)
    (xCommon : xBase + xExtra = common)
    (yCommon : yBase + yExtra = common)
    (sumCommon : sumBase + sumExtra = common)
    (commonAddDomain : CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveTransducer.Named.add
        (halfIterate xExtra xInput).name
        (halfIterate yExtra yInput).name))
    (scaledAdd : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (halfIterate xExtra xInput).name
        (halfIterate yExtra yInput).name)
      (halfIterate sumExtra sumInput).name) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (restoredLocalExp xBase xInput xDomain).name
        (restoredLocalExp yBase yInput yDomain).name)
      (restoredLocalExp sumBase sumInput sumDomain).name := by
  let xCommonInput := halfIterate xExtra xInput
  let yCommonInput := halfIterate yExtra yInput
  let sumCommonInput := halfIterate sumExtra sumInput
  let xCommonDomain := halfIterateUnitDisk xExtra xInput xDomain
  let yCommonDomain := halfIterateUnitDisk yExtra yInput yDomain
  let sumCommonDomain := halfIterateUnitDisk sumExtra sumInput sumDomain
  let xBaseExp := restoredLocalExp xBase xInput xDomain
  let yBaseExp := restoredLocalExp yBase yInput yDomain
  let sumBaseExp := restoredLocalExp sumBase sumInput sumDomain
  let xCommonExp := restoredLocalExp common xCommonInput xCommonDomain
  let yCommonExp := restoredLocalExp common yCommonInput yCommonDomain
  let sumCommonExp := restoredLocalExp common sumCommonInput sumCommonDomain
  have xRaise : NamedEquivalent xCommonExp.name xBaseExp.name := by
    simpa only [xCommonExp, xCommonInput, xBaseExp, restoredLocalExp, xCommon]
      using coherentDyadicExp_raise xBase xExtra xInput xDomain
  have yRaise : NamedEquivalent yCommonExp.name yBaseExp.name := by
    simpa only [yCommonExp, yCommonInput, yBaseExp, restoredLocalExp, yCommon]
      using coherentDyadicExp_raise yBase yExtra yInput yDomain
  have sumRaise : NamedEquivalent sumCommonExp.name sumBaseExp.name := by
    simpa only [sumCommonExp, sumCommonInput, sumBaseExp, restoredLocalExp,
      sumCommon] using
        coherentDyadicExp_raise sumBase sumExtra sumInput sumDomain
  have factorsToCommon :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          xBaseExp.name yBaseExp.name)
        (CCL.ProgressiveTransducer.Named.mul
          xCommonExp.name yCommonExp.name) :=
    coherentMul_respects xBaseExp xCommonExp yBaseExp yCommonExp
      (CCL.OperationalEquivalence.NamedEquivalent.symm xRaise)
      (CCL.OperationalEquivalence.NamedEquivalent.symm yRaise)
  have commonLaw := coherentLocalExp_add_after_squareIterate common
    xCommonInput yCommonInput xCommonDomain yCommonDomain commonAddDomain
  let commonAddInput :=
    CCL.ProgressiveCoherence.CoherentNamed.add
      xCommonInput yCommonInput
  let commonAddExp : CoherentNamed :=
    { name := CCL.ProgressiveExp.named
        commonAddInput.name commonAddDomain
      coherent := localExpCoherent commonAddInput.name commonAddDomain }
  let sumLocalExp : CoherentNamed :=
    { name := CCL.ProgressiveExp.named
        sumCommonInput.name sumCommonDomain
      coherent := localExpCoherent sumCommonInput.name sumCommonDomain }
  have localToSum : NamedEquivalent commonAddExp.name sumLocalExp.name :=
    localExpNamed_respects commonAddDomain sumCommonDomain scaledAdd
  have restoredToSum : NamedEquivalent
      (CCL.ProgressiveExpRange.squareIterate common
        commonAddExp.name)
      sumCommonExp.name := by
    simpa only [sumCommonExp, restoredLocalExp] using
      squareIterate_respects common commonAddExp sumLocalExp localToSum
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    factorsToCommon
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (by simpa only [xCommonExp, yCommonExp, restoredLocalExp,
          commonAddExp, commonAddInput,
          CCL.ProgressiveCoherence.CoherentNamed.add]
        using commonLaw)
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        restoredToSum sumRaise))

/-- Global exponential addition for arbitrary coherent progressive CCL
inputs.  The three automatic range reductions may choose different finite
exponents; a computed maximum, explicit halving chains, and finite sampler
normalization reconcile them without selecting completed input values. -/
def automaticExp_add (left right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.named left.name)
        (CCL.ProgressiveExpRange.named right.name))
      (CCL.ProgressiveExpRange.named
        (CCL.ProgressiveTransducer.Named.add
          left.name right.name)) := by
  let sumInput :=
    CCL.ProgressiveCoherence.CoherentNamed.add left right
  let xBase :=
    CCL.ProgressiveExpRange.rangeExponent left.name
  let yBase :=
    CCL.ProgressiveExpRange.rangeExponent right.name
  let sumBase :=
    CCL.ProgressiveExpRange.rangeExponent sumInput.name
  let common := max xBase (max yBase sumBase)
  let xExtra := common - xBase
  let yExtra := common - yBase
  let sumExtra := common - sumBase
  have xOrder : xBase ≤ common := Nat.le_max_left _ _
  have yOrder : yBase ≤ common :=
    (Nat.le_max_left yBase sumBase).trans (Nat.le_max_right _ _)
  have sumOrder : sumBase ≤ common :=
    (Nat.le_max_right yBase sumBase).trans (Nat.le_max_right _ _)
  have xCommon : xBase + xExtra = common := by
    dsimp only [xExtra]
    rw [Nat.add_comm, Nat.sub_add_cancel xOrder]
  have yCommon : yBase + yExtra = common := by
    dsimp only [yExtra]
    rw [Nat.add_comm, Nat.sub_add_cancel yOrder]
  have sumCommon : sumBase + sumExtra = common := by
    dsimp only [sumExtra]
    rw [Nat.add_comm, Nat.sub_add_cancel sumOrder]
  let xDomain := CCL.ProgressiveExpRange.scaledDomain left.name
  let yDomain := CCL.ProgressiveExpRange.scaledDomain right.name
  let sumDomain :=
    CCL.ProgressiveExpRange.scaledDomain sumInput.name
  let commonAddDomain := automaticCommonAddUnitDisk
    xExtra yExtra sumExtra common left right xCommon yCommon sumCommon
  let scaledAdd := automaticCommonScaledAdd_equivalent
    xExtra yExtra sumExtra common left right xCommon yCommon sumCommon
  simpa only [xBase, yBase, sumBase, sumInput, restoredLocalExp,
      automaticScaled, CCL.ProgressiveExpRange.named,
      CCL.ProgressiveCoherence.CoherentNamed.add] using
    coherentDyadicExp_add_independent
      xBase xExtra yBase yExtra sumBase sumExtra common
      (automaticScaled left) (automaticScaled right)
      (automaticScaled sumInput) xDomain yDomain sumDomain
      xCommon yCommon sumCommon commonAddDomain scaledAdd

/-- The total automatically range-reduced exponential transform respects
finite operational equality of arbitrary coherent progressive inputs, even
when the two input processes select different range exponents. -/
def automaticExp_respects (left right : CoherentNamed)
    (equivalent : NamedEquivalent left.name right.name) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named left.name)
      (CCL.ProgressiveExpRange.named right.name) := by
  let leftBase :=
    CCL.ProgressiveExpRange.rangeExponent left.name
  let rightBase :=
    CCL.ProgressiveExpRange.rangeExponent right.name
  let common := max leftBase rightBase
  let leftExtra := common - leftBase
  let rightExtra := common - rightBase
  have leftOrder : leftBase ≤ common := Nat.le_max_left _ _
  have rightOrder : rightBase ≤ common := Nat.le_max_right _ _
  have leftCommon : leftBase + leftExtra = common := by
    dsimp only [leftExtra]
    rw [Nat.add_comm, Nat.sub_add_cancel leftOrder]
  have rightCommon : rightBase + rightExtra = common := by
    dsimp only [rightExtra]
    rw [Nat.add_comm, Nat.sub_add_cancel rightOrder]
  let leftAutomaticInput := automaticScaled left
  let rightAutomaticInput := automaticScaled right
  let leftDomain :=
    CCL.ProgressiveExpRange.scaledDomain left.name
  let rightDomain :=
    CCL.ProgressiveExpRange.scaledDomain right.name
  let leftCommonInput := halfIterate leftExtra leftAutomaticInput
  let rightCommonInput := halfIterate rightExtra rightAutomaticInput
  let leftCommonDomain := halfIterateUnitDisk leftExtra
    leftAutomaticInput leftDomain
  let rightCommonDomain := halfIterateUnitDisk rightExtra
    rightAutomaticInput rightDomain
  let leftScaledApproximation := dyadicScaledApproximation common left.name
  let rightScaledApproximation := dyadicScaledApproximation common right.name
  have leftNormalized : NamedEquivalent leftCommonInput.name
      leftScaledApproximation.toNamed := by
    simpa only [leftCommonInput, leftAutomaticInput,
      leftScaledApproximation, leftCommon, leftBase] using
        halfIterateAutomatic_to_dyadicScaled leftExtra left
  have rightNormalized : NamedEquivalent rightCommonInput.name
      rightScaledApproximation.toNamed := by
    simpa only [rightCommonInput, rightAutomaticInput,
      rightScaledApproximation, rightCommon, rightBase] using
        halfIterateAutomatic_to_dyadicScaled rightExtra right
  have scaledEquivalent : NamedEquivalent
      leftScaledApproximation.toNamed rightScaledApproximation.toNamed :=
    approximationEquivalent_toNamed
      (contractiveScaleApproximation_respects (inverseDyadicAt common)
        (normSq_inverseDyadicAt_le_one common) equivalent)
  have commonInputEquivalent : NamedEquivalent
      leftCommonInput.name rightCommonInput.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      leftNormalized
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        scaledEquivalent
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          rightNormalized))
  let leftCommonLocal : CoherentNamed :=
    { name := CCL.ProgressiveExp.named
        leftCommonInput.name leftCommonDomain
      coherent := localExpCoherent leftCommonInput.name leftCommonDomain }
  let rightCommonLocal : CoherentNamed :=
    { name := CCL.ProgressiveExp.named
        rightCommonInput.name rightCommonDomain
      coherent := localExpCoherent rightCommonInput.name rightCommonDomain }
  have commonLocalEquivalent : NamedEquivalent
      leftCommonLocal.name rightCommonLocal.name :=
    localExpNamed_respects leftCommonDomain rightCommonDomain
      commonInputEquivalent
  have commonRestoredEquivalent : NamedEquivalent
      (CCL.ProgressiveExpRange.squareIterate common
        leftCommonLocal.name)
      (CCL.ProgressiveExpRange.squareIterate common
        rightCommonLocal.name) :=
    squareIterate_respects common leftCommonLocal rightCommonLocal
      commonLocalEquivalent
  have leftRaise := coherentDyadicExp_raise leftBase leftExtra
    leftAutomaticInput leftDomain
  have rightRaise := coherentDyadicExp_raise rightBase rightExtra
    rightAutomaticInput rightDomain
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (by simpa only [leftCommon, leftCommonInput, leftAutomaticInput,
          leftCommonLocal, leftCommonDomain, leftBase, leftDomain,
          automaticScaled, CCL.ProgressiveExpRange.named]
        using leftRaise))
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      commonRestoredEquivalent
      (by simpa only [rightCommon, rightCommonInput, rightAutomaticInput,
          rightCommonLocal, rightCommonDomain, rightBase, rightDomain,
          automaticScaled, CCL.ProgressiveExpRange.named]
        using rightRaise))

/-- If every possible reading of a coherent input is already in the local
unit disk, the total automatic exponential is operationally the direct local
exponential, even if its conservative initial ball selected a nonzero range
exponent. -/
def automaticExp_toLocal (input : CoherentNamed)
    (domain : CCL.ProgressiveExp.UnitDisk input.name) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named input.name)
      (CCL.ProgressiveExp.named input.name domain) := by
  let exponent :=
    CCL.ProgressiveExpRange.rangeExponent input.name
  let automaticInput := automaticScaled input
  let automaticDomain :=
    CCL.ProgressiveExpRange.scaledDomain input.name
  let halvedInput := halfIterate exponent input
  let halvedDomain := halfIterateUnitDisk exponent input domain
  have automaticToScaled := automaticScaled_to_dyadicScaled input
  have halvedToScaled := halfIterate_to_dyadicScaled exponent input
  have inputEquivalent : NamedEquivalent
      automaticInput.name halvedInput.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      automaticToScaled
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        halvedToScaled)
  let automaticLocal : CoherentNamed :=
    { name := CCL.ProgressiveExp.named
        automaticInput.name automaticDomain
      coherent := localExpCoherent automaticInput.name automaticDomain }
  let halvedLocal : CoherentNamed :=
    { name := CCL.ProgressiveExp.named
        halvedInput.name halvedDomain
      coherent := localExpCoherent halvedInput.name halvedDomain }
  have localEquivalent : NamedEquivalent
      automaticLocal.name halvedLocal.name :=
    localExpNamed_respects automaticDomain halvedDomain inputEquivalent
  have restoredEquivalent := squareIterate_respects exponent
    automaticLocal halvedLocal localEquivalent
  have halvedToLocal := coherentDyadicExp_raise 0 exponent input domain
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by simpa only [exponent, automaticInput, automaticDomain, automaticLocal,
        automaticScaled, CCL.ProgressiveExpRange.named]
      using restoredEquivalent)
    (by simpa only [Nat.zero_add, halvedInput, halvedDomain, halvedLocal,
        CCL.ProgressiveExpRange.squareIterate]
      using halvedToLocal)

theorem dyadicScale_unit_succ {exponent : Nat} {value : Gaussian}
    (unit : normSq (dyadicScale exponent value) ≤ 1) :
    normSq (dyadicScale (exponent + 1) value) ≤ 1 := by
  rw [dyadicScale, normSq_mul, normSq_dyadicHalf]
  calc
    (1 / 4 : Coordinate) * normSq (dyadicScale exponent value) ≤
        (1 / 4 : Coordinate) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct unit (by decide)
    _ ≤ 1 := by decide

theorem dyadicScale_unit_add (base extra : Nat) (value : Gaussian)
    (unit : normSq (dyadicScale base value) ≤ 1) :
    normSq (dyadicScale (base + extra) value) ≤ 1 := by
  induction extra with
  | zero => exact unit
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      exact dyadicScale_unit_succ inductionHypothesis

/-- Adjacent admissible dyadic exponents give operationally equivalent
restored exponential names. -/
def exactDyadicExp_step (exponent : Nat) (value : Gaussian)
    (unit : normSq (dyadicScale exponent value) ≤ 1) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.squareIterate (exponent + 1)
        (exactLocalExpNamed (dyadicScale (exponent + 1) value)
          (dyadicScale_unit_succ unit)))
      (CCL.ProgressiveExpRange.squareIterate exponent
        (exactLocalExpNamed (dyadicScale exponent value) unit)) := by
  have doubleUnit :
      normSq
          (dyadicScale (exponent + 1) value +
            dyadicScale (exponent + 1) value) ≤ 1 := by
    rw [dyadicScale_succ_add_self]
    exact unit
  simpa only [dyadicScale_succ_add_self] using
    exactLocalExp_doubling_after_squareIterate exponent
      (dyadicScale (exponent + 1) value)
      (dyadicScale_unit_succ unit) doubleUnit

/-- Raising any admissible displayed dyadic exponent by a finite amount does
not change the restored exact exponential name operationally. -/
def exactDyadicExp_raise (base extra : Nat) (value : Gaussian)
    (unit : normSq (dyadicScale base value) ≤ 1) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.squareIterate (base + extra)
        (exactLocalExpNamed (dyadicScale (base + extra) value)
          (dyadicScale_unit_add base extra value unit)))
      (CCL.ProgressiveExpRange.squareIterate base
        (exactLocalExpNamed (dyadicScale base value) unit)) := by
  induction extra with
  | zero =>
      exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  | succ extra inductionHypothesis =>
      have step := exactDyadicExp_step (base + extra) value
        (dyadicScale_unit_add base extra value unit)
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (by simpa only [Nat.add_succ] using step)
        inductionHypothesis

@[simp] theorem dyadicScale_add (exponent : Nat) (left right : Gaussian) :
    dyadicScale exponent (left + right) =
      dyadicScale exponent left + dyadicScale exponent right := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [dyadicScale, dyadicScale, dyadicScale, inductionHypothesis]
      exact RFAP.ConstructiveGaussian.Gaussian.left_distrib _ _ _

/-- At one common admissible dyadic exponent, the restored exact CCL
exponential is an operational homomorphism from addition to multiplication. -/
def exactDyadicExp_add_at_common_exponent (exponent : Nat)
    (x y : Gaussian)
    (xUnit : normSq (dyadicScale exponent x) ≤ 1)
    (yUnit : normSq (dyadicScale exponent y) ≤ 1)
    (sumUnit : normSq (dyadicScale exponent (x + y)) ≤ 1) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.squareIterate exponent
          (exactLocalExpNamed (dyadicScale exponent x) xUnit))
        (CCL.ProgressiveExpRange.squareIterate exponent
          (exactLocalExpNamed (dyadicScale exponent y) yUnit)))
      (CCL.ProgressiveExpRange.squareIterate exponent
        (exactLocalExpNamed (dyadicScale exponent (x + y)) sumUnit)) := by
  have scaledSumUnit :
      normSq (dyadicScale exponent x + dyadicScale exponent y) ≤ 1 := by
    rw [← dyadicScale_add]
    exact sumUnit
  simpa only [← dyadicScale_add] using
    exactLocalExp_add_after_squareIterate exponent xUnit yUnit scaledSumUnit

theorem dyadicScale_unit_of_le {lower upper : Nat} (value : Gaussian)
    (order : lower ≤ upper)
    (unit : normSq (dyadicScale lower value) ≤ 1) :
    normSq (dyadicScale upper value) ≤ 1 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  exact dyadicScale_unit_add lower extra value unit

/-- Coherent exact exponential name at a displayed admissible dyadic
exponent. -/
def exactDyadicExpCoherent (exponent : Nat) (value : Gaussian)
    (unit : normSq (dyadicScale exponent value) ≤ 1) : CoherentNamed :=
  { name := CCL.ProgressiveExpRange.squareIterate exponent
      (exactLocalExpNamed (dyadicScale exponent value) unit)
    coherent := squareIterateCoherent exponent _
      (CCL.ProgressiveCoherence.Coherent.ofApproximation
        (exactLocalExpApproximation (dyadicScale exponent value) unit)) }

/-- Ordered admissible dyadic exponents are interchangeable in the restored
exact exponential name. -/
def exactDyadicExp_raise_to {lower upper : Nat} (value : Gaussian)
    (order : lower ≤ upper)
    (unit : normSq (dyadicScale lower value) ≤ 1) :
    NamedEquivalent
      (exactDyadicExpCoherent upper value
        (dyadicScale_unit_of_le value order unit)).name
      (exactDyadicExpCoherent lower value unit).name := by
  let extra := upper - lower
  have sumEq : lower + extra = upper := by
    dsimp only [extra]
    rw [Nat.add_comm, Nat.sub_add_cancel order]
  simpa only [exactDyadicExpCoherent, sumEq] using
    exactDyadicExp_raise lower extra value unit

/-- Exact Gaussian-rational inputs may choose three independent admissible
dyadic exponents for `x`, `y`, and `x+y`.  A finite maximum raises all three
to one common exponent, applies the common-exponent law, and lowers the sum
side again. -/
def exactDyadicExp_add_independent
    (xExponent yExponent sumExponent : Nat) (x y : Gaussian)
    (xUnit : normSq (dyadicScale xExponent x) ≤ 1)
    (yUnit : normSq (dyadicScale yExponent y) ≤ 1)
    (sumUnit : normSq (dyadicScale sumExponent (x + y)) ≤ 1) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (exactDyadicExpCoherent xExponent x xUnit).name
        (exactDyadicExpCoherent yExponent y yUnit).name)
      (exactDyadicExpCoherent sumExponent (x + y) sumUnit).name := by
  let common := max xExponent (max yExponent sumExponent)
  have xOrder : xExponent ≤ common := Nat.le_max_left _ _
  have yOrder : yExponent ≤ common :=
    (Nat.le_max_left yExponent sumExponent).trans (Nat.le_max_right _ _)
  have sumOrder : sumExponent ≤ common :=
    (Nat.le_max_right yExponent sumExponent).trans (Nat.le_max_right _ _)
  let xCommonUnit := dyadicScale_unit_of_le x xOrder xUnit
  let yCommonUnit := dyadicScale_unit_of_le y yOrder yUnit
  let sumCommonUnit := dyadicScale_unit_of_le (x + y) sumOrder sumUnit
  let xBase := exactDyadicExpCoherent xExponent x xUnit
  let yBase := exactDyadicExpCoherent yExponent y yUnit
  let sumBase := exactDyadicExpCoherent sumExponent (x + y) sumUnit
  let xCommon := exactDyadicExpCoherent common x xCommonUnit
  let yCommon := exactDyadicExpCoherent common y yCommonUnit
  have factorsToCommon :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          xBase.name yBase.name)
        (CCL.ProgressiveTransducer.Named.mul
          xCommon.name yCommon.name) :=
    coherentMul_respects xBase xCommon yBase yCommon
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (exactDyadicExp_raise_to x xOrder xUnit))
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (exactDyadicExp_raise_to y yOrder yUnit))
  have commonLaw :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          xCommon.name yCommon.name)
        (exactDyadicExpCoherent common (x + y) sumCommonUnit).name :=
    exactDyadicExp_add_at_common_exponent common x y
      xCommonUnit yCommonUnit sumCommonUnit
  have sumFromCommon :
      NamedEquivalent
        (exactDyadicExpCoherent common (x + y) sumCommonUnit).name
        sumBase.name :=
    exactDyadicExp_raise_to (x + y) sumOrder sumUnit
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    factorsToCommon
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      commonLaw sumFromCommon)

/-- Actual CCL multiplication of two exact displayed rational names is
operationally the exact displayed product. -/
def exactMul_named_equivalent (left right : Gaussian) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveTransducer.Named.exact left)
        (CCL.ProgressiveTransducer.Named.exact right))
      (CCL.ProgressiveTransducer.Named.exact (left * right)) :=
  CCL.OperationalEquivalence.Equivalent.of_constant_samples
    _ _ (left * right) (by intro index; rfl) (by intro index; rfl)

theorem inverseDyadic_exact_mul_eq_dyadicScale (value : Gaussian) :
    CCL.ProgressiveExpRange.inverseDyadic
          (CCL.ProgressiveTransducer.Named.exact value) * value =
      dyadicScale
        (CCL.ProgressiveExpRange.rangeExponent
          (CCL.ProgressiveTransducer.Named.exact value)) value := by
  exact (dyadicScale_eq_inversePower
    (CCL.ProgressiveExpRange.rangeExponent
      (CCL.ProgressiveTransducer.Named.exact value)) value).symm

theorem automaticExactDyadicScale_unit (value : Gaussian) :
    normSq
        (dyadicScale
          (CCL.ProgressiveExpRange.rangeExponent
            (CCL.ProgressiveTransducer.Named.exact value)) value) ≤
      1 := by
  let input := CCL.ProgressiveTransducer.Named.exact value
  have possible :
      (CCL.ProgressiveExpRange.scaledInput input).process.Possible
        (CCL.ProgressiveExpRange.scaledInput input).state
        (CCL.ProgressiveExpRange.inverseDyadic input * value) :=
    ⟨CCL.ProgressiveExpRange.inverseDyadic input, value,
      rfl, rfl, rfl⟩
  have unit :=
    (CCL.ProgressiveExpRange.scaledDomain input).possible_unit
      possible
  rw [inverseDyadic_exact_mul_eq_dyadicScale value] at unit
  exact unit

/-- The actual automatic exponential of an exact rational input is
operationally its explicit dyadic normal form. -/
def automaticExactExp_toDyadic (value : Gaussian) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ProgressiveTransducer.Named.exact value))
      (exactDyadicExpCoherent
        (CCL.ProgressiveExpRange.rangeExponent
          (CCL.ProgressiveTransducer.Named.exact value))
        value (automaticExactDyadicScale_unit value)).name := by
  let input := CCL.ProgressiveTransducer.Named.exact value
  let exponent := CCL.ProgressiveExpRange.rangeExponent input
  let scaled := CCL.ProgressiveExpRange.scaledInput input
  let actualDomain := CCL.ProgressiveExpRange.scaledDomain input
  let exactUnit := automaticExactDyadicScale_unit value
  let exactScaled := CCL.ProgressiveTransducer.Named.exact
    (dyadicScale exponent value)
  let exactDomain := CCL.ProgressiveExp.UnitDisk.exact
    (dyadicScale exponent value) exactUnit
  have scaledEquivalent : NamedEquivalent scaled exactScaled := by
    simpa only [scaled, exactScaled, input,
      CCL.ProgressiveExpRange.scaledInput,
      inverseDyadic_exact_mul_eq_dyadicScale] using
        exactMul_named_equivalent
          (CCL.ProgressiveExpRange.inverseDyadic input) value
  let actualLocal : CoherentNamed :=
    { name := CCL.ProgressiveExp.named scaled actualDomain
      coherent := localExpCoherent scaled actualDomain }
  let exactLocal : CoherentNamed :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      (exactLocalExpApproximation (dyadicScale exponent value) exactUnit)
  have localEquivalent : NamedEquivalent actualLocal.name exactLocal.name :=
    localExpNamed_respects actualDomain exactDomain scaledEquivalent
  exact squareIterate_respects exponent actualLocal exactLocal localEquivalent

/-- Global exponential addition for the actual automatically range-reduced
CCL entry point on arbitrary displayed Gaussian-rational inputs.  Each of the
three calls may compute a different finite range exponent. -/
def automaticExactExp_add (x y : Gaussian) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.named
          (CCL.ProgressiveTransducer.Named.exact x))
        (CCL.ProgressiveExpRange.named
          (CCL.ProgressiveTransducer.Named.exact y)))
      (CCL.ProgressiveExpRange.named
        (CCL.ProgressiveTransducer.Named.exact (x + y))) := by
  let xInput := CCL.ProgressiveTransducer.Named.exact x
  let yInput := CCL.ProgressiveTransducer.Named.exact y
  let sumInput := CCL.ProgressiveTransducer.Named.exact (x + y)
  let xExponent := CCL.ProgressiveExpRange.rangeExponent xInput
  let yExponent := CCL.ProgressiveExpRange.rangeExponent yInput
  let sumExponent := CCL.ProgressiveExpRange.rangeExponent sumInput
  let xUnit := automaticExactDyadicScale_unit x
  let yUnit := automaticExactDyadicScale_unit y
  let sumUnit := automaticExactDyadicScale_unit (x + y)
  let xAutomatic := exp xInput
  let yAutomatic := exp yInput
  let xDyadic := exactDyadicExpCoherent xExponent x xUnit
  let yDyadic := exactDyadicExpCoherent yExponent y yUnit
  have factorsToDyadic :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          xAutomatic.name yAutomatic.name)
        (CCL.ProgressiveTransducer.Named.mul
          xDyadic.name yDyadic.name) :=
    coherentMul_respects xAutomatic xDyadic yAutomatic yDyadic
      (automaticExactExp_toDyadic x)
      (automaticExactExp_toDyadic y)
  have dyadicLaw :
      NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          xDyadic.name yDyadic.name)
        (exactDyadicExpCoherent sumExponent (x + y) sumUnit).name :=
    exactDyadicExp_add_independent xExponent yExponent sumExponent x y
      xUnit yUnit sumUnit
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    factorsToDyadic
    (CCL.OperationalEquivalence.NamedEquivalent.trans dyadicLaw
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (automaticExactExp_toDyadic (x + y))))

theorem rangeExponent_exact_zero :
    CCL.ProgressiveExpRange.rangeExponent
      (CCL.ProgressiveTransducer.Named.exact 0) = 0 := by
  decide

/-- The actual total automatic exponential sends the exact zero CCL name to
the exact one CCL name operationally. -/
def automaticExp_zero :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ProgressiveTransducer.Named.exact 0))
      (CCL.ProgressiveTransducer.Named.exact 1) := by
  let zeroUnit : normSq (0 : Gaussian) ≤ 1 := by decide
  have localToFinite : NamedEquivalent
      (exactLocalExpNamed 0 zeroUnit)
      CCL.TranscendentalLaws.expZeroApproximation.toNamed :=
    approximationEquivalent_toNamed
      (approximationEquivalentOfSamplesEq
        (exactLocalExpApproximation 0 zeroUnit)
        CCL.TranscendentalLaws.expZeroApproximation
        (by intro index; rfl))
  have finiteToOne : NamedEquivalent
      CCL.TranscendentalLaws.expZeroApproximation.toNamed
      CCL.TranscendentalLaws.oneApproximation.toNamed :=
    approximationEquivalent_toNamed
      CCL.TranscendentalLaws.exp_zero_equivalent_one
  have oneToExact : NamedEquivalent
      CCL.TranscendentalLaws.oneApproximation.toNamed
      (CCL.ProgressiveTransducer.Named.exact 1) :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (exact_toConstantNamed 1)
  have dyadicToOne : NamedEquivalent
      (exactDyadicExpCoherent
        (CCL.ProgressiveExpRange.rangeExponent
          (CCL.ProgressiveTransducer.Named.exact 0))
        0 (automaticExactDyadicScale_unit 0)).name
      (CCL.ProgressiveTransducer.Named.exact 1) := by
    simpa only [rangeExponent_exact_zero, exactDyadicExpCoherent,
        dyadicScale, CCL.ProgressiveExpRange.squareIterate] using
      CCL.OperationalEquivalence.NamedEquivalent.trans
        localToFinite
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          finiteToOne oneToExact)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (automaticExactExp_toDyadic 0) dyadicToOne

/-- The local positive-real logarithm output is coherent by its explicit
finite approximation. -/
def localLogCoherent (input : Named)
    (chart : CCL.ProgressiveLog.Chart input) :
    Coherent (CCL.ProgressiveLog.named input chart).process :=
  CCL.ProgressiveCoherence.Coherent.ofApproximation
    (CCL.ProgressiveLog.approximation input chart)

/-- The finite `log 2` stream used by dyadic range correction is coherent. -/
def logTwoCoherent :
    Coherent CCL.ProgressiveLogRange.logTwo.process :=
  localLogCoherent
    (CCL.ProgressiveTransducer.Named.exact ⟨2, 0⟩)
    (CCL.ProgressiveLog.Chart.exact 2 (by decide) le_rfl)

/-- Every signed natural multiple of the finite `log 2` stream is coherent. -/
def logCorrectionCoherent
    (direction : CCL.PositiveDyadic.Direction) (exponent : Nat) :
    Coherent
      (CCL.ProgressiveLogRange.correction direction exponent).process :=
  CCL.ProgressiveCoherence.Coherent.mul
    (CCL.ProgressiveCoherence.Coherent.exact
      (CCL.ProgressiveLogRange.correctionCoefficient
        direction exponent))
    logTwoCoherent

/-- A dyadically range-reduced positive-real logarithm, including its finite
correction term, is coherent. -/
def logRangeNamedCoherent (input : Named)
    (chart : CCL.ProgressiveLogRange.DyadicChart input) :
    Coherent
      (CCL.ProgressiveLogRange.named input chart).process :=
  CCL.ProgressiveCoherence.Coherent.add
    (localLogCoherent
      (CCL.ProgressiveLogRange.scaledInput input chart.direction
        chart.exponent) chart.localChart)
    (logCorrectionCoherent chart.direction chart.exponent)

/-- The automatically charted global positive-real logarithm output is
coherent. -/
def positiveLogNamedCoherent (input : Named)
    (positive : CCL.ProgressiveLogPositive.PositiveReal input) :
    Coherent
      (CCL.ProgressiveLogPositive.named input positive).process :=
  logRangeNamedCoherent
    (CCL.ProgressiveLogPositive.refinedInput positive)
    (CCL.ProgressiveLogPositive.automaticChart positive)

def positiveLog (input : Named)
    (positive : CCL.ProgressiveLogPositive.PositiveReal input) :
    CoherentNamed :=
  { name := CCL.ProgressiveLogPositive.named input positive
    coherent := positiveLogNamedCoherent input positive }

/-- The local complex logarithm output of a supplied disk chart is coherent. -/
def localComplexLogCoherent (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input) :
    Coherent
      (CCL.ProgressiveComplexLog.named input disk).process :=
  CCL.ProgressiveCoherence.Coherent.ofApproximation
    (CCL.ProgressiveComplexLog.approximation input disk)

def dynamicLocalExpLogErrorScale : Coordinate :=
  2 * (10 + 16 * CCL.ProgressiveComplexLog.errorScale)

theorem dynamicLocalExpLogErrorScale_nonneg :
    0 ≤ dynamicLocalExpLogErrorScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        CCL.ProgressiveComplexLog.errorScale_nonneg))

/-- Diagonal finite program for exponentiating a progressive local complex
logarithm: logarithm depth `n`, exponential depth `2n+1`. -/
def dynamicLocalExpLogApproximation (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input) :
    Approximation where
  sample depth := CCL.FiniteExp.sample
    (CCL.ProgressiveComplexLog.domainSample input disk depth)
    (2 * depth + 1)
  radiusSq := CCL.FiniteGeometric.quarterRadius
    dynamicLocalExpLogErrorScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      dynamicLocalExpLogErrorScale_nonneg
  later_close := by
    intro earlier later order
    let earlierInput :=
      CCL.ProgressiveComplexLog.domainSample input disk earlier
    let laterInput :=
      CCL.ProgressiveComplexLog.domainSample input disk later
    have earlierUnit : normSq earlierInput ≤ 1 :=
      CCL.FiniteComplexLog.sample_bounded_one
        (CCL.ProgressiveComplexLog.inputSample_bound disk earlier)
        earlier
    have laterUnit : normSq laterInput ≤ 1 :=
      CCL.FiniteComplexLog.sample_bounded_one
        (CCL.ProgressiveComplexLog.inputSample_bound disk later)
        later
    have depthOrder : 2 * earlier + 1 ≤ 2 * later + 1 := by omega
    have truncationRaw := CCL.FiniteExp.sample_later_close
      laterInput laterUnit depthOrder
    have truncation :
        normSq
            (CCL.FiniteExp.sample laterInput (2 * later + 1) -
              CCL.FiniteExp.sample laterInput
                (2 * earlier + 1)) ≤
          10 * (1 / 4 : Coordinate) ^ earlier := by
      exact truncationRaw.trans (by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (CCL.FinitePolynomial.quarterPower_antitone
            (show earlier ≤ 2 * earlier + 1 by omega)) (by decide))
    have inputMovement :=
      CCL.ProgressiveComplexLog.domainSample_later_close disk order
    have inputEffectRaw := CCL.FiniteExp.sample_input_close
      laterInput earlierInput laterUnit earlierUnit (2 * earlier + 1)
    have inputEffect :
        normSq
            (CCL.FiniteExp.sample laterInput (2 * earlier + 1) -
              CCL.FiniteExp.sample earlierInput
                (2 * earlier + 1)) ≤
          16 * CCL.ProgressiveComplexLog.errorScale *
            (1 / 4 : Coordinate) ^ earlier := by
      calc
        normSq
            (CCL.FiniteExp.sample laterInput (2 * earlier + 1) -
              CCL.FiniteExp.sample earlierInput
                (2 * earlier + 1)) ≤
          16 * normSq (laterInput - earlierInput) := inputEffectRaw
        _ ≤ 16 * CCL.FiniteGeometric.quarterRadius
            CCL.ProgressiveComplexLog.errorScale earlier :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            inputMovement (by decide)
        _ = 16 * CCL.ProgressiveComplexLog.errorScale *
            (1 / 4 : Coordinate) ^ earlier := by
          rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
          ring1
    change normSq
        (CCL.FiniteExp.sample laterInput (2 * later + 1) -
          CCL.FiniteExp.sample earlierInput (2 * earlier + 1)) ≤
      CCL.FiniteGeometric.quarterRadius
        dynamicLocalExpLogErrorScale earlier
    calc
      normSq
          (CCL.FiniteExp.sample laterInput (2 * later + 1) -
            CCL.FiniteExp.sample earlierInput
              (2 * earlier + 1)) ≤
        2 *
          (normSq
              (CCL.FiniteExp.sample laterInput (2 * later + 1) -
                CCL.FiniteExp.sample laterInput
                  (2 * earlier + 1)) +
            normSq
              (CCL.FiniteExp.sample laterInput
                  (2 * earlier + 1) -
                CCL.FiniteExp.sample earlierInput
                  (2 * earlier + 1))) :=
        normSq_sub_le_via _ _ _
      _ ≤ 2 *
          (10 * (1 / 4 : Coordinate) ^ earlier +
            (16 * CCL.ProgressiveComplexLog.errorScale) *
              (1 / 4 : Coordinate) ^ earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add truncation inputEffect) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          dynamicLocalExpLogErrorScale earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        unfold dynamicLocalExpLogErrorScale
        ring1
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      dynamicLocalExpLogErrorScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      dynamicLocalExpLogErrorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      dynamicLocalExpLogErrorScale dynamicLocalExpLogErrorScale_nonneg
  centerBound := 10
  centerBound_nonneg := by decide
  sample_bounded := by
    intro depth
    exact CCL.FiniteExp.sample_bounded _
      (CCL.FiniteComplexLog.sample_bounded_one
        (CCL.ProgressiveComplexLog.inputSample_bound disk depth)
        depth) (2 * depth + 1)

@[simp] theorem dynamicLocalExpLogApproximation_sample
    (input : Named) (disk : CCL.ProgressiveComplexLog.Disk input)
    (depth : Nat) :
    (dynamicLocalExpLogApproximation input disk).sample depth =
      CCL.FinitePolynomial.localExpLogSample
        (CCL.ProgressiveComplexLog.inputSample input depth)
        depth :=
  rfl

def dynamicLocalExpLogChartSample (input : Named) (depth : Nat) : Gaussian :=
  let reduced :=
    CCL.ProgressiveComplexLog.inputSample input depth
  (1 + reduced) / (1 - reduced)

theorem dynamicLocalExpLog_chart_error (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input)
    (depth : Nat) :
    normSq
        ((dynamicLocalExpLogApproximation input disk).sample depth -
          dynamicLocalExpLogChartSample input depth) ≤
      CCL.FinitePolynomial.expLogErrorScale *
        (1 / 4 : Coordinate) ^ depth := by
  exact CCL.FinitePolynomial.localExpLogSample_chart_error
    (CCL.ProgressiveComplexLog.inputSample_bound disk depth)
    depth

def dynamicLocalExpLogChartApproximationScale : Coordinate :=
  2 * (3 * CCL.FinitePolynomial.expLogErrorScale +
    2 * dynamicLocalExpLogErrorScale)

theorem dynamicLocalExpLogChartApproximationScale_nonneg :
    0 ≤ dynamicLocalExpLogChartApproximationScale := by
  unfold dynamicLocalExpLogChartApproximationScale
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        CCL.FinitePolynomial.expLogErrorScale_nonnegative)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        dynamicLocalExpLogErrorScale_nonneg))

def dynamicLocalExpLogChartCenterBound : Coordinate :=
  2 * (CCL.FinitePolynomial.expLogErrorScale + 5 * 10)

theorem dynamicLocalExpLogChartCenterBound_nonneg :
    0 ≤ dynamicLocalExpLogChartCenterBound := by
  unfold dynamicLocalExpLogChartCenterBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      CCL.FinitePolynomial.expLogErrorScale_nonnegative
      (by decide))

/-- The exact rational Möbius reconstruction of each finite reduced reading.
Its Cauchy certificate is obtained solely from the explicit finite exp-log
error and the already proved dynamic-program movement bound. -/
def dynamicLocalExpLogChartApproximation (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input) :
    Approximation where
  sample := dynamicLocalExpLogChartSample input
  radiusSq := CCL.FiniteGeometric.quarterRadius
    dynamicLocalExpLogChartApproximationScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      dynamicLocalExpLogChartApproximationScale_nonneg
  later_close := by
    intro earlier later order
    let dynamic := dynamicLocalExpLogApproximation input disk
    have laterError := dynamicLocalExpLog_chart_error input disk later
    have earlierError := dynamicLocalExpLog_chart_error input disk earlier
    have laterScaled :
        CCL.FinitePolynomial.expLogErrorScale *
            (1 / 4 : Coordinate) ^ later ≤
          CCL.FinitePolynomial.expLogErrorScale *
            (1 / 4 : Coordinate) ^ earlier :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (CCL.FinitePolynomial.quarterPower_antitone order)
        CCL.FinitePolynomial.expLogErrorScale_nonnegative
    have laterErrorScaled := laterError.trans laterScaled
    have laterErrorReverse :
        normSq
            (dynamicLocalExpLogChartSample input later -
              dynamic.sample later) ≤
          CCL.FinitePolynomial.expLogErrorScale *
            (1 / 4 : Coordinate) ^ earlier := by
      have identity :
          dynamicLocalExpLogChartSample input later -
              dynamic.sample later =
            -(dynamic.sample later -
              dynamicLocalExpLogChartSample input later) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
      rw [identity, normSq_neg]
      exact laterErrorScaled
    have dynamicMovement := dynamic.later_close order
    have dynamicMovementScaled :
        normSq (dynamic.sample later - dynamic.sample earlier) ≤
          dynamicLocalExpLogErrorScale *
            (1 / 4 : Coordinate) ^ earlier := by
      change normSq (dynamic.sample later - dynamic.sample earlier) ≤
        CCL.FiniteGeometric.quarterRadius
          dynamicLocalExpLogErrorScale earlier at dynamicMovement
      simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        using dynamicMovement
    change normSq
        (dynamicLocalExpLogChartSample input later -
          dynamicLocalExpLogChartSample input earlier) ≤
      CCL.FiniteGeometric.quarterRadius
        dynamicLocalExpLogChartApproximationScale earlier
    calc
      normSq
          (dynamicLocalExpLogChartSample input later -
            dynamicLocalExpLogChartSample input earlier) ≤
        2 *
          (normSq
              (dynamicLocalExpLogChartSample input later -
                dynamic.sample later) +
            normSq
              (dynamic.sample later -
                dynamicLocalExpLogChartSample input earlier)) :=
        normSq_sub_le_via _ _ _
      _ ≤ 2 *
          (CCL.FinitePolynomial.expLogErrorScale *
              (1 / 4 : Coordinate) ^ earlier +
            2 *
              (dynamicLocalExpLogErrorScale *
                  (1 / 4 : Coordinate) ^ earlier +
                CCL.FinitePolynomial.expLogErrorScale *
                  (1 / 4 : Coordinate) ^ earlier)) := by
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        apply add_le_add laterErrorReverse
        calc
          normSq
              (dynamic.sample later -
                dynamicLocalExpLogChartSample input earlier) ≤
            2 *
              (normSq (dynamic.sample later - dynamic.sample earlier) +
                normSq
                  (dynamic.sample earlier -
                    dynamicLocalExpLogChartSample input earlier)) :=
              normSq_sub_le_via _ _ _
          _ ≤ 2 *
              (dynamicLocalExpLogErrorScale *
                  (1 / 4 : Coordinate) ^ earlier +
                CCL.FinitePolynomial.expLogErrorScale *
                  (1 / 4 : Coordinate) ^ earlier) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add dynamicMovementScaled earlierError) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          dynamicLocalExpLogChartApproximationScale earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        unfold dynamicLocalExpLogChartApproximationScale
        ring1
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      dynamicLocalExpLogChartApproximationScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      dynamicLocalExpLogChartApproximationScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      dynamicLocalExpLogChartApproximationScale
      dynamicLocalExpLogChartApproximationScale_nonneg
  centerBound := dynamicLocalExpLogChartCenterBound
  centerBound_nonneg := dynamicLocalExpLogChartCenterBound_nonneg
  sample_bounded := by
    intro depth
    let dynamic := dynamicLocalExpLogApproximation input disk
    have error := dynamicLocalExpLog_chart_error input disk depth
    have errorLe :
        CCL.FinitePolynomial.expLogErrorScale *
            (1 / 4 : Coordinate) ^ depth ≤
          CCL.FinitePolynomial.expLogErrorScale := by
      simpa only [pow_zero, RFAP.ConstructiveFraction.mul_one_direct]
        using RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (CCL.FinitePolynomial.quarterPower_antitone
            (show 0 ≤ depth by omega))
          CCL.FinitePolynomial.expLogErrorScale_nonnegative
    have reverseError :
        normSq
            (dynamicLocalExpLogChartSample input depth -
              dynamic.sample depth) ≤
          CCL.FinitePolynomial.expLogErrorScale := by
      have identity : dynamicLocalExpLogChartSample input depth -
            dynamic.sample depth =
          -(dynamic.sample depth -
            dynamicLocalExpLogChartSample input depth) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
      rw [identity, normSq_neg]
      exact error.trans errorLe
    have dynamicBound : normSq (dynamic.sample depth) ≤ 5 * 10 :=
      CCL.FinitePolynomial.localExpLogSample_bounded
        (CCL.ProgressiveComplexLog.inputSample_bound disk depth)
        depth
    have identity : dynamicLocalExpLogChartSample input depth =
        (dynamicLocalExpLogChartSample input depth - dynamic.sample depth) +
          dynamic.sample depth := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im] <;> ring1
    rw [identity]
    exact (normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add reverseError dynamicBound) (by decide))

/-- Exact finite Möbius reconstruction respects operational equality of two
progressive reduced inputs. -/
def dynamicLocalExpLogChartApproximation_respects {left right : Named}
    (leftDisk : CCL.ProgressiveComplexLog.Disk left)
    (rightDisk : CCL.ProgressiveComplexLog.Disk right)
    (equivalent : NamedEquivalent left right) :
    Equivalent
      (dynamicLocalExpLogChartApproximation left leftDisk)
      (dynamicLocalExpLogChartApproximation right rightDisk) where
  compare := by
    intro leftStart rightStart target positive
    let coefficient : Coordinate := (9 * 9) / 4
    have coefficientPositive : 0 < coefficient := by
      dsimp only [coefficient]
      decide
    let inputTarget := target / coefficient
    have inputPositive : 0 < inputTarget :=
      RFAP.ConstructiveFraction.div_pos_direct positive coefficientPositive
    let comparison := equivalent.compare leftStart rightStart
      inputTarget inputPositive
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have inputClose := comparison.close leftOrder rightOrder
          have chartClose :=
            CCL.FinitePolynomial.localChart_input_close
              (CCL.ProgressiveComplexLog.inputSample_bound
                leftDisk leftLater)
              (CCL.ProgressiveComplexLog.inputSample_bound
                rightDisk rightLater)
          calc
            normSq
                ((dynamicLocalExpLogChartApproximation left leftDisk).sample
                    leftLater -
                  (dynamicLocalExpLogChartApproximation right rightDisk).sample
                    rightLater) ≤
              coefficient * normSq
                (CCL.ProgressiveComplexLog.inputSample
                    left leftLater -
                  CCL.ProgressiveComplexLog.inputSample
                    right rightLater) := chartClose
            _ < coefficient * inputTarget :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                coefficientPositive inputClose
            _ = target := by
              dsimp only [inputTarget]
              rw [RFAP.ConstructiveFraction.mul_comm]
              exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
                target coefficient coefficientPositive.ne' }

def dynamicLocalExpLogChartNamed_respects {left right : Named}
    (leftDisk : CCL.ProgressiveComplexLog.Disk left)
    (rightDisk : CCL.ProgressiveComplexLog.Disk right)
    (equivalent : NamedEquivalent left right) :
    NamedEquivalent
      (dynamicLocalExpLogChartApproximation left leftDisk).toNamed
      (dynamicLocalExpLogChartApproximation right rightDisk).toNamed :=
  approximationEquivalent_toNamed
    (dynamicLocalExpLogChartApproximation_respects
      leftDisk rightDisk equivalent)

def dynamicLocalExpLogChartEquivalentMasterScale : Coordinate :=
  dynamicLocalExpLogErrorScale +
    dynamicLocalExpLogChartApproximationScale +
      CCL.FinitePolynomial.expLogErrorScale

theorem dynamicLocalExpLogChartEquivalentMasterScale_nonneg :
    0 ≤ dynamicLocalExpLogChartEquivalentMasterScale :=
  add_nonneg
    (add_nonneg dynamicLocalExpLogErrorScale_nonneg
      dynamicLocalExpLogChartApproximationScale_nonneg)
    CCL.FinitePolynomial.expLogErrorScale_nonnegative

private theorem dynamicLocalExpLogScale_le_chartEquivalentMaster :
    dynamicLocalExpLogErrorScale ≤
      dynamicLocalExpLogChartEquivalentMasterScale := by
  unfold dynamicLocalExpLogChartEquivalentMasterScale
  calc
    dynamicLocalExpLogErrorScale ≤
        dynamicLocalExpLogErrorScale +
          dynamicLocalExpLogChartApproximationScale :=
      coordinate_le_add_of_nonneg_right _ _
        dynamicLocalExpLogChartApproximationScale_nonneg
    _ ≤ dynamicLocalExpLogErrorScale +
          dynamicLocalExpLogChartApproximationScale +
            CCL.FinitePolynomial.expLogErrorScale :=
      coordinate_le_add_of_nonneg_right _ _
        CCL.FinitePolynomial.expLogErrorScale_nonnegative

private theorem dynamicLocalExpLogChartScale_le_chartEquivalentMaster :
    dynamicLocalExpLogChartApproximationScale ≤
      dynamicLocalExpLogChartEquivalentMasterScale := by
  unfold dynamicLocalExpLogChartEquivalentMasterScale
  calc
    dynamicLocalExpLogChartApproximationScale ≤
        dynamicLocalExpLogErrorScale +
          dynamicLocalExpLogChartApproximationScale :=
      coordinate_le_add_of_nonneg_left _ _
        dynamicLocalExpLogErrorScale_nonneg
    _ ≤ dynamicLocalExpLogErrorScale +
          dynamicLocalExpLogChartApproximationScale +
            CCL.FinitePolynomial.expLogErrorScale :=
      coordinate_le_add_of_nonneg_right _ _
        CCL.FinitePolynomial.expLogErrorScale_nonnegative

private theorem finiteExpLogScale_le_chartEquivalentMaster :
    CCL.FinitePolynomial.expLogErrorScale ≤
      dynamicLocalExpLogChartEquivalentMasterScale := by
  unfold dynamicLocalExpLogChartEquivalentMasterScale
  exact coordinate_le_add_of_nonneg_left _ _
    (add_nonneg dynamicLocalExpLogErrorScale_nonneg
      dynamicLocalExpLogChartApproximationScale_nonneg)

/-- The dynamic finite exp-log computation is operationally equal to exact
Möbius reconstruction of the same finite reduced readings. -/
def dynamicLocalExpLog_chart_equivalent (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input) :
    Equivalent
      (dynamicLocalExpLogApproximation input disk)
      (dynamicLocalExpLogChartApproximation input disk) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 16
    have smallPositive : 0 < smallTarget :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    let start := max leftStart rightStart
    let index := CCL.FiniteGeometric.firstQuarterBelow
      dynamicLocalExpLogChartEquivalentMasterScale start smallTarget
    have indexGe : start ≤ index :=
      CCL.FiniteGeometric.firstQuarterBelow_ge
        dynamicLocalExpLogChartEquivalentMasterScale start smallTarget
    have masterSmall :
        CCL.FiniteGeometric.quarterRadius
            dynamicLocalExpLogChartEquivalentMasterScale index < smallTarget :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate
        dynamicLocalExpLogChartEquivalentMasterScale
          dynamicLocalExpLogChartEquivalentMasterScale_nonneg
            start smallTarget smallPositive
    exact
      { leftIndex := index
        rightIndex := index
        left_ge := (Nat.le_max_left _ _).trans indexGe
        right_ge := (Nat.le_max_right _ _).trans indexGe
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftTail :=
            (dynamicLocalExpLogApproximation input disk).later_close leftOrder
          have leftTailSmall := leftTail.trans_lt
            ((quarterRadius_scale_le
                dynamicLocalExpLogScale_le_chartEquivalentMaster index).trans_lt
              masterSmall)
          have rightTail :=
            (dynamicLocalExpLogChartApproximation input disk).later_close
              rightOrder
          have rightTailSmall := rightTail.trans_lt
            ((quarterRadius_scale_le
                dynamicLocalExpLogChartScale_le_chartEquivalentMaster
                index).trans_lt masterSmall)
          have rightTailReverse :
              normSq
                  ((dynamicLocalExpLogChartApproximation input disk).sample
                      index -
                    (dynamicLocalExpLogChartApproximation input disk).sample
                      rightLater) < smallTarget := by
            have identity :
                (dynamicLocalExpLogChartApproximation input disk).sample
                      index -
                    (dynamicLocalExpLogChartApproximation input disk).sample
                      rightLater =
                  -((dynamicLocalExpLogChartApproximation input disk).sample
                      rightLater -
                    (dynamicLocalExpLogChartApproximation input disk).sample
                      index) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [identity, normSq_neg]
            exact rightTailSmall
          have direct := dynamicLocalExpLog_chart_error input disk index
          have directSmall :
              normSq
                  ((dynamicLocalExpLogApproximation input disk).sample index -
                    (dynamicLocalExpLogChartApproximation input disk).sample
                      index) < smallTarget := by
            change normSq
                ((dynamicLocalExpLogApproximation input disk).sample index -
                  dynamicLocalExpLogChartSample input index) < smallTarget
            have directRadius :
                CCL.FinitePolynomial.expLogErrorScale *
                    (1 / 4 : Coordinate) ^ index ≤
                  CCL.FiniteGeometric.quarterRadius
                    dynamicLocalExpLogChartEquivalentMasterScale index := by
              rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
              exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                finiteExpLogScale_le_chartEquivalentMaster
                (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
            exact direct.trans_lt (directRadius.trans_lt masterSmall)
          have middle := (normSq_sub_le_via _ _ _).trans_lt
            (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              (by decide)
              (RFAP.ConstructiveFraction.add_lt_add_direct
                directSmall rightTailReverse))
          calc
            normSq
                ((dynamicLocalExpLogApproximation input disk).sample
                    leftLater -
                  (dynamicLocalExpLogChartApproximation input disk).sample
                    rightLater) ≤
              2 *
                (normSq
                    ((dynamicLocalExpLogApproximation input disk).sample
                        leftLater -
                      (dynamicLocalExpLogApproximation input disk).sample
                        index) +
                  normSq
                    ((dynamicLocalExpLogApproximation input disk).sample
                        index -
                      (dynamicLocalExpLogChartApproximation input disk).sample
                        rightLater)) :=
              normSq_sub_le_via _ _ _
            _ < 2 *
                (smallTarget + 2 * (smallTarget + smallTarget)) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  leftTailSmall middle)
            _ = 10 * smallTarget := by ring1
            _ < target := by
              dsimp only [smallTarget]
              exact ten_sixteenths_lt positive }

def dynamicLocalExpLog_chart_named_equivalent (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input) :
    NamedEquivalent
      (dynamicLocalExpLogApproximation input disk).toNamed
      (dynamicLocalExpLogChartApproximation input disk).toNamed :=
  approximationEquivalent_toNamed
    (dynamicLocalExpLog_chart_equivalent input disk)

def scaledDynamicLocalExpLogChartErrorScale (factor : Gaussian) : Coordinate :=
  dynamicLocalExpLogChartApproximationScale * normSq factor

theorem scaledDynamicLocalExpLogChartErrorScale_nonneg (factor : Gaussian) :
    0 ≤ scaledDynamicLocalExpLogChartErrorScale factor :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    dynamicLocalExpLogChartApproximationScale_nonneg (normSq_nonneg factor)

/-- Pointwise multiplication of the reconstructed local exp-log chart by one
displayed rational branch factor. -/
def scaledDynamicLocalExpLogChartApproximation (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input)
    (factor : Gaussian) : Approximation where
  sample depth := dynamicLocalExpLogChartSample input depth * factor
  radiusSq := CCL.FiniteGeometric.quarterRadius
    (scaledDynamicLocalExpLogChartErrorScale factor)
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      (scaledDynamicLocalExpLogChartErrorScale_nonneg factor)
  later_close := by
    intro earlier later order
    have movement :=
      (dynamicLocalExpLogChartApproximation input disk).later_close order
    have movementScaled :
        normSq
            (dynamicLocalExpLogChartSample input later -
              dynamicLocalExpLogChartSample input earlier) ≤
          dynamicLocalExpLogChartApproximationScale *
            (1 / 4 : Coordinate) ^ earlier := by
      change normSq
          (dynamicLocalExpLogChartSample input later -
            dynamicLocalExpLogChartSample input earlier) ≤
        CCL.FiniteGeometric.quarterRadius
          dynamicLocalExpLogChartApproximationScale earlier at movement
      simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        using movement
    have identity :
        dynamicLocalExpLogChartSample input later * factor -
            dynamicLocalExpLogChartSample input earlier * factor =
          (dynamicLocalExpLogChartSample input later -
            dynamicLocalExpLogChartSample input earlier) * factor := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    change normSq
        (dynamicLocalExpLogChartSample input later * factor -
          dynamicLocalExpLogChartSample input earlier * factor) ≤
      CCL.FiniteGeometric.quarterRadius
        (scaledDynamicLocalExpLogChartErrorScale factor) earlier
    rw [identity, normSq_mul,
      CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
    unfold scaledDynamicLocalExpLogChartErrorScale
    calc
      normSq
          (dynamicLocalExpLogChartSample input later -
            dynamicLocalExpLogChartSample input earlier) * normSq factor ≤
        (dynamicLocalExpLogChartApproximationScale *
            (1 / 4 : Coordinate) ^ earlier) * normSq factor :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            movementScaled (normSq_nonneg factor)
      _ = dynamicLocalExpLogChartApproximationScale * normSq factor *
          (1 / 4 : Coordinate) ^ earlier := by ring1
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      (scaledDynamicLocalExpLogChartErrorScale factor) current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      (scaledDynamicLocalExpLogChartErrorScale factor) current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      (scaledDynamicLocalExpLogChartErrorScale factor)
      (scaledDynamicLocalExpLogChartErrorScale_nonneg factor)
  centerBound := dynamicLocalExpLogChartCenterBound * normSq factor
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      dynamicLocalExpLogChartCenterBound_nonneg (normSq_nonneg factor)
  sample_bounded := by
    intro depth
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      ((dynamicLocalExpLogChartApproximation input disk).sample_bounded depth)
      (normSq_nonneg factor)

@[simp] theorem scaledDynamicLocalExpLogChartApproximation_sample
    (input : Named) (disk : CCL.ProgressiveComplexLog.Disk input)
    (factor : Gaussian) (depth : Nat) :
    (scaledDynamicLocalExpLogChartApproximation input disk factor).sample
        depth =
      (dynamicLocalExpLogChartApproximation input disk).sample depth *
        (CCL.TranscendentalLaws.constantApproximation factor).sample
          depth :=
  rfl

/-- Rational branch scaling preserves the finite Möbius reconstruction
congruence, with a direct zero-factor branch and an explicit norm budget
otherwise. -/
def scaledDynamicLocalExpLogChartApproximation_respects {left right : Named}
    (leftDisk : CCL.ProgressiveComplexLog.Disk left)
    (rightDisk : CCL.ProgressiveComplexLog.Disk right)
    (factor : Gaussian) (equivalent : NamedEquivalent left right) :
    Equivalent
      (scaledDynamicLocalExpLogChartApproximation left leftDisk factor)
      (scaledDynamicLocalExpLogChartApproximation right rightDisk factor) := by
  by_cases factorZero : factor = 0
  · subst factor
    exact approximationEquivalentOfSamplesEq _ _ (by
      intro index
      change dynamicLocalExpLogChartSample left index * 0 =
        dynamicLocalExpLogChartSample right index * 0
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mul_re, mul_im, zero_re, zero_im] <;> ring1)
  · let sourceEquivalent :=
      dynamicLocalExpLogChartApproximation_respects
        leftDisk rightDisk equivalent
    exact
      { compare := by
          intro leftStart rightStart target positive
          let factorNorm := normSq factor
          have factorPositive : 0 < factorNorm := normSq_pos factorZero
          let sourceTarget := target / factorNorm
          have sourcePositive : 0 < sourceTarget :=
            RFAP.ConstructiveFraction.div_pos_direct positive factorPositive
          let comparison := sourceEquivalent.compare leftStart rightStart
            sourceTarget sourcePositive
          exact
            { leftIndex := comparison.leftIndex
              rightIndex := comparison.rightIndex
              left_ge := comparison.left_ge
              right_ge := comparison.right_ge
              close := by
                intro leftLater rightLater leftOrder rightOrder
                have sourceClose := comparison.close leftOrder rightOrder
                have identity :
                    dynamicLocalExpLogChartSample left leftLater * factor -
                        dynamicLocalExpLogChartSample right rightLater * factor =
                      (dynamicLocalExpLogChartSample left leftLater -
                        dynamicLocalExpLogChartSample right rightLater) *
                          factor := by
                  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                    simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
                change normSq
                    (dynamicLocalExpLogChartSample left leftLater * factor -
                      dynamicLocalExpLogChartSample right rightLater * factor) <
                    target
                rw [identity, normSq_mul]
                calc
                  normSq
                        (dynamicLocalExpLogChartSample left leftLater -
                          dynamicLocalExpLogChartSample right rightLater) *
                      factorNorm < sourceTarget * factorNorm :=
                    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
                      sourceClose factorPositive
                  _ = target :=
                    RFAP.ConstructiveFraction.div_mul_cancel_of_ne
                      target factorNorm factorPositive.ne' } }

def scaledDynamicLocalExpLogChartNamed_respects {left right : Named}
    (leftDisk : CCL.ProgressiveComplexLog.Disk left)
    (rightDisk : CCL.ProgressiveComplexLog.Disk right)
    (factor : Gaussian) (equivalent : NamedEquivalent left right) :
    NamedEquivalent
      (scaledDynamicLocalExpLogChartApproximation left leftDisk factor).toNamed
      (scaledDynamicLocalExpLogChartApproximation right rightDisk factor).toNamed :=
  approximationEquivalent_toNamed
    (scaledDynamicLocalExpLogChartApproximation_respects
      leftDisk rightDisk factor equivalent)

/-- The sharper finite Horner estimate places every explicitly possible
local complex-log reading in the local exponential unit disk. -/
theorem localComplexLogUnitDisk (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input) :
    CCL.ProgressiveExp.UnitDisk
      (CCL.ProgressiveComplexLog.named input disk) where
  possible_unit := by
    intro value possible
    change (CCL.ProgressiveComplexLog.approximation
      input disk).Possible 0 value at possible
    rcases possible with ⟨later, _order, rfl⟩
    exact CCL.FiniteComplexLog.sample_bounded_one
      (CCL.ProgressiveComplexLog.inputSample_bound disk later)
      later

def dynamicLocalExpLogReindexDirectScale : Coordinate := 2 * (10 + 16)

theorem dynamicLocalExpLogReindexDirectScale_nonneg :
    0 ≤ dynamicLocalExpLogReindexDirectScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (by decide))

def dynamicLocalExpLogReindexMasterScale : Coordinate :=
  dynamicLocalExpLogErrorScale +
    CCL.ProgressiveExp.errorScale +
      dynamicLocalExpLogReindexDirectScale

theorem dynamicLocalExpLogReindexMasterScale_nonneg :
    0 ≤ dynamicLocalExpLogReindexMasterScale :=
  add_nonneg
    (add_nonneg dynamicLocalExpLogErrorScale_nonneg
      CCL.ProgressiveExp.errorScale_nonneg)
    dynamicLocalExpLogReindexDirectScale_nonneg

private theorem dynamicLocalExpLogScale_le_reindexMaster :
    dynamicLocalExpLogErrorScale ≤
      dynamicLocalExpLogReindexMasterScale := by
  unfold dynamicLocalExpLogReindexMasterScale
  calc
    dynamicLocalExpLogErrorScale ≤
        dynamicLocalExpLogErrorScale +
          CCL.ProgressiveExp.errorScale :=
      coordinate_le_add_of_nonneg_right _ _
        CCL.ProgressiveExp.errorScale_nonneg
    _ ≤ dynamicLocalExpLogErrorScale +
          CCL.ProgressiveExp.errorScale +
            dynamicLocalExpLogReindexDirectScale :=
      coordinate_le_add_of_nonneg_right _ _
        dynamicLocalExpLogReindexDirectScale_nonneg

private theorem progressiveExpScale_le_dynamicLocalExpLogReindexMaster :
    CCL.ProgressiveExp.errorScale ≤
      dynamicLocalExpLogReindexMasterScale := by
  unfold dynamicLocalExpLogReindexMasterScale
  calc
    CCL.ProgressiveExp.errorScale ≤
        dynamicLocalExpLogErrorScale +
          CCL.ProgressiveExp.errorScale :=
      coordinate_le_add_of_nonneg_left _ _
        dynamicLocalExpLogErrorScale_nonneg
    _ ≤ dynamicLocalExpLogErrorScale +
          CCL.ProgressiveExp.errorScale +
            dynamicLocalExpLogReindexDirectScale :=
      coordinate_le_add_of_nonneg_right _ _
        dynamicLocalExpLogReindexDirectScale_nonneg

private theorem dynamicLocalExpLogReindexDirectScale_le_master :
    dynamicLocalExpLogReindexDirectScale ≤
      dynamicLocalExpLogReindexMasterScale := by
  unfold dynamicLocalExpLogReindexMasterScale
  exact coordinate_le_add_of_nonneg_left _ _
    (add_nonneg dynamicLocalExpLogErrorScale_nonneg
      CCL.ProgressiveExp.errorScale_nonneg)

/-- Finite resampling bridge between the diagonal `exp_(2n+1)(log_n(z_n))`
program and the productive local exponential reading the progressive local
logarithm at its own requested source indices. -/
def dynamicLocalExpLogReindexEquivalent (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input) :
    Equivalent
      (dynamicLocalExpLogApproximation input disk)
      (CCL.ProgressiveExp.approximation
        (CCL.ProgressiveComplexLog.named input disk)
        (localComplexLogUnitDisk input disk)) := by
  let source :=
    CCL.ProgressiveComplexLog.approximation input disk
  let wrapperDomain := localComplexLogUnitDisk input disk
  let wrapperExp := CCL.ProgressiveExp.approximation
    source.toNamed wrapperDomain
  exact
    { compare := by
        intro leftStart rightStart target positive
        let smallTarget := target / 16
        have smallPositive : 0 < smallTarget :=
          RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
        let start := max leftStart rightStart
        let rightIndex := CCL.FiniteGeometric.firstQuarterBelow
          dynamicLocalExpLogReindexMasterScale start smallTarget
        have startLeRight : start ≤ rightIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            dynamicLocalExpLogReindexMasterScale start smallTarget
        have masterSmall :
            CCL.FiniteGeometric.quarterRadius
                dynamicLocalExpLogReindexMasterScale rightIndex < smallTarget :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            dynamicLocalExpLogReindexMasterScale
              dynamicLocalExpLogReindexMasterScale_nonneg start smallTarget
                smallPositive
        let sourceIndex :=
          CCL.OperationalEquivalence.emittedSampleIndex
            source rightIndex
        let leftIndex := max rightIndex sourceIndex
        have rightLeLeft : rightIndex ≤ leftIndex := Nat.le_max_left _ _
        have sourceLeLeft : sourceIndex ≤ leftIndex := Nat.le_max_right _ _
        have sourceRadiusSmall :
            source.radiusSq sourceIndex <
              CCL.ProgressiveSampling.refinementTarget rightIndex :=
          CCL.ProgressiveSampling.stateAt_accurate
            source.toProcess (show source.toProcess.State from (0 : Nat))
              rightIndex
        have sourceMovement := source.later_close sourceLeLeft
        have inputMovement :
            normSq (source.sample leftIndex - source.sample sourceIndex) <
              CCL.ProgressiveSampling.refinementTarget rightIndex :=
          sourceMovement.trans_lt sourceRadiusSmall
        have leftInputUnit : normSq (source.sample leftIndex) ≤ 1 := by
          exact CCL.FiniteComplexLog.sample_bounded_one
            (CCL.ProgressiveComplexLog.inputSample_bound
              disk leftIndex) leftIndex
        have rightInputUnit : normSq (source.sample sourceIndex) ≤ 1 := by
          exact CCL.FiniteComplexLog.sample_bounded_one
            (CCL.ProgressiveComplexLog.inputSample_bound
              disk sourceIndex) sourceIndex
        have depthOrder : rightIndex ≤ 2 * leftIndex + 1 := by omega
        have truncation := CCL.FiniteExp.sample_later_close
          (source.sample leftIndex) leftInputUnit depthOrder
        have inputEffect := CCL.FiniteExp.sample_input_close
          (source.sample leftIndex) (source.sample sourceIndex)
            leftInputUnit rightInputUnit rightIndex
        have inputStrict :
            normSq
                (CCL.FiniteExp.sample
                    (source.sample leftIndex) rightIndex -
                  CCL.FiniteExp.sample
                    (source.sample sourceIndex) rightIndex) <
              16 * CCL.ProgressiveSampling.refinementTarget
                rightIndex :=
          inputEffect.trans_lt
            (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              (by decide) inputMovement)
        have direct :
            normSq
                (CCL.FiniteExp.sample
                    (source.sample leftIndex) (2 * leftIndex + 1) -
                  CCL.FiniteExp.sample
                    (source.sample sourceIndex) rightIndex) <
              CCL.FiniteGeometric.quarterRadius
                dynamicLocalExpLogReindexDirectScale rightIndex := by
          calc
            normSq
                (CCL.FiniteExp.sample
                    (source.sample leftIndex) (2 * leftIndex + 1) -
                  CCL.FiniteExp.sample
                    (source.sample sourceIndex) rightIndex) ≤
              2 *
                (normSq
                    (CCL.FiniteExp.sample
                        (source.sample leftIndex) (2 * leftIndex + 1) -
                      CCL.FiniteExp.sample
                        (source.sample leftIndex) rightIndex) +
                  normSq
                    (CCL.FiniteExp.sample
                        (source.sample leftIndex) rightIndex -
                      CCL.FiniteExp.sample
                        (source.sample sourceIndex) rightIndex)) :=
              normSq_sub_le_via _ _ _
            _ < 2 *
                (CCL.FiniteGeometric.quarterRadius 10 rightIndex +
                  16 * CCL.ProgressiveSampling.refinementTarget
                    rightIndex) :=
              twice_add_lt_twice_add_of_le_of_lt truncation inputStrict
            _ = CCL.FiniteGeometric.quarterRadius
                dynamicLocalExpLogReindexDirectScale rightIndex := by
              unfold dynamicLocalExpLogReindexDirectScale
              rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
                CCL.ProgressiveSampling.refinementTarget,
                CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
                CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
              ring1
        have directSmall := direct.trans
          ((quarterRadius_scale_le
              dynamicLocalExpLogReindexDirectScale_le_master rightIndex).trans_lt
            masterSmall)
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := (Nat.le_max_left leftStart rightStart).trans
              (startLeRight.trans rightLeLeft)
            right_ge := (Nat.le_max_right leftStart rightStart).trans startLeRight
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have leftTail :=
                (dynamicLocalExpLogApproximation input disk).later_close
                  leftOrder
              have leftRadiusToMaster :
                  CCL.FiniteGeometric.quarterRadius
                      dynamicLocalExpLogErrorScale leftIndex ≤
                    CCL.FiniteGeometric.quarterRadius
                      dynamicLocalExpLogReindexMasterScale rightIndex :=
                (quarterRadius_scale_le
                    dynamicLocalExpLogScale_le_reindexMaster leftIndex).trans
                  (quarterRadius_index_antitone
                    dynamicLocalExpLogReindexMasterScale_nonneg rightLeLeft)
              have leftTailSmall := leftTail.trans_lt
                (leftRadiusToMaster.trans_lt masterSmall)
              have rightTail := wrapperExp.later_close rightOrder
              have rightTailSmall := rightTail.trans_lt
                ((quarterRadius_scale_le
                    progressiveExpScale_le_dynamicLocalExpLogReindexMaster
                    rightIndex).trans_lt masterSmall)
              have rightTailReverse :
                  normSq
                      (wrapperExp.sample rightIndex -
                        wrapperExp.sample rightLater) < smallTarget := by
                have identity : wrapperExp.sample rightIndex -
                      wrapperExp.sample rightLater =
                    -(wrapperExp.sample rightLater -
                      wrapperExp.sample rightIndex) := by
                  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                    simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
                rw [identity, normSq_neg]
                exact rightTailSmall
              have baseIdentity :
                  (dynamicLocalExpLogApproximation input disk).sample
                      leftIndex =
                    CCL.FiniteExp.sample
                      (source.sample leftIndex) (2 * leftIndex + 1) := by
                rfl
              have wrapperIdentity : wrapperExp.sample rightIndex =
                  CCL.FiniteExp.sample
                    (source.sample sourceIndex) rightIndex := rfl
              rw [← baseIdentity, ← wrapperIdentity] at directSmall
              have middle := (normSq_sub_le_via _ _ _).trans_lt
                (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                  (by decide)
                  (RFAP.ConstructiveFraction.add_lt_add_direct
                    directSmall rightTailReverse))
              calc
                normSq
                    ((dynamicLocalExpLogApproximation input disk).sample
                        leftLater - wrapperExp.sample rightLater) ≤
                  2 *
                    (normSq
                        ((dynamicLocalExpLogApproximation input disk).sample
                            leftLater -
                          (dynamicLocalExpLogApproximation input disk).sample
                            leftIndex) +
                      normSq
                        ((dynamicLocalExpLogApproximation input disk).sample
                            leftIndex - wrapperExp.sample rightLater)) :=
                  normSq_sub_le_via _ _ _
                _ < 2 *
                    (smallTarget + 2 * (smallTarget + smallTarget)) :=
                  RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                    (by decide)
                    (RFAP.ConstructiveFraction.add_lt_add_direct
                      leftTailSmall middle)
                _ = 10 * smallTarget := by ring1
                _ < target := by
                  dsimp only [smallTarget]
                  exact ten_sixteenths_lt positive } }

/-- Name-level form of the finite resampling bridge for local exp-log. -/
def dynamicLocalExpLog_toLocalExp (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input) :
    NamedEquivalent
      (dynamicLocalExpLogApproximation input disk).toNamed
      (CCL.ProgressiveExp.named
        (CCL.ProgressiveComplexLog.named input disk)
        (localComplexLogUnitDisk input disk)) :=
  approximationEquivalent_toNamed
    (dynamicLocalExpLogReindexEquivalent input disk)

/-- The actual total exponential of a coherent local complex-log name reaches
the explicit diagonal finite exp-log program. -/
def automaticExpLocalComplexLog_toDynamic (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ProgressiveComplexLog.named input disk))
      (dynamicLocalExpLogApproximation input disk).toNamed :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (automaticExp_toLocal
      { name := CCL.ProgressiveComplexLog.named input disk
        coherent := localComplexLogCoherent input disk }
      (localComplexLogUnitDisk input disk))
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (dynamicLocalExpLog_toLocalExp input disk))

/-- The actual total exponential of the progressive local logarithm is the
productive CCL name generated by exact rational Möbius reconstruction of its
finite reduced readings. -/
def automaticExpLocalComplexLog_toChart (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ProgressiveComplexLog.named input disk))
      (dynamicLocalExpLogChartApproximation input disk).toNamed :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (automaticExpLocalComplexLog_toDynamic input disk)
    (dynamicLocalExpLog_chart_named_equivalent input disk)

/-- Multiplying the actual total local-log exponential by one displayed
rational factor reaches the pointwise scaled Möbius reconstruction program.
This packages every analytic and multiplication-resampling step; only the
algebraic relation between the chart's reduced input and its original input
remains to identify a full logarithm inverse. -/
def automaticExpLocalComplexLog_mulExact_toScaledChart (input : Named)
    (disk : CCL.ProgressiveComplexLog.Disk input)
    (factor : Gaussian) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.named
          (CCL.ProgressiveComplexLog.named input disk))
        (CCL.ProgressiveTransducer.Named.exact factor))
      (scaledDynamicLocalExpLogChartApproximation input disk factor).toNamed :=
  by
    let actualLeft : CoherentNamed :=
      { name := CCL.ProgressiveExpRange.named
          (CCL.ProgressiveComplexLog.named input disk)
        coherent := expNamedCoherent
          (CCL.ProgressiveComplexLog.named input disk) }
    let chartedLeft :=
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
        (dynamicLocalExpLogChartApproximation input disk)
    let exactRight :=
      CCL.ProgressiveCoherence.CoherentNamed.exact factor
    let constantRight :=
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
        (CCL.TranscendentalLaws.constantApproximation factor)
    have productsEquivalent : NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          actualLeft.name exactRight.name)
        (CCL.ProgressiveTransducer.Named.mul
          chartedLeft.name constantRight.name) :=
      coherentMul_respects actualLeft chartedLeft exactRight constantRight
        (automaticExpLocalComplexLog_toChart input disk)
        (exact_toConstantNamed factor)
    have pointwiseBridge : NamedEquivalent
        (CCL.ProgressiveTransducer.Named.mul
          (dynamicLocalExpLogChartApproximation input disk).toNamed
          (CCL.TranscendentalLaws.constantApproximation
            factor).toNamed)
        (scaledDynamicLocalExpLogChartApproximation input disk factor).toNamed :=
      mulToNamed_equivalent_pointwise
        (dynamicLocalExpLogChartApproximation input disk)
        (CCL.TranscendentalLaws.constantApproximation factor)
        (scaledDynamicLocalExpLogChartApproximation input disk factor)
        (scaledDynamicLocalExpLogChartApproximation_sample input disk factor)
    exact CCL.OperationalEquivalence.NamedEquivalent.trans
      (by simpa only [actualLeft, exactRight,
          CCL.ProgressiveCoherence.CoherentNamed.exact]
        using productsEquivalent)
      (by simpa only [chartedLeft, constantRight,
          CCL.ProgressiveCoherence.CoherentNamed.ofApproximation]
        using pointwiseBridge)

/-- A charted complex logarithm is coherent whenever its explicit additive
branch-correction name is coherent. -/
def complexLogNamedCoherent (input : Named)
    (chart : CCL.ComplexLogChart.Chart input)
    (correctionCoherent : Coherent chart.correction.process) :
    Coherent (CCL.ComplexLogChart.named input chart).process :=
  CCL.ProgressiveCoherence.Coherent.add
    (localComplexLogCoherent
      (CCL.ComplexLogChart.reduced input chart.factor
        chart.denominatorApart) chart.reducedDisk)
    correctionCoherent

end CCL.TranscendentalCoherence
