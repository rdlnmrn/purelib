import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.CalculusCongruence

/-!
# Finite geometry for transporting and selecting logarithm branches

An anchored complex logarithm is local data.  This file supplies the missing
geometric constructors around that data.

* `SafeOverlapExtension` rechecks one chart's rational denominator and
  reduced-disk inequalities on a second coherent name and records an actual
  rational point admitted by both finite enclosures.  The original factor,
  correction process, and correction certificate can then be transported.
* `LocalExpInjectivity` is a displayed finite cell, membership certificates
  for two particular coherent names, and the local exponential-injectivity
  rule for that pair.  It is deliberately local and never chooses a global
  logarithm branch.
* `SelectedLogarithm.ofOverlap` combines those two pieces of finite data.  It
  constructs an anchored chart over the computed exponential and derives the
  zero-alignment certificate required for `log (exp x) = x`.

The local complex-log congruence proved first is quantitative: it compares
finite reduced-argument samples with the existing rational sensitivity bound
and finite truncation bounds.  No completed logarithm or limiting argument is
introduced.
-/

namespace CCL.LogBranchGeometry

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent :=
  CCL.OperationalEquivalence.NamedEquivalent
abbrev Equivalent := CCL.OperationalEquivalence.Equivalent
abbrev Chart := CCL.ComplexLogChart.Chart
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart
abbrev BitLaw := CCL.ProgressiveCalculusCongruence.BitLaw

open RFAP.ConstructiveGaussian.Gaussian
open CCL.OperationalFieldLaws

private theorem scale_mul_div_cancel (scale target : Coordinate)
    (scale_ne : scale ≠ 0) : scale * (target / scale) = target := by
  rw [RFAP.ConstructiveFraction.mul_comm]
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne target scale scale_ne

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

/-! ## Quantitative congruence of the local complex logarithm -/

/-- The finite local complex-log approximation respects operational equality
of reduced-argument names.  A common finite Horner depth, the displayed
`sampleInputScale`, and two finite truncation estimates answer each requested
rational comparison. -/
def localLogApproximation_respects {left right : Named}
    (leftDisk : CCL.ProgressiveComplexLog.Disk left)
    (rightDisk : CCL.ProgressiveComplexLog.Disk right)
    (equivalent : NamedEquivalent left right) :
    Equivalent
      (CCL.ProgressiveComplexLog.approximation left leftDisk)
      (CCL.ProgressiveComplexLog.approximation right rightDisk) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 16
    have smallPositive : 0 < smallTarget :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    let inputScale := CCL.FiniteComplexLog.sampleInputScale
    have inputScalePositive : 0 < inputScale := by
      change (0 : Coordinate) < 2 * (16 + 16)
      decide
    let inputTarget := smallTarget / inputScale
    have inputPositive : 0 < inputTarget :=
      RFAP.ConstructiveFraction.div_pos_direct smallPositive
        inputScalePositive
    let inputComparison :=
      equivalent.compare leftStart rightStart inputTarget inputPositive
    let start := max (max leftStart rightStart)
      (max inputComparison.leftIndex inputComparison.rightIndex)
    let depth := CCL.FiniteGeometric.firstQuarterBelow
      5 start smallTarget
    have startLeDepth : start ≤ depth :=
      CCL.FiniteGeometric.firstQuarterBelow_ge
        5 start smallTarget
    have tailSmall :
        CCL.FiniteGeometric.quarterRadius 5 depth <
          smallTarget :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate
        5 (by decide) start smallTarget smallPositive
    have tailSmall' : 5 * (1 / 4 : Coordinate) ^ depth < smallTarget := by
      simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        using tailSmall
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
            CCL.ProgressiveComplexLog.inputSample left leftLater
          let rightInput :=
            CCL.ProgressiveComplexLog.inputSample right rightLater
          have leftInputBound : normSq leftInput ≤ 1 / 9 :=
            CCL.ProgressiveComplexLog.inputSample_bound
              leftDisk leftLater
          have rightInputBound : normSq rightInput ≤ 1 / 9 :=
            CCL.ProgressiveComplexLog.inputSample_bound
              rightDisk rightLater
          have inputClose : normSq (leftInput - rightInput) < inputTarget :=
            inputComparison.close
              (inputLeftLeDepth.trans leftOrder)
              (inputRightLeDepth.trans rightOrder)
          have directLe :=
            CCL.FiniteComplexLog.sample_input_close
              leftInputBound rightInputBound depth
          have direct :
              normSq
                  (CCL.FiniteComplexLog.sample leftInput depth -
                    CCL.FiniteComplexLog.sample rightInput depth) <
                smallTarget := by
            calc
              normSq
                  (CCL.FiniteComplexLog.sample leftInput depth -
                    CCL.FiniteComplexLog.sample rightInput depth) ≤
                inputScale * normSq (leftInput - rightInput) := directLe
              _ < inputScale * inputTarget :=
                RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                  inputScalePositive inputClose
              _ = smallTarget := by
                dsimp only [inputTarget]
                exact scale_mul_div_cancel inputScale smallTarget
                  inputScalePositive.ne'
          have leftTail :
              normSq
                  (CCL.FiniteComplexLog.sample leftInput leftLater -
                    CCL.FiniteComplexLog.sample leftInput depth) <
                smallTarget :=
            (CCL.FiniteComplexLog.sample_later_close
              leftInputBound leftOrder).trans_lt tailSmall'
          have rightTailForward :
              normSq
                  (CCL.FiniteComplexLog.sample rightInput rightLater -
                    CCL.FiniteComplexLog.sample rightInput depth) <
                smallTarget :=
            (CCL.FiniteComplexLog.sample_later_close
              rightInputBound rightOrder).trans_lt tailSmall'
          have rightTail :
              normSq
                  (CCL.FiniteComplexLog.sample rightInput depth -
                    CCL.FiniteComplexLog.sample rightInput rightLater) <
                smallTarget := by
            have identity :
                CCL.FiniteComplexLog.sample rightInput depth -
                    CCL.FiniteComplexLog.sample rightInput rightLater =
                  -(CCL.FiniteComplexLog.sample rightInput rightLater -
                    CCL.FiniteComplexLog.sample rightInput depth) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [identity, normSq_neg]
            exact rightTailForward
          have middle :
              normSq
                  (CCL.FiniteComplexLog.sample leftInput depth -
                    CCL.FiniteComplexLog.sample rightInput rightLater) <
                2 * (smallTarget + smallTarget) :=
            (normSq_sub_le_via _ _ _).trans_lt
              (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct direct rightTail))
          change normSq
              (CCL.FiniteComplexLog.sample leftInput leftLater -
                CCL.FiniteComplexLog.sample rightInput rightLater) <
              target
          calc
            normSq
                (CCL.FiniteComplexLog.sample leftInput leftLater -
                  CCL.FiniteComplexLog.sample rightInput rightLater) ≤
              2 *
                (normSq
                    (CCL.FiniteComplexLog.sample leftInput leftLater -
                      CCL.FiniteComplexLog.sample leftInput depth) +
                  normSq
                    (CCL.FiniteComplexLog.sample leftInput depth -
                      CCL.FiniteComplexLog.sample rightInput
                        rightLater)) :=
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

/-- Productive-name form of finite local complex-log congruence. -/
def localLogNamed_respects {left right : Named}
    (leftDisk : CCL.ProgressiveComplexLog.Disk left)
    (rightDisk : CCL.ProgressiveComplexLog.Disk right)
    (equivalent : NamedEquivalent left right) :
    NamedEquivalent
      (CCL.ProgressiveComplexLog.named left leftDisk)
      (CCL.ProgressiveComplexLog.named right rightDisk) :=
  CCL.OperationalEquivalence.Equivalent.trans
    (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
      (CCL.ProgressiveComplexLog.approximation left leftDisk))
    (CCL.OperationalEquivalence.Equivalent.trans
      (localLogApproximation_respects leftDisk rightDisk equivalent)
      (CCL.OperationalEquivalence.Equivalent.symm
        (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
          (CCL.ProgressiveComplexLog.approximation
            right rightDisk))))

/-! ## Finite overlap and safe chart transport -/

/-- One displayed rational point admitted by both current finite enclosures.
This witnesses actual overlap; it is not an assertion about completed chart
domains. -/
structure OverlapWitness (left right : CoherentNamed) where
  point : Gaussian
  left_possible : left.name.process.Possible left.name.state point
  right_possible : right.name.process.Possible right.name.state point

/-- Rechecked rational safety data for extending an already anchored chart to
a second coherent input.  The factor and correction are inherited from the
source branch; only the finite denominator and reduced-disk inequalities are
re-established on the target enclosure. -/
structure SafeOverlapExtension (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput) where
  overlap : OverlapWitness sourceInput targetInput
  lowerSq : Coordinate
  lowerSq_positive : 0 < lowerSq
  denominatorLower :
    ∀ (state : targetInput.name.process.State) {value : Gaussian},
      targetInput.name.process.Possible state value →
        lowerSq ≤ normSq (source.chart.factor * value + 1)
  reducedBound : ∀ {numeratorSource denominatorSource : Gaussian},
    targetInput.name.process.Possible targetInput.name.state numeratorSource →
    targetInput.name.process.Possible targetInput.name.state denominatorSource →
      normSq
          ((source.chart.factor * numeratorSource - 1) /
            (source.chart.factor * denominatorSource + 1)) ≤ 1 / 9

namespace SafeOverlapExtension

/-- The target chart computed from the displayed overlap safety data. -/
def chart {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    (extension : SafeOverlapExtension sourceInput targetInput source) :
    Chart targetInput.name :=
  CCL.ComplexLogChart.Chart.ofBounds targetInput.name
    source.chart.factor extension.lowerSq extension.lowerSq_positive
    extension.denominatorLower extension.reducedBound source.chart.correction

@[simp] theorem chart_factor {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    (extension : SafeOverlapExtension sourceInput targetInput source) :
    extension.chart.factor = source.chart.factor := rfl

@[simp] theorem chart_correction {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    (extension : SafeOverlapExtension sourceInput targetInput source) :
    extension.chart.correction = source.chart.correction := rfl

/-- Analytic continuation through a certified finite overlap: the target
chart is rebuilt from target-side rational inequalities while retaining the
source factor and anchored correction. -/
def transport {sourceInput targetInput : CoherentNamed}
    (source : AnchoredChart sourceInput)
    (extension : SafeOverlapExtension sourceInput targetInput source) :
    AnchoredChart targetInput :=
  { chart := extension.chart
    certificate :=
      { factor_ne_zero := source.certificate.factor_ne_zero
        correction_exponential := source.certificate.correction_exponential }
    correctionCoherent := source.correctionCoherent }

@[simp] theorem transport_factor {sourceInput targetInput : CoherentNamed}
    (source : AnchoredChart sourceInput)
    (extension : SafeOverlapExtension sourceInput targetInput source) :
    (extension.transport source).chart.factor = source.chart.factor := rfl

@[simp] theorem transport_correction {sourceInput targetInput : CoherentNamed}
    (source : AnchoredChart sourceInput)
    (extension : SafeOverlapExtension sourceInput targetInput source) :
    (extension.transport source).chart.correction = source.chart.correction := rfl

/-- The transported branch is still an ordinary productive CCL computation. -/
theorem transport_productive {sourceInput targetInput : CoherentNamed}
    (source : AnchoredChart sourceInput)
    (extension : SafeOverlapExtension sourceInput targetInput source)
    (count : Nat) :
    (extension.transport source).output.name.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (extension.transport source).output.name.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        (extension.transport source).output.name.machine count).emitted.length =
          count :=
  CCL.ComplexLogChart.productive targetInput.name
    (extension.transport source).chart count

/-- Full finite request contract for the transported branch: one refinement
answers the rational accuracy request, and the ordinary CCL cursor emits the
requested number of bits with exact parser semantics. -/
theorem transport_bitstream_and_error
    {sourceInput targetInput : CoherentNamed}
    (source : AnchoredChart sourceInput)
    (extension : SafeOverlapExtension sourceInput targetInput source)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    let refined := CCL.TranscendentalOutput.refined
      (extension.transport source).output.name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          refined.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        refined.machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        refined.process refined.state
        (CCL.ProgressiveTransducer.advance refined.machine count) :=
  CCL.TranscendentalOutput.refined_bitstream_and_error
    (extension.transport source).output.name target positive count

/-- Rechecking safety and transporting the anchored correction preserves the
finite exponential/logarithm inverse. -/
def transport_exponential_inverse
    {sourceInput targetInput : CoherentNamed}
    (source : AnchoredChart sourceInput)
    (extension : SafeOverlapExtension sourceInput targetInput source) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (extension.transport source).output.name)
      targetInput.name :=
  (extension.transport source).exponential_inverse

end SafeOverlapExtension

/-! ## Explicitly aligned branch laws -/

/-- Operational equality of two names gives a zero discrepancy by actual CCL
addition and negation. -/
def difference_zero_of_equivalent (left right : CoherentNamed)
    (equivalent : NamedEquivalent right.name left.name) :
    NamedEquivalent
      (CCL.LogBranchCalculus.difference left right).name
      (CCL.ProgressiveTransducer.Named.exact 0) := by
  let negativeLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.neg left
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by
      simpa only [CCL.LogBranchCalculus.difference, negativeLeft,
        CCL.ProgressiveCoherence.CoherentNamed.add,
        CCL.ProgressiveCoherence.CoherentNamed.neg] using
        CCL.TranscendentalCoherence.coherentAdd_respects
          right left negativeLeft negativeLeft equivalent
          (CCL.OperationalEquivalence.NamedEquivalent.refl
            negativeLeft.name))
    (coherentAdd_neg_right left)

/-- Conversely, a supplied zero discrepancy identifies the two local branch
outputs.  This is finite field algebra, not an appeal to global logarithm
uniqueness. -/
def equivalent_of_difference_zero (left right : CoherentNamed)
    (alignment : CCL.LogExpInverse.LocalAlignment left right) :
    NamedEquivalent right.name left.name := by
  let negativeLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.neg left
  let discrepancy := CCL.LogBranchCalculus.difference left right
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  let discrepancyPlusLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.add discrepancy left
  let zeroPlusLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.add zero left
  let cancelled :=
    CCL.ProgressiveCoherence.CoherentNamed.add negativeLeft left
  let rightPlusCancelled :=
    CCL.ProgressiveCoherence.CoherentNamed.add right cancelled
  have reassociate : NamedEquivalent discrepancyPlusLeft.name
      rightPlusCancelled.name := by
    simpa only [discrepancyPlusLeft, discrepancy, negativeLeft,
      rightPlusCancelled, cancelled,
      CCL.LogBranchCalculus.difference,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg] using
      coherentAdd_assoc right negativeLeft left
  have cancelLeft : NamedEquivalent cancelled.name zero.name := by
    simpa only [cancelled, negativeLeft, zero,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      coherentAdd_neg_left left
  have replaceCancelled : NamedEquivalent rightPlusCancelled.name
      (CCL.ProgressiveCoherence.CoherentNamed.add right zero).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      right right cancelled zero
      (CCL.OperationalEquivalence.NamedEquivalent.refl right.name)
      cancelLeft
  have removeZero : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add right zero).name
      right.name := coherentAdd_zero_right right
  have discrepancyPlusLeft_to_right :
      NamedEquivalent discrepancyPlusLeft.name right.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans reassociate
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        replaceCancelled removeZero)
  have replaceDiscrepancy : NamedEquivalent discrepancyPlusLeft.name
      zeroPlusLeft.name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      discrepancy zero left left alignment
      (CCL.OperationalEquivalence.NamedEquivalent.refl left.name)
  have removeLeadingZero : NamedEquivalent zeroPlusLeft.name left.name := by
    simpa only [zeroPlusLeft, zero,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      coherentAdd_zero_left left
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      discrepancyPlusLeft_to_right)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      replaceDiscrepancy removeLeadingZero)

/-- Explicit finite data for the guarded logarithm product law: the displayed
product input must be the actual CCL product, and the selected product branch
must have zero discrepancy from the selected sum branch. -/
def ProductAlignment
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : AnchoredChart leftInput)
    (rightBranch : AnchoredChart rightInput)
    (productBranch : AnchoredChart productInput) : Type :=
  NamedEquivalent productInput.name
      (CCL.ProgressiveTransducer.Named.mul
        leftInput.name rightInput.name) ×
    CCL.LogExpInverse.LocalAlignment
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftBranch.output rightBranch.output) productBranch.output

namespace ProductAlignment

def productEquivalent
    {leftInput rightInput productInput : CoherentNamed}
    {leftBranch : AnchoredChart leftInput}
    {rightBranch : AnchoredChart rightInput}
    {productBranch : AnchoredChart productInput}
    (alignment : ProductAlignment leftInput rightInput productInput
      leftBranch rightBranch productBranch) :
    NamedEquivalent productInput.name
      (CCL.ProgressiveTransducer.Named.mul
        leftInput.name rightInput.name) :=
  alignment.1

def zeroDiscrepancy
    {leftInput rightInput productInput : CoherentNamed}
    {leftBranch : AnchoredChart leftInput}
    {rightBranch : AnchoredChart rightInput}
    {productBranch : AnchoredChart productInput}
    (alignment : ProductAlignment leftInput rightInput productInput
      leftBranch rightBranch productBranch) :
    CCL.LogExpInverse.LocalAlignment
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftBranch.output rightBranch.output) productBranch.output :=
  alignment.2

end ProductAlignment

/-- The same finite product certificate also recovers the weaker but
unconditional branch statement: its discrepancy exponentiates to one. -/
def logarithm_product_discrepancy_unit
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : AnchoredChart leftInput)
    (rightBranch : AnchoredChart rightInput)
    (productBranch : AnchoredChart productInput)
    (alignment : ProductAlignment leftInput rightInput productInput
      leftBranch rightBranch productBranch) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.LogBranchCalculus.productBranchDiscrepancy
          leftInput rightInput productInput leftBranch rightBranch
            productBranch).name)
      (CCL.ProgressiveTransducer.Named.exact 1) :=
  CCL.LogBranchCalculus.exp_productBranchDiscrepancy_unit
    leftInput rightInput productInput leftBranch rightBranch productBranch
      alignment.productEquivalent

/-- On an explicitly zero-aligned product branch, the actual logarithm CCL
equals the actual sum of the two logarithm CCLs. -/
def logarithm_product_of_alignment
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : AnchoredChart leftInput)
    (rightBranch : AnchoredChart rightInput)
    (productBranch : AnchoredChart productInput)
    (alignment : ProductAlignment leftInput rightInput productInput
      leftBranch rightBranch productBranch) :
    NamedEquivalent productBranch.output.name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftBranch.output rightBranch.output).name :=
  equivalent_of_difference_zero _ _ alignment.zeroDiscrepancy

/-- Bit-producing form of the guarded logarithm product law. -/
def logarithm_product_bitLaw
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : AnchoredChart leftInput)
    (rightBranch : AnchoredChart rightInput)
    (productBranch : AnchoredChart productInput)
    (alignment : ProductAlignment leftInput rightInput productInput
      leftBranch rightBranch productBranch) :
    BitLaw productBranch.output
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftBranch.output rightBranch.output) :=
  CCL.ProgressiveCalculusCongruence.BitLaw.ofEquivalent
    (logarithm_product_of_alignment leftInput rightInput productInput
      leftBranch rightBranch productBranch alignment)

/-! ## Finite local selection of the preimage of an exponential -/

/-- A displayed rational disk used only as a finite local cell. -/
structure FiniteCell where
  center : Gaussian
  radiusSq : Coordinate
  radiusSq_positive : 0 < radiusSq
  radiusSq_le_one : radiusSq ≤ 1

/-- The current finite enclosure of one coherent name lies in the displayed
cell. -/
structure CellMember (cell : FiniteCell) (value : CoherentNamed) : Prop where
  possible_near : ∀ {candidate : Gaussian},
    value.name.process.Possible value.name.state candidate →
      normSq (candidate - cell.center) ≤ cell.radiusSq

/-- Pair-specific local injectivity of the finite exponential computation.
The geometric cell and both membership proofs are data; `identify` is the
local theorem for this displayed pair, not a global injectivity assertion. -/
structure LocalExpInjectivity (left right : CoherentNamed) where
  cell : FiniteCell
  leftMember : CellMember cell left
  rightMember : CellMember cell right
  identify : NamedEquivalent
      (CCL.ProgressiveExpRange.named left.name)
      (CCL.ProgressiveExpRange.named right.name) →
    NamedEquivalent left.name right.name

/-- The result of finite preimage selection: both the constructed anchored
chart and the derived zero alignment are retained. -/
def SelectedLogarithm (input : CoherentNamed) : Type 1 :=
  Sigma fun branch : AnchoredChart
    (CCL.LogExpInverse.exponentialInput input) =>
      CCL.LogExpInverse.LocalAlignment input branch.output

namespace SelectedLogarithm

def branch {input : CoherentNamed} (selection : SelectedLogarithm input) :
    AnchoredChart (CCL.LogExpInverse.exponentialInput input) :=
  selection.1

def alignment {input : CoherentNamed} (selection : SelectedLogarithm input) :
    CCL.LogExpInverse.LocalAlignment input selection.branch.output :=
  selection.2

/-- Construct the logarithm branch over the actual computed exponential by
transport through a certified overlap, then use the displayed local
injectivity cell to select the preimage near `input`.  The caller supplies no
`LocalAlignment`; it is computed below. -/
def ofOverlap (input sourceInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (extension : SafeOverlapExtension sourceInput
      (CCL.LogExpInverse.exponentialInput input) source)
    (injectivity : LocalExpInjectivity
      (extension.transport source).output input) :
    SelectedLogarithm input := by
  let branch := extension.transport source
  have exponentials : NamedEquivalent
      (CCL.ProgressiveExpRange.named branch.output.name)
      (CCL.ProgressiveExpRange.named input.name) := by
    simpa only [branch, CCL.LogExpInverse.exponentialInput,
      CCL.TranscendentalCoherence.exp] using
      branch.exponential_inverse
  have selected : NamedEquivalent branch.output.name input.name :=
    injectivity.identify exponentials
  exact ⟨branch, difference_zero_of_equivalent input branch.output selected⟩

/-- The constructed local branch proves the reverse exponential/logarithm
inverse without a caller-supplied alignment premise. -/
def logarithm_exponential_inverse (input : CoherentNamed)
    (selection : SelectedLogarithm input) :
    NamedEquivalent selection.branch.output.name input.name :=
  CCL.LogExpInverse.logarithm_exponential_inverse input
    selection.branch selection.alignment

/-- Bit-producing form of the automatically selected local inverse. -/
def logarithm_exponential_bitLaw (input : CoherentNamed)
    (selection : SelectedLogarithm input) :
    BitLaw selection.branch.output input :=
  CCL.ProgressiveCalculusCongruence.BitLaw.ofEquivalent
    (selection.logarithm_exponential_inverse input)

end SelectedLogarithm

end CCL.LogBranchGeometry
