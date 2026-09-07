import CCL.Progressive.DivisionCongruence
import CCL.Transcendental.LogChartSafety

/-!
# Operational congruence for anchored logarithm charts

Two finite chart constructions may use different based process state types and
different proofs of denominator and disk safety.  When their inputs are
operationally equivalent and they retain the same rational factor and
operationally equivalent branch corrections, their actual charted logarithm
outputs are operationally equivalent.

This is the schedule-coherence bridge needed by retryable anchored logarithm
preflight.  It compares finite programs directly; it does not identify
independently selected branches from equality of their exponentials.
-/

namespace CCL.LogChartCongruence

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart

/-- Coherent packaging of the chart numerator. -/
def numeratorName (input : CoherentNamed) (branch : AnchoredChart input) :
    CoherentNamed where
  name := CCL.ComplexLogChart.numerator input.name branch.chart.factor
  coherent := CCL.ComplexLogCorrectness.numeratorCoherent
    input.name branch.chart input.coherent

/-- Coherent packaging of the unprepared chart denominator. -/
def denominatorName (input : CoherentNamed) (branch : AnchoredChart input) :
    CoherentNamed where
  name := CCL.ComplexLogChart.denominator input.name branch.chart.factor
  coherent := CCL.ComplexLogCorrectness.denominatorCoherent
    input.name branch.chart input.coherent

/-- Coherent packaging of the chart's actual apartified denominator. -/
def preparedDenominatorName (input : CoherentNamed)
    (branch : AnchoredChart input) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify
    (denominatorName input branch) branch.chart.denominatorApart

/-- Coherent packaging of the independently sampled reduced quotient. -/
def reducedName (input : CoherentNamed) (branch : AnchoredChart input) :
    CoherentNamed where
  name := CCL.ComplexLogChart.reduced input.name branch.chart.factor
    branch.chart.denominatorApart
  coherent := CCL.ComplexLogCorrectness.reducedCoherent
    input.name branch.chart input.coherent

/-- Coherent packaging of the local logarithm before adding its branch
correction. -/
def localOutputName (input : CoherentNamed) (branch : AnchoredChart input) :
    CoherentNamed where
  name := CCL.ComplexLogChart.localOutput input.name branch.chart
  coherent := CCL.TranscendentalCoherence.localComplexLogCoherent
    (CCL.ComplexLogChart.reduced input.name branch.chart.factor
      branch.chart.denominatorApart) branch.chart.reducedDisk

/-- Coherent packaging of the explicitly anchored correction. -/
def correctionName {input : CoherentNamed} (branch : AnchoredChart input) :
    CoherentNamed where
  name := branch.chart.correction
  coherent := branch.correctionCoherent

/-- Scaling by the same exact rational factor respects operational equality of
the two coherent inputs. -/
def scaled_respects
    (left right : CoherentNamed)
    (leftBranch : AnchoredChart left) (rightBranch : AnchoredChart right)
    (inputEquivalent : NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    NamedEquivalent
      (CCL.ComplexLogChart.scaled left.name leftBranch.chart.factor)
      (CCL.ComplexLogChart.scaled right.name rightBranch.chart.factor) := by
  let leftFactor := CCL.ProgressiveCoherence.CoherentNamed.exact
    leftBranch.chart.factor
  let rightFactor := CCL.ProgressiveCoherence.CoherentNamed.exact
    rightBranch.chart.factor
  have factorEquivalent : NamedEquivalent leftFactor.name rightFactor.name := by
    dsimp only [leftFactor, rightFactor]
    rw [factorEqual]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  simpa only [CCL.ComplexLogChart.scaled, leftFactor, rightFactor,
    CCL.ProgressiveCoherence.CoherentNamed.mul,
    CCL.ProgressiveCoherence.CoherentNamed.exact] using
    CCL.TranscendentalCoherence.coherentMul_respects
      leftFactor rightFactor left right factorEquivalent inputEquivalent

/-- The chart numerators respect input equivalence when the factors agree. -/
def numerator_respects
    (left right : CoherentNamed)
    (leftBranch : AnchoredChart left) (rightBranch : AnchoredChart right)
    (inputEquivalent : NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    NamedEquivalent (numeratorName left leftBranch).name
      (numeratorName right rightBranch).name := by
  let leftScaled : CoherentNamed :=
    { name := CCL.ComplexLogChart.scaled left.name leftBranch.chart.factor
      coherent := CCL.ComplexLogCorrectness.scaledCoherent
        left.name leftBranch.chart left.coherent }
  let rightScaled : CoherentNamed :=
    { name := CCL.ComplexLogChart.scaled right.name rightBranch.chart.factor
      coherent := CCL.ComplexLogCorrectness.scaledCoherent
        right.name rightBranch.chart right.coherent }
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  have scaledEquivalent : NamedEquivalent leftScaled.name rightScaled.name :=
    scaled_respects left right leftBranch rightBranch inputEquivalent factorEqual
  simpa only [numeratorName, CCL.ComplexLogChart.numerator, leftScaled,
    rightScaled, one, CCL.ComplexLogChart.exactOne,
    CCL.ProgressiveCoherence.CoherentNamed.sub,
    CCL.ProgressiveCoherence.CoherentNamed.exact] using
    (CCL.ProgressiveCalculusCongruence.subtraction_respects
      leftScaled rightScaled one one scaledEquivalent
      (CCL.OperationalEquivalence.NamedEquivalent.refl one.name)).equivalent

/-- The unprepared chart denominators respect input equivalence when the
factors agree. -/
def denominator_respects
    (left right : CoherentNamed)
    (leftBranch : AnchoredChart left) (rightBranch : AnchoredChart right)
    (inputEquivalent : NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    NamedEquivalent (denominatorName left leftBranch).name
      (denominatorName right rightBranch).name := by
  let leftScaled : CoherentNamed :=
    { name := CCL.ComplexLogChart.scaled left.name leftBranch.chart.factor
      coherent := CCL.ComplexLogCorrectness.scaledCoherent
        left.name leftBranch.chart left.coherent }
  let rightScaled : CoherentNamed :=
    { name := CCL.ComplexLogChart.scaled right.name rightBranch.chart.factor
      coherent := CCL.ComplexLogCorrectness.scaledCoherent
        right.name rightBranch.chart right.coherent }
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  have scaledEquivalent : NamedEquivalent leftScaled.name rightScaled.name :=
    scaled_respects left right leftBranch rightBranch inputEquivalent factorEqual
  simpa only [denominatorName, CCL.ComplexLogChart.denominator, leftScaled,
    rightScaled, one, CCL.ComplexLogChart.exactOne,
    CCL.ProgressiveCoherence.CoherentNamed.add,
    CCL.ProgressiveCoherence.CoherentNamed.exact] using
    CCL.TranscendentalCoherence.coherentAdd_respects
      leftScaled rightScaled one one scaledEquivalent
      (CCL.OperationalEquivalence.NamedEquivalent.refl one.name)

/-- Independently apartified versions of equivalent chart denominators remain
operationally equivalent. -/
def preparedDenominator_respects
    (left right : CoherentNamed)
    (leftBranch : AnchoredChart left) (rightBranch : AnchoredChart right)
    (inputEquivalent : NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    NamedEquivalent (preparedDenominatorName left leftBranch).name
      (preparedDenominatorName right rightBranch).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent
        (denominatorName left leftBranch) leftBranch.chart.denominatorApart))
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (denominator_respects left right leftBranch rightBranch
        inputEquivalent factorEqual)
      (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent
        (denominatorName right rightBranch)
        rightBranch.chart.denominatorApart))

/-- The reduced Möbius arguments of two fixed-factor charts respect
operational input equivalence. -/
def reduced_respects
    (left right : CoherentNamed)
    (leftBranch : AnchoredChart left) (rightBranch : AnchoredChart right)
    (inputEquivalent : NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    NamedEquivalent (reducedName left leftBranch).name
      (reducedName right rightBranch).name := by
  simpa only [reducedName, numeratorName, preparedDenominatorName,
    denominatorName, CCL.ProgressiveCoherence.CoherentNamed.apartify,
    CCL.ProgressiveCoherence.CoherentNamed.div,
    CCL.ComplexLogChart.reduced,
    CCL.ComplexLogChart.preparedDenominator,
    CCL.ComplexLogChart.preparedDenominatorApart] using
    CCL.ProgressiveDivisionCongruence.coherentDiv_respects
      (numeratorName left leftBranch) (numeratorName right rightBranch)
      (preparedDenominatorName left leftBranch)
      (preparedDenominatorName right rightBranch)
      (CCL.ComplexLogChart.preparedDenominatorApart left.name
        leftBranch.chart.factor leftBranch.chart.denominatorApart)
      (CCL.ComplexLogChart.preparedDenominatorApart right.name
        rightBranch.chart.factor rightBranch.chart.denominatorApart)
      (numerator_respects left right leftBranch rightBranch
        inputEquivalent factorEqual)
      (preparedDenominator_respects left right leftBranch rightBranch
        inputEquivalent factorEqual)

/-- The local finite logarithms respect fixed-factor chart input equivalence,
independently of the particular disk-certificate proofs. -/
def localOutput_respects
    (left right : CoherentNamed)
    (leftBranch : AnchoredChart left) (rightBranch : AnchoredChart right)
    (inputEquivalent : NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    NamedEquivalent (localOutputName left leftBranch).name
      (localOutputName right rightBranch).name :=
  CCL.LogBranchGeometry.localLogNamed_respects
    leftBranch.chart.reducedDisk rightBranch.chart.reducedDisk
    (reduced_respects left right leftBranch rightBranch
      inputEquivalent factorEqual)

/-- Full anchored chart congruence.  Correction equivalence is an explicit
premise because matching exponentials alone does not identify a logarithm
branch. -/
def output_respects
    (left right : CoherentNamed)
    (leftBranch : AnchoredChart left) (rightBranch : AnchoredChart right)
    (inputEquivalent : NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor)
    (correctionEquivalent : NamedEquivalent
      leftBranch.chart.correction rightBranch.chart.correction) :
    NamedEquivalent leftBranch.output.name rightBranch.output.name := by
  simpa only [CCL.LogBranchCalculus.AnchoredChart.output,
    CCL.ComplexLogChart.named, CCL.ComplexLogChart.localOutput,
    localOutputName, correctionName,
    CCL.ProgressiveCoherence.CoherentNamed.add] using
    CCL.TranscendentalCoherence.coherentAdd_respects
      (localOutputName left leftBranch) (localOutputName right rightBranch)
      (correctionName leftBranch) (correctionName rightBranch)
      (localOutput_respects left right leftBranch rightBranch
        inputEquivalent factorEqual)
      correctionEquivalent

/-- Two safe transports from the same fixed source anchor have equivalent
outputs whenever their target names are operationally equivalent.  Both
transports retain the source factor and correction by construction. -/
def transportedOutput_respects
    {sourceInput leftTarget rightTarget : CoherentNamed}
    (source : AnchoredChart sourceInput)
    (leftExtension : CCL.LogBranchGeometry.SafeOverlapExtension
      sourceInput leftTarget source)
    (rightExtension : CCL.LogBranchGeometry.SafeOverlapExtension
      sourceInput rightTarget source)
    (targetEquivalent : NamedEquivalent leftTarget.name rightTarget.name) :
    NamedEquivalent
      (leftExtension.transport source).output.name
      (rightExtension.transport source).output.name :=
  output_respects leftTarget rightTarget
    (leftExtension.transport source) (rightExtension.transport source)
    targetEquivalent rfl
    (CCL.OperationalEquivalence.NamedEquivalent.refl
      source.chart.correction)

end CCL.LogChartCongruence
