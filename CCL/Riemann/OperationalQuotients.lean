import CCL.Progressive.DivisionCongruence
import CCL.Riemann.FiniteQuotientVariation
import CCL.Transcendental.Coherence
import CCL.Arithmetic.OperationalFieldLaws

/-!
# Riemann compatibility facade for operational quotient congruence

The general finite quotient construction and congruence theorem now live in
`CCL.Progressive.DivisionCongruence`, below the Riemann layer.  This module
retains the established Riemann names and the scalar-cancellation consequences
which use the broader operational field-law library.
-/

namespace CCL.Riemann.OperationalQuotients

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev Equivalent := CCL.OperationalEquivalence.Equivalent
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev Apart := CCL.ProgressiveTransducer.Named.Apart

open RFAP.ConstructiveGaussian.Gaussian

export CCL.ProgressiveDivisionCongruence
  (sampled_lower sampled_nonzero sampledQuotientErrorScale
    sampledQuotientErrorScale_nonnegative sampledQuotientApproximation
    sampledQuotientApproximation_sample commonLower commonLower_positive
    quotientComparisonCoefficient quotientComparisonCoefficient_nonnegative
    quotientComparisonTarget quotientComparisonTarget_positive
    quotientComparisonTarget_budget_lt sampledQuotientApproximation_respects
    coherentQuotientBridgeCoefficient coherentQuotientBridgeCoefficient_positive
    coherentQuotientBridgeTarget coherentQuotientBridgeTarget_positive
    coherentQuotientBridgeTarget_budget_lt coherentDiv_toSampled
    coherentDiv_respects)

/-- The actual apartness-certified reciprocal is a left operational inverse.
The proof normalizes the quotient and product to equal-index finite Gaussian
samples and applies exact rational cancellation at each displayed index. -/
def reciprocal_mul_cancel (denominator : CoherentNamed)
    (apart : Apart denominator.name) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.div
          (CCL.ProgressiveCoherence.CoherentNamed.exact 1)
          denominator apart)
        denominator).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 1).name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let reciprocal := CCL.ProgressiveCoherence.CoherentNamed.div
    one denominator apart
  let quotient := sampledQuotientApproximation one denominator apart
  let denominatorSource :=
    CCL.ProgressiveSampling.approximation denominator.name
  let sampledReciprocal :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation quotient
  let sampledDenominator :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation denominatorSource
  have reciprocalEquivalent : NamedEquivalent reciprocal.name
      sampledReciprocal.name := by
    simpa only [reciprocal, one, sampledReciprocal,
      CCL.ProgressiveCoherence.CoherentNamed.div,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      coherentDiv_toSampled one denominator apart
  have denominatorEquivalent : NamedEquivalent denominator.name
      sampledDenominator.name := by
    simpa only [sampledDenominator,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      CCL.TranscendentalCoherence.named_toSamplingNamed denominator.name
  have replaceOperands : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        reciprocal denominator).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        sampledReciprocal sampledDenominator).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      reciprocal sampledReciprocal denominator sampledDenominator
      reciprocalEquivalent denominatorEquivalent
  apply CCL.OperationalEquivalence.NamedEquivalent.trans replaceOperands
  have pointwise : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        sampledReciprocal sampledDenominator).name
      (CCL.ProgressiveSampling.approximation one.name).toNamed := by
    simpa only [sampledReciprocal, sampledDenominator,
      CCL.ProgressiveCoherence.CoherentNamed.mul,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      CCL.TranscendentalCoherence.mulToNamed_equivalent_pointwise
        quotient denominatorSource
        (CCL.ProgressiveSampling.approximation one.name) (by
          intro index
          rw [sampledQuotientApproximation_sample]
          exact (RFAP.ExplicitField.div_mul_cancel _
            (sampled_nonzero denominator apart index)).symm)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans pointwise
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.TranscendentalCoherence.named_toSamplingNamed one.name))

/-- An apartness-certified operational quotient cancels when multiplied on
the right by its exact denominator.  This is the numerator-parametric form of
`reciprocal_mul_cancel`; keeping it public avoids rebuilding the synchronized
quotient comparison whenever a finite certificate prepares a ratio through a
different but equivalent denominator presentation. -/
def coherentDiv_mul_cancel (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.div
          numerator denominator apart)
        denominator).name
      numerator.name := by
  let quotient := sampledQuotientApproximation numerator denominator apart
  let numeratorSource :=
    CCL.ProgressiveSampling.approximation numerator.name
  let denominatorSource :=
    CCL.ProgressiveSampling.approximation denominator.name
  let actualQuotient := CCL.ProgressiveCoherence.CoherentNamed.div
    numerator denominator apart
  let sampledQuotient :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation quotient
  let sampledDenominator :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation denominatorSource
  have quotientEquivalent : NamedEquivalent actualQuotient.name
      sampledQuotient.name := by
    simpa only [actualQuotient, sampledQuotient,
      CCL.ProgressiveCoherence.CoherentNamed.div,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      coherentDiv_toSampled numerator denominator apart
  have denominatorEquivalent : NamedEquivalent denominator.name
      sampledDenominator.name := by
    simpa only [sampledDenominator,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      CCL.TranscendentalCoherence.named_toSamplingNamed denominator.name
  have replaceOperands : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        actualQuotient denominator).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        sampledQuotient sampledDenominator).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      actualQuotient sampledQuotient denominator sampledDenominator
      quotientEquivalent denominatorEquivalent
  apply CCL.OperationalEquivalence.NamedEquivalent.trans replaceOperands
  have pointwise : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        sampledQuotient sampledDenominator).name
      numeratorSource.toNamed := by
    simpa only [sampledQuotient, sampledDenominator,
      CCL.ProgressiveCoherence.CoherentNamed.mul,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      CCL.TranscendentalCoherence.mulToNamed_equivalent_pointwise
        quotient denominatorSource numeratorSource (by
          intro index
          rw [sampledQuotientApproximation_sample]
          exact (RFAP.ExplicitField.div_mul_cancel _
            (sampled_nonzero denominator apart index)).symm)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans pointwise
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.TranscendentalCoherence.named_toSamplingNamed numerator.name))

/-- Multiplication by an apart coherent scalar is operationally cancellable.
Only the displayed apartness witness is used; no completed nonzero value or
choice of an inverse is introduced. -/
def coherentMul_cancel_left (scalar left right : CoherentNamed)
    (apart : Apart scalar.name)
    (scaledEquivalent : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul scalar left).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul scalar right).name) :
    NamedEquivalent left.name right.name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let reciprocal := CCL.ProgressiveCoherence.CoherentNamed.div
    one scalar apart
  let inverseProduct := CCL.ProgressiveCoherence.CoherentNamed.mul
    reciprocal scalar
  have inverseLaw : NamedEquivalent inverseProduct.name one.name := by
    simpa only [inverseProduct, reciprocal, one] using
      reciprocal_mul_cancel scalar apart
  have begin : NamedEquivalent left.name
      (CCL.ProgressiveCoherence.CoherentNamed.mul one left).name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalFieldLaws.coherentMul_one_left left)
  have insertInverse : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul one left).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul inverseProduct left).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      one inverseProduct left left
      (CCL.OperationalEquivalence.NamedEquivalent.symm inverseLaw)
      (CCL.OperationalEquivalence.NamedEquivalent.refl left.name)
  have associateLeft : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul inverseProduct left).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal
        (CCL.ProgressiveCoherence.CoherentNamed.mul scalar left)).name := by
    simpa only [inverseProduct,
      CCL.ProgressiveCoherence.CoherentNamed.mul] using
      CCL.TranscendentalCoherence.coherentMul_assoc reciprocal scalar left
  have replaceScaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal
        (CCL.ProgressiveCoherence.CoherentNamed.mul scalar left)).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal
        (CCL.ProgressiveCoherence.CoherentNamed.mul scalar right)).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      reciprocal reciprocal
      (CCL.ProgressiveCoherence.CoherentNamed.mul scalar left)
      (CCL.ProgressiveCoherence.CoherentNamed.mul scalar right)
      (CCL.OperationalEquivalence.NamedEquivalent.refl reciprocal.name)
      scaledEquivalent
  have associateRight : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal
        (CCL.ProgressiveCoherence.CoherentNamed.mul scalar right)).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul inverseProduct right).name := by
    exact CCL.OperationalEquivalence.NamedEquivalent.symm (by
      simpa only [inverseProduct,
        CCL.ProgressiveCoherence.CoherentNamed.mul] using
        CCL.TranscendentalCoherence.coherentMul_assoc reciprocal scalar right)
  have removeInverse : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul inverseProduct right).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul one right).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      inverseProduct one right right inverseLaw
      (CCL.OperationalEquivalence.NamedEquivalent.refl right.name)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans begin
    (CCL.OperationalEquivalence.NamedEquivalent.trans insertInverse
      (CCL.OperationalEquivalence.NamedEquivalent.trans associateLeft
        (CCL.OperationalEquivalence.NamedEquivalent.trans replaceScaled
          (CCL.OperationalEquivalence.NamedEquivalent.trans associateRight
            (CCL.OperationalEquivalence.NamedEquivalent.trans removeInverse
              (CCL.OperationalFieldLaws.coherentMul_one_left right))))))

end CCL.Riemann.OperationalQuotients
