module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
public import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Division
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Coherence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Name.Coherent.Division

open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication

open Purelib.Approximation.Gaussian.Sequence.Name

section
@[expose] public section

/-!
# Riemann compatibility facade for operational quotient congruence

The general finite quotient construction and congruence theorem now live in
`Purelib.CCL.Progressive.DivisionCongruence`, below the Riemann layer. This module
retains the established Riemann names and the scalar-cancellation consequences
which use the broader operational field-law library.
-/

namespace Purelib.Approximation.Gaussian.Name.Apart.Sampling
end Purelib.Approximation.Gaussian.Name.Apart.Sampling

namespace Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample
end Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample

namespace Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence
end Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence

namespace Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
end Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence

namespace Purelib.Approximation.Gaussian.Division.Cancellation

export Purelib.Approximation.Gaussian.Name.Apart.Sampling
  (sampled_lower sampled_nonzero)

export Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample
  (sampledQuotientErrorScale sampledQuotientErrorScale_nonnegative sampledQuotientApproximation
    sampledQuotientApproximation_sample)

export Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence
  (commonLower commonLower_positive quotientComparisonCoefficient quotientComparisonCoefficient_nonnegative
    quotientComparisonTarget quotientComparisonTarget_positive quotientComparisonTarget_budget_lt
    sampledQuotientApproximation_respects)

export Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
  (coherentQuotientBridgeCoefficient coherentQuotientBridgeCoefficient_positive coherentQuotientBridgeTarget
    coherentQuotientBridgeTarget_positive coherentQuotientBridgeTarget_budget_lt coherentDiv_toSampled
    coherentDiv_respects)

/-- The actual apartness-certified reciprocal is a left operational inverse. The proof normalizes the quotient and
product to equal-index finite Gaussian samples and applies exact rational cancellation at each displayed index. -/
def reciprocal_mul_cancel (denominator :
  Coherent.CoherentNamed)
    (apart : Named.Apart denominator.name) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        (CoherentNamed.div
          (Coherence.exact 1)
          denominator apart)
        denominator).name
      (Coherence.exact 1).name := by
  let one := Coherence.exact 1
  let reciprocal := CoherentNamed.div
    one denominator apart
  let quotient := Sample.sampledQuotientApproximation one denominator apart
  let denominatorSource :=
    Sampling.approximation denominator.name
  let sampledReciprocal :=
    CoherentNamed.ofApproximation quotient
  let sampledDenominator :=
    CoherentNamed.ofApproximation denominatorSource
  have reciprocalEquivalent : Gaussian.Equivalence.NamedEquivalent reciprocal.name
      sampledReciprocal.name := by
    simpa only [reciprocal, one, sampledReciprocal,
      CoherentNamed.div,
      CoherentNamed.ofApproximation] using
      Equivalence.coherentDiv_toSampled one denominator apart
  have denominatorEquivalent : Gaussian.Equivalence.NamedEquivalent denominator.name
      sampledDenominator.name := by
    simpa only [sampledDenominator,
      CoherentNamed.ofApproximation] using
      Equivalence.named_toSamplingNamed denominator.name
  have replaceOperands : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        reciprocal denominator).name
      (CoherentNamed.mul
        sampledReciprocal sampledDenominator).name :=
    Congruence.coherentMul_respects
      reciprocal sampledReciprocal denominator sampledDenominator
      reciprocalEquivalent denominatorEquivalent
  apply NamedEquivalent.trans replaceOperands
  have pointwise : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        sampledReciprocal sampledDenominator).name
      (Sampling.approximation one.name).toNamed := by
    simpa only [sampledReciprocal, sampledDenominator,
      CoherentNamed.mul,
      CoherentNamed.ofApproximation] using
      Bridge.mulToNamed_equivalent_pointwise
        quotient denominatorSource
        (Sampling.approximation one.name) (by
          intro index
          rw [Sample.sampledQuotientApproximation_sample]
          exact (Algebra.Field.ExplicitField.div_mul_cancel _
            (Name.Apart.Sampling.sampled_nonzero denominator apart index)).symm)
  exact NamedEquivalent.trans pointwise
    (NamedEquivalent.symm
      (Equivalence.named_toSamplingNamed one.name))

/-- An apartness-certified operational quotient cancels when multiplied on the right by its exact denominator. This is
the numerator-parametric form of `reciprocal_mul_cancel`; keeping it public avoids rebuilding the synchronized quotient
comparison whenever a finite certificate prepares a ratio through a different but equivalent denominator presentation.
-/
def coherentDiv_mul_cancel (numerator denominator :
  Coherent.CoherentNamed)
    (apart : Named.Apart denominator.name) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        (CoherentNamed.div
          numerator denominator apart)
        denominator).name
      numerator.name := by
  let quotient := Sample.sampledQuotientApproximation numerator denominator apart
  let numeratorSource :=
    Sampling.approximation numerator.name
  let denominatorSource :=
    Sampling.approximation denominator.name
  let actualQuotient := CoherentNamed.div
    numerator denominator apart
  let sampledQuotient :=
    CoherentNamed.ofApproximation quotient
  let sampledDenominator :=
    CoherentNamed.ofApproximation denominatorSource
  have quotientEquivalent : Gaussian.Equivalence.NamedEquivalent actualQuotient.name
      sampledQuotient.name := by
    simpa only [actualQuotient, sampledQuotient,
      CoherentNamed.div,
      CoherentNamed.ofApproximation] using
      Equivalence.coherentDiv_toSampled numerator denominator apart
  have denominatorEquivalent : Gaussian.Equivalence.NamedEquivalent denominator.name
      sampledDenominator.name := by
    simpa only [sampledDenominator,
      CoherentNamed.ofApproximation] using
      Equivalence.named_toSamplingNamed denominator.name
  have replaceOperands : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        actualQuotient denominator).name
      (CoherentNamed.mul
        sampledQuotient sampledDenominator).name :=
    Congruence.coherentMul_respects
      actualQuotient sampledQuotient denominator sampledDenominator
      quotientEquivalent denominatorEquivalent
  apply NamedEquivalent.trans replaceOperands
  have pointwise : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        sampledQuotient sampledDenominator).name
      numeratorSource.toNamed := by
    simpa only [sampledQuotient, sampledDenominator,
      CoherentNamed.mul,
      CoherentNamed.ofApproximation] using
      Bridge.mulToNamed_equivalent_pointwise
        quotient denominatorSource numeratorSource (by
          intro index
          rw [Sample.sampledQuotientApproximation_sample]
          exact (Algebra.Field.ExplicitField.div_mul_cancel _
            (Name.Apart.Sampling.sampled_nonzero denominator apart index)).symm)
  exact NamedEquivalent.trans pointwise
    (NamedEquivalent.symm
      (Equivalence.named_toSamplingNamed numerator.name))

/-- Multiplication by an apart coherent scalar is operationally cancellable. Only the displayed apartness witness is
used; no completed nonzero value or choice of an inverse is introduced. -/
def coherentMul_cancel_left (scalar left right :
  Coherent.CoherentNamed)
    (apart : Named.Apart scalar.name)
    (scaledEquivalent : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul scalar left).name
      (CoherentNamed.mul scalar right).name) :
    Gaussian.Equivalence.NamedEquivalent left.name right.name := by
  let one := Coherence.exact 1
  let reciprocal := CoherentNamed.div
    one scalar apart
  let inverseProduct := CoherentNamed.mul
    reciprocal scalar
  have inverseLaw : Gaussian.Equivalence.NamedEquivalent inverseProduct.name one.name := by
    simpa only [inverseProduct, reciprocal, one] using
      reciprocal_mul_cancel scalar apart
  have begin : Gaussian.Equivalence.NamedEquivalent left.name
      (CoherentNamed.mul one left).name :=
    NamedEquivalent.symm
      (Mul.coherentMul_one_left left)
  have insertInverse : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul one left).name
      (CoherentNamed.mul inverseProduct left).name :=
    Congruence.coherentMul_respects
      one inverseProduct left left
      (NamedEquivalent.symm inverseLaw)
      (NamedEquivalent.refl left.name)
  have associateLeft : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul inverseProduct left).name
      (CoherentNamed.mul reciprocal
        (CoherentNamed.mul scalar left)).name := by
    simpa only [inverseProduct,
      CoherentNamed.mul] using
      Laws.coherentMul_assoc reciprocal scalar left
  have replaceScaled : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul reciprocal
        (CoherentNamed.mul scalar left)).name
      (CoherentNamed.mul reciprocal
        (CoherentNamed.mul scalar right)).name :=
    Congruence.coherentMul_respects
      reciprocal reciprocal
      (CoherentNamed.mul scalar left)
      (CoherentNamed.mul scalar right)
      (NamedEquivalent.refl reciprocal.name)
      scaledEquivalent
  have associateRight : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul reciprocal
        (CoherentNamed.mul scalar right)).name
      (CoherentNamed.mul inverseProduct right).name := by
    exact NamedEquivalent.symm (by
      simpa only [inverseProduct,
        CoherentNamed.mul] using
        Laws.coherentMul_assoc reciprocal scalar right)
  have removeInverse : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul inverseProduct right).name
      (CoherentNamed.mul one right).name :=
    Congruence.coherentMul_respects
      inverseProduct one right right inverseLaw
      (NamedEquivalent.refl right.name)
  exact NamedEquivalent.trans begin
    (NamedEquivalent.trans insertInverse
      (NamedEquivalent.trans associateLeft
        (NamedEquivalent.trans replaceScaled
          (NamedEquivalent.trans associateRight
            (NamedEquivalent.trans removeInverse
              (Mul.coherentMul_one_left right))))))

end Purelib.Approximation.Gaussian.Division.Cancellation

end
