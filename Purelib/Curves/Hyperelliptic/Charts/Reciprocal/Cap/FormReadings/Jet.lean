module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Comparison
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients.Primitive
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Laurent
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Polynomial.Dense.Gaussian

/-! # Finite Laurent comparisons of the actual retained cap-form channel

The original scalar numerator, numerical root preparation and guarded
inverse-root remainder supply the operational expansion. The finite
principal product supplies its actual polar, logarithmic and polynomial
coefficient values before any original observation is compared.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Coefficient

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence.Observation
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence (coherentAdd_respects)
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Algebra.Field

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {parameter : Canonical} {inside : collar.box.Contains (Primitives.point curve parameter)}
  {differential : OddPowerDifferential curve.polynomial} {prepared : Preparation cap parameter inside}

/-- The exact finite polar, logarithmic and regular coefficient of one retained principal product.

The original cap power coordinate and chart degree are retained explicitly.
The supplied reciprocal primitive consumes the same original finite C table.
Its pivot and literal polynomial tail are read in w=parameter^degree: for
degree two the w^-1 pivot is a parameter^-2 polar term, not a logarithmic
parameter term. Actual primitive integration needs that same substitution.
-/
def principalValue {jet : InfinityCoefficients.Jet curve}
    {polynomial : Dense.Basic.DensePolynomial Canonical}
    (retained : jet.Principal polynomial differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus) : Canonical :=
  let point := Primitives.point curve parameter
  (Primitives.degree curve : Canonical) *
    (primitive.derivativeValue point + Coefficient.coefficient retained.val genus * point⁻¹ +
      Evaluation.eval (Arithmetic.divideByPower (genus + 1) retained.val) point)

/-- The supplied finite split reads the actual numerator times its same retained jet value.

The original coordinate is nonzero and the original differential obeys its
reduced numerator bound. Exact padded-polynomial and convolution readbacks
supply the identity in both original chart parities.
-/
theorem principalValue_eq (cached : Coefficient differential prepared) (nonzero : parameter ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) })
    {jet : InfinityCoefficients.Jet curve} (retained : jet.Principal polynomial.val differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus)
    (coefficientCache : { value : Canonical // value = Evaluation.eval jet.val (Primitives.point curve parameter) }) :
    principalValue (parameter := parameter) retained primitive = cached.numerator * coefficientCache.val := by
  have pointNonzero : Primitives.point curve parameter ≠ 0 :=
    ExplicitField.pow_ne_zero_of_ne_zero nonzero _
  rewrite [principalValue, ← retained.nonlogarithmic_split primitive _ pointNonzero,
    cached.numerator_padded nonzero bound polynomial, coefficientCache.property, retained.eval]
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- The original finite principal value splits in the actual cap parameter on both degree parities.

The supplied parameter polynomial and its original reciprocal primitive
retain the same C product. The odd chart substitutes the actual squared
parameter before choosing its nonlogarithmic block and logarithmic pivot.
No pointwise w-pivot is treated as a parameter logarithmic coefficient.
-/
theorem principalValue_parameter_split {jet : InfinityCoefficients.Jet curve}
    {polynomial : Dense.Basic.DensePolynomial Canonical}
    (retained : jet.Principal polynomial differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus)
    (table : { value : CoefficientPolynomial // value = Primitives.parameterPolynomial retained })
    (parameterPrimitive : Antiderivative.ReciprocalPrimitive table.val (Primitives.parameterOrder curve))
    (nonzero : parameter ≠ 0) :
    principalValue (parameter := parameter) retained primitive =
      parameterPrimitive.derivativeValue parameter +
        Coefficient.coefficient table.val (Primitives.parameterOrder curve) * parameter⁻¹ +
          Evaluation.eval (Arithmetic.divideByPower (Primitives.parameterOrder curve + 1) table.val) parameter := by
  have coordinateNonzero : Primitives.point curve parameter ≠ 0 :=
    ExplicitField.pow_ne_zero_of_ne_zero nonzero _
  have power : Primitives.point curve parameter ^ (genus + 1) =
      parameter ^ (Primitives.degree curve * (genus + 1)) := by
    unfold Primitives.point
    exact (pow_mul parameter (Primitives.degree curve) (genus + 1)).symm
  dsimp only [principalValue]
  rewrite [← retained.nonlogarithmic_split primitive _ coordinateNonzero, power]
  have combined : (Primitives.degree curve : Canonical) *
      (Evaluation.eval retained.val (Primitives.point curve parameter) *
        (parameter ^ (Primitives.degree curve * (genus + 1)))⁻¹) =
      ((Primitives.degree curve : Canonical) * Evaluation.eval retained.val (Primitives.point curve parameter)) *
        (parameter ^ (Primitives.degree curve * (genus + 1)))⁻¹ := by ring1
  exact combined.trans (Primitives.parameter_split retained table parameterPrimitive parameter nonzero)

/-- The actual finite Laurent coefficient over the retained origin, plus its original guarded error channel.

The supplied principal and error caches are consumed directly. The exact
chart degree and padded numerator multiply the actual error; no bounded
error is identified with zero or replaced by a new error presentation.
-/
@[expose] def jetChannel {jet : InfinityCoefficients.Jet curve}
    {polynomial : Dense.Basic.DensePolynomial Canonical} (origin : Owners.Point cap 0)
    (retained : jet.Principal polynomial differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus) (error : CoherentNamed) : CoherentNamed :=
  (div (Coherence.exact (principalValue (parameter := parameter) retained primitive))
    origin.certificate.value origin.certificate.apart).add
      ((Coherence.exact ((Primitives.degree curve : Canonical) *
        (-differential.scale * polynomial.eval (Primitives.point curve parameter)))).mul error)

/-- The complete expansion channel retains the supplied principal, origin and error values literally. -/
theorem jetChannel_eq {jet : InfinityCoefficients.Jet curve}
    {polynomial : Dense.Basic.DensePolynomial Canonical} (origin : Owners.Point cap 0)
    (retained : jet.Principal polynomial differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus) (error : CoherentNamed) :
    jetChannel (parameter := parameter) origin retained primitive error =
      (div (Coherence.exact (principalValue (parameter := parameter) retained primitive))
        origin.certificate.value origin.certificate.apart).add
          ((Coherence.exact ((Primitives.degree curve : Canonical) *
            (-differential.scale * polynomial.eval (Primitives.point curve parameter)))).mul error) := by
  unfold jetChannel
  rfl

/-- The original cap-form channel agrees operationally with its retained finite Laurent expansion and actual error.

The supplied regular Point is indexed by the same numerical certificate;
the original inverse-root remainder and its three guarded quotient caches
are consumed without reconstruction. Its principal coefficient is the actual
finite polar/logarithmic/regular split, and its error multiplier retains the
original chart degree, scale and padded numerator.
-/
def jet_equivalent (cached : Coefficient differential prepared) (nonzero : parameter ≠ 0)
    (pairs : differential.denominatorPairs = 0) (bound : differential.numerator.natDegree ≤ 2 * genus)
    (regular : Owners.Point cap (Primitives.point curve parameter))
    (certificateEq : prepared.1.certificate = regular.certificate)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Canonical // value = Evaluation.eval jet.val (Primitives.point curve parameter) })
    (residualCache : { value : Canonical //
      value = Evaluation.eval remainder.val (Primitives.point curve parameter) })
    (factor : Division.Prepared (origin.certificate.value.add
      (prepared.1.certificate.value.mul (Coherence.exact coefficientCache.val))))
    (error : Owners.Point.JetRemainder regular ⟨prepared.1.certificate, certificateEq⟩ origin jet remainder
      coefficientCache residualCache factor)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) })
    (retained : jet.Principal polynomial.val differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus) :
    NamedEquivalent cached.channel.name
      (jetChannel (parameter := parameter) origin retained primitive error.error).name := by
  let point := Primitives.point curve parameter
  let cleared := (Primitives.degree curve : Canonical) * (-differential.scale * polynomial.val.eval point)
  have clearing : cached.numerator * point ^ (genus + 1) = cleared := by
    rewrite [cached.numerator_padded nonzero bound polynomial]
    exact ExplicitField.div_mul_cancel _
      (ExplicitField.pow_ne_zero_of_ne_zero (ExplicitField.pow_ne_zero_of_ne_zero nonzero _) _)
  have expandedEq := Owners.Point.JetRemainder.Result.scale prepared.1.certificate origin
    coefficientCache.val (point ^ (genus + 1)) error.result cached.numerator cleared clearing
  have original := cached.quotient_equivalent pairs cached.numerator (cached.numerator_cleared nonzero)
  change NamedEquivalent
    (div (Coherence.exact cached.numerator) prepared.1.certificate.value prepared.1.certificate.apart).name
    ((div (Coherence.exact (cached.numerator * coefficientCache.val))
      origin.certificate.value origin.certificate.apart).add
        ((Coherence.exact cleared).mul error.error)).name at expandedEq
  have valueEq := principalValue_eq cached nonzero bound polynomial retained primitive coefficientCache
  unfold jetChannel
  exact original.trans (NamedEquivalent.transport rfl
    (congrArg (fun value : Canonical =>
      ((div (Coherence.exact value) origin.certificate.value origin.certificate.apart).add
        ((Coherence.exact cleared).mul error.error)).name) valueEq.symm) expandedEq)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Coefficient

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Reading

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence.Observation
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {parameter : Canonical} {inside : collar.box.Contains (Primitives.point curve parameter)}
  {differential : OddPowerDifferential curve.polynomial} {target : Fraction.Rational}

/-- Pay an actual expanded-form observation and compare it with the supplied original whole-form reading.

The original reading, supplied root certificate, finite principal product
and guarded error remain the same input objects. The original observation
comparison retains the two actual requests, its computed tail indices,
residual and explicit radius/accuracy budget. The expanded request keeps
both whole operand readings from its actual paired process state.
No success comparison or
vanishing remainder is required from the caller.
-/
def jetComparison (reading : Reading differential cap parameter inside target)
    (nonzero : parameter ≠ 0) (pairs : differential.denominatorPairs = 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (regular : Owners.Point cap (Primitives.point curve parameter))
    (certificateEq : reading.1.1.certificate = regular.certificate)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Canonical // value = Evaluation.eval jet.val (Primitives.point curve parameter) })
    (residualCache : { value : Canonical //
      value = Evaluation.eval remainder.val (Primitives.point curve parameter) })
    (factor : Division.Prepared (origin.certificate.value.add
      (reading.1.1.certificate.value.mul (Coherence.exact coefficientCache.val))))
    (error : Owners.Point.JetRemainder regular ⟨reading.1.1.certificate, certificateEq⟩ origin jet remainder
      coefficientCache residualCache factor)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) })
    (retained : jet.Principal polynomial.val differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus)
    (expandedTarget : Fraction.Rational) (expandedPositive : 0 < expandedTarget)
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    (expanded : Request (Coefficient.jetChannel (parameter := parameter)
      origin retained primitive error.error) expandedTarget) ×
      Observation.Reading.SumParts
        (div (Coherence.exact (Coefficient.principalValue (parameter := parameter) retained primitive))
          origin.certificate.value origin.certificate.apart)
        ((Coherence.exact ((Primitives.degree curve : Canonical) *
          (-differential.scale * polynomial.val.eval (Primitives.point curve parameter)))).mul error.error)
        expanded.reading × Comparison reading.request.reading expanded.reading accuracy := by
  let principal := div (Coherence.exact (Coefficient.principalValue (parameter := parameter) retained primitive))
    origin.certificate.value origin.certificate.apart
  let errorValue := (Coherence.exact ((Primitives.degree curve : Canonical) *
    (-differential.scale * polynomial.val.eval (Primitives.point curve parameter)))).mul error.error
  let observed := Request.buildSum principal errorValue expandedTarget expandedPositive
  let expanded := observed.1
  let equivalent := reading.2.1.jet_equivalent nonzero pairs bound regular certificateEq
    origin jet remainder coefficientCache residualCache factor error polynomial retained primitive
  exact ⟨expanded, observed.2, Comparison.build reading.request.reading expanded.reading equivalent accuracy positive⟩

/-- The retained finite expansion caches and actual comparison of one original whole-form reading.

This is an exact dependent-pair view of the original coefficient readings,
Prepared factor, JetRemainder, Request, same-state operand Readings and
Comparison owners. The same original numerical certificate indexes the Point
view; that view is not
stored as a second root channel or selected by another root procedure.
-/
abbrev Jet (reading : Reading differential cap parameter inside target)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) })
    (retained : jet.Principal polynomial.val differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus)
    (expandedTarget accuracy : Fraction.Rational) :=
  let regular := Owners.Point.build cap (Primitives.point curve parameter) inside reading.1.1
  let certificateEq := (Owners.Point.build_certificate cap _ inside reading.1.1).symm
  (coefficientCache : { value : Canonical //
    value = Evaluation.eval jet.val (Primitives.point curve parameter) }) ×
  (residualCache : { value : Canonical //
    value = Evaluation.eval remainder.val (Primitives.point curve parameter) }) ×
  (factor : Division.Prepared (origin.certificate.value.add
    (reading.1.1.certificate.value.mul (Coherence.exact coefficientCache.val)))) ×
  (error : Owners.Point.JetRemainder regular ⟨reading.1.1.certificate, certificateEq⟩ origin jet remainder
    coefficientCache residualCache factor) ×
  (expanded : Request (Coefficient.jetChannel (parameter := parameter)
    origin retained primitive error.error) expandedTarget) ×
  Observation.Reading.SumParts
    (div (Coherence.exact (Coefficient.principalValue (parameter := parameter) retained primitive))
      origin.certificate.value origin.certificate.apart)
    ((Coherence.exact ((Primitives.degree curve : Canonical) *
      (-differential.scale * polynomial.val.eval (Primitives.point curve parameter)))).mul error.error)
    expanded.reading × Comparison reading.request.reading expanded.reading accuracy

/-- Construct the actual finite expansion observation using the supplied original factor-preparation handler.

The jet and residual readings, guarded factor and three-quotient error chain
are each retained once. The Point is only the original indexed view of the
supplied numerical preparation; no fresh preparation is selected. The same
actual error is consumed by the expansion request and observation comparison.
Its two operand readings retain the actual shared refinement state, witness
values and visible radii without running another request.
-/
def jet (reading : Reading differential cap parameter inside target)
    (nonzero : parameter ≠ 0) (pairs : differential.denominatorPairs = 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) })
    (retained : jet.Principal polynomial.val differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus)
    (prepareFactor : (coefficientCache : { value : Canonical //
      value = Evaluation.eval jet.val (Primitives.point curve parameter) }) →
        Division.Prepared (origin.certificate.value.add
          (reading.1.1.certificate.value.mul (Coherence.exact coefficientCache.val))))
    (expandedTarget : Fraction.Rational) (expandedPositive : 0 < expandedTarget)
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy := by
  let regular := Owners.Point.build cap (Primitives.point curve parameter) inside reading.1.1
  have certificateEq : reading.1.1.certificate = regular.certificate :=
    (Owners.Point.build_certificate cap _ inside reading.1.1).symm
  let coefficientCache : { value : Canonical //
      value = Evaluation.eval jet.val (Primitives.point curve parameter) } :=
    ⟨Evaluation.eval jet.val (Primitives.point curve parameter), rfl⟩
  let residualCache : { value : Canonical //
      value = Evaluation.eval remainder.val (Primitives.point curve parameter) } :=
    ⟨Evaluation.eval remainder.val (Primitives.point curve parameter), rfl⟩
  let factor := prepareFactor coefficientCache
  let error := regular.inverseJetRemainder ⟨reading.1.1.certificate, certificateEq⟩
    origin jet remainder coefficientCache residualCache factor
  let compared := reading.jetComparison nonzero pairs bound regular certificateEq origin jet remainder
    coefficientCache residualCache factor error polynomial retained primitive
    expandedTarget expandedPositive accuracy positive
  exact ⟨coefficientCache, residualCache, factor, error, compared.1, compared.2.1, compared.2.2⟩

namespace Jet

variable {reading : Reading differential cap parameter inside target}
  {origin : Owners.Point cap 0} {jet : InfinityCoefficients.Jet curve}
  {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
  {polynomial : { value : Dense.Basic.DensePolynomial Canonical //
    value = Reciprocal.padded differential.numerator (2 * genus) }}
  {retained : jet.Principal polynomial.val differential.scale}
  {primitive : Antiderivative.ReciprocalPrimitive retained.val genus}
  {expandedTarget accuracy : Fraction.Rational}

/-- Read the actual retained inverse-root remainder and its complete original quotient caches. -/
abbrev error (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy) :=
  stored.2.2.2.1

/-- Read the actual request of the finite expansion using that same retained error channel. -/
abbrev request (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy) :=
  stored.2.2.2.2.1

/-- Read both actual operand readings retained from the same expanded sum state. -/
abbrev parts (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy) :=
  stored.2.2.2.2.2.1

/-- Read the actual original observation comparison without rerunning its finite procedure. -/
abbrev comparison (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy) :=
  stored.2.2.2.2.2.2

/-- The comparison retains the same actual original requested reading value. -/
theorem source_value (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy) :
    stored.comparison.leftObservation.value = reading.request.reading.value :=
  congrArg (fun value : Observation.Reading reading.2.1.channel => value.value)
    stored.comparison.leftObservation_eq

/-- The comparison retains the same actual finite expansion requested reading value. -/
theorem target_value (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy) :
    stored.comparison.rightObservation.value = stored.request.reading.value :=
  congrArg (fun value : Observation.Reading
    (Coefficient.jetChannel (parameter := parameter) origin retained primitive stored.error.error) => value.value)
    stored.comparison.rightObservation_eq

/-- The actual saved expansion value is the sum of its two retained operand values. -/
theorem value_split (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy) :
    stored.request.reading.value = stored.parts.val.1.value + stored.parts.val.2.value :=
  stored.parts.property.2.2

/-- A finite comparison of the actual retained root error bounds its same-state multiplied error reading.

The original sum request pays this operand's own semantic allowance. The
same actual bounded root-error comparison is multiplied by the original
exact chart degree, scale and padded numerator; an exact-zero reading
needs no further process refinement. A bounded error is not set to zero.
-/
theorem error_normSq_le
    (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (positive : 0 < expandedTarget) (upper : Fraction.Rational)
    (comparison : Equivalence.Comparison
      (Name.Sampling.approximation stored.error.error.name)
      (Name.Sampling.approximation (Coherence.exact 0).name) 0 0 (upper + expandedTarget)) :
    Norm.Basic.normSq stored.parts.val.2.value ≤
      64 * expandedTarget + 4 *
        (4 * (Norm.Basic.normSq ((Primitives.degree curve : Canonical) *
          (-differential.scale * polynomial.val.eval (Primitives.point curve parameter))) *
            (upper + expandedTarget)) + expandedTarget) :=
  Observation.Reading.mul_zero_normSq_le
    ((Primitives.degree curve : Canonical) *
      (-differential.scale * polynomial.val.eval (Primitives.point curve parameter)))
    stored.error.error stored.parts.val.2 positive
    (Observation.Reading.SumParts.right_allowance_lt stored.parts) upper comparison

/-- The actual saved principal reading compares with its scalar times one supplied original reciprocal reading.

The original sum's semantic payment applies to the literal saved principal
operand. Its denominator and guard are unchanged, and the other endpoint
uses the same supplied whole reciprocal reading without a new request.
-/
theorem principal_distance_le
    (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (reciprocal : Observation.Reading
      (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart))
    {productTarget comparisonTarget : Fraction.Rational} (positive : 0 < expandedTarget)
    (productPositive : 0 < productTarget) (comparisonPositive : 0 < comparisonTarget)
    (productPaid : ((Coherence.exact (Coefficient.principalValue (parameter := parameter) retained primitive)).mul
      (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)).coherent.allowance
        (reciprocal.exact_mul (Coefficient.principalValue (parameter := parameter) retained primitive)).state <
          productTarget) :
    Norm.Basic.normSq (stored.parts.val.1.value -
      Coefficient.principalValue (parameter := parameter) retained primitive * reciprocal.value) ≤
        32 * (expandedTarget + productTarget) + 4 * comparisonTarget :=
  Observation.Reading.exact_div_distance_le
    (Coefficient.principalValue (parameter := parameter) retained primitive)
    origin.certificate.value origin.certificate.apart stored.parts.val.1 reciprocal
    positive productPositive comparisonPositive
    (Observation.Reading.SumParts.left_allowance_lt stored.parts) productPaid

/-- The actual original and expanded readings satisfy their separately paid visible-radius and accuracy budget.

Both readings are the original finite requests stored by the comparison.
The comparison's actual residual and bound readbacks preserve the displayed
sixteenfold radius sum and fourfold operational target.
-/
theorem distance_le (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy) :
    Data.Gaussian.Norm.Basic.normSq (reading.request.reading.value - stored.request.reading.value) ≤
      16 * (target + expandedTarget) + 4 * accuracy := by
  exact (Comparison.requested_error_lt reading.request stored.request stored.comparison).le
/-- The same actual cached observation values obey the separately paid request and comparison budget. -/
theorem observations_distance_le
    (stored : Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy) :
    Data.Gaussian.Norm.Basic.normSq
      (stored.comparison.leftObservation.value - stored.comparison.rightObservation.value) ≤
        16 * (target + expandedTarget) + 4 * accuracy := by
  exact Comparison.observations_distance_le reading.request stored.request stored.comparison

end Jet

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Reading

end
