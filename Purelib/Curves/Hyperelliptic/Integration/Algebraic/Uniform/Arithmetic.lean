module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Interpretation
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Comparison
import Purelib.Approximation.Gaussian.Enclosure.Ball.Distance
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Tactic.Ring

/-! # Actual arithmetic readings attached to original uniform polynomial queries

The old numerical reading and the actual uniform query reading keep their
own states and witnesses. Their two original sheet generators are compared
operationally; the existing generic observation comparison retains the actual
selected sample pair. The uniform candidate estimate then controls the
original polynomial at its same retained input, without resampling the query.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
  (Reading RootObservation radiusRequest comparisonRequest)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential curve.polynomial}
    {start finish : LiftedPoint 2} {lifted : LiftedCell start finish} {cell : CellModel} {time : Fraction.Rational}
    (uniform : UniformObservation curve differential lifted cell time)

/-- View the exact original uniform query reading/state as a retained observation of its actual coefficient channel. -/
@[expose] def asReading : Equivalence.Observation.Reading uniform.algebraic.interpretation.channel :=
  Equivalence.Observation.Reading.retain uniform.algebraic.interpretation.channel uniform.algebraic.readingState
    uniform.observation.integrandReading uniform.algebraic.readingPossible

/-- The observation view retains the SAME displayed integrand reading of the original uniform query. -/
theorem asReading_value : uniform.asReading.value = uniform.observation.integrandReading := by rfl

variable {point : Canonical} {sheet : CoherentNamed} {apart : Named.Apart sheet.name}
    {state : sheet.name.process.State} {rootObservation : RootObservation}
    {accuracy : Approximation.AccuracyRequest}
    (numeric : Reading differential point sheet apart state rootObservation accuracy)
    (identity : PowerIdentity sheet 2 (curve.polynomial.eval point))
    (samePoint : point = uniform.algebraic.point)
    (roots : NamedEquivalent sheet.name uniform.algebraic.sheetValue.value.name)

/-- One cached numeric denotation and the actual comparison to the SAME original uniform observation.

The exact source and query generators, both observations and their original
states remain indices. The cached interpretation consumes the supplied
original square identity. Physical point equality and signed operational
root agreement identify the coefficient channels; no Taylor bound is input.
-/
@[expose] def ArithmeticComparison :=
  (_interpreted : { value : Expression.Denotation differential.coefficient point sheet //
    value = differential.interpret point sheet identity apart }) ×
  Equivalence.Observation.Comparison numeric.asObservation uniform.asReading (comparisonRequest accuracy).tolerance

namespace ArithmeticComparison

open Purelib.Data.Rat.Fraction.Order

variable {uniform numeric identity samePoint roots}

/-- Compare the unchanged actual numeric/query readings using their original square and signed root certificates. -/
def build (query : UniformObservation curve differential lifted cell time)
    (reading : Reading differential point sheet apart state rootObservation accuracy)
    (power : PowerIdentity sheet 2 (curve.polynomial.eval point))
    (point_eq : point = query.algebraic.point)
    (signed_eq : NamedEquivalent sheet.name query.algebraic.sheetValue.value.name) :
    ArithmeticComparison query reading power := by
  clear roots samePoint identity numeric uniform
  let interpreted := differential.interpret point sheet power apart
  have equivalent : NamedEquivalent reading.coefficient.name query.algebraic.interpretation.channel.name := by
    cases point_eq
    exact (reading.equivalent_denotation interpreted).trans
      (interpreted.equivalent query.algebraic.interpretation signed_eq)
  let comparison := Equivalence.Observation.Comparison.build reading.asObservation query.asReading equivalent
    (comparisonRequest accuracy).tolerance (comparisonRequest accuracy).positive
  exact ⟨⟨interpreted, rfl⟩, comparison⟩

variable (retained : ArithmeticComparison uniform numeric identity)

/-- Read the SAME cached denotation of the original numerical evaluator and its original square identity. -/
@[expose] def interpreted := retained.1.val

/-- Read the existing generic comparison retaining both old observations and its actual selected tail samples. -/
@[expose] def comparison := retained.2

include retained in
/-- The actual numerical reading and original polynomial query obey an explicit paid finite estimate.

The original numerical state radius pays its displayed witness, the actual
comparison target pays its two selected samples, and the uniform candidate
estimate pays the original polynomial. The uniform query is not resampled.
-/
theorem polynomial_error_le :
    Norm.Basic.normSq (numeric.reading - Evaluation.eval cell.polynomial ⟨time, 0⟩) ≤
      16 * numeric.asObservation.radius + 4 * (comparisonRequest accuracy).tolerance + 2 * cell.localAllowance := by
  let comparison := retained.comparison
  have firstInside := numeric.coefficient.name.process.possible_inside numeric.reading_possible
  have sampleInside := numeric.coefficient.name.process.possible_inside comparison.leftSample_possible
  have firstBound := Enclosure.Ball.Distance.normSq_sub_le_four_radiusSq firstInside sampleInside
  change Norm.Basic.normSq (numeric.reading - comparison.leftSample) ≤ 4 * numeric.asObservation.radius at firstBound
  have lastBound := uniform.candidate_error_le comparison.rightSample_possible
  have inner := (Norm.Bounds.normSq_sub_le_via numeric.reading comparison.leftSample comparison.rightSample).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct firstBound comparison.sample_distance_lt.le)
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2))
  have total := (Norm.Bounds.normSq_sub_le_via numeric.reading comparison.rightSample
    (Evaluation.eval cell.polynomial ⟨time, 0⟩)).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct inner lastBound)
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2))
  exact total.trans_eq (by ring1)

/-- The exact sixteenth arithmetic radius and eighth comparison request pay the factor seven halves. -/
private theorem request_budget (accuracy : Approximation.AccuracyRequest) :
    16 * (radiusRequest accuracy).tolerance + 4 * (comparisonRequest accuracy).tolerance +
        2 * accuracy.tolerance = (7 / 2 : Fraction.Rational) * accuracy.tolerance := by
  change 16 * (accuracy.tolerance / 16) + 4 * (accuracy.tolerance / 8) + 2 * accuracy.tolerance = _
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  calc
    _ = accuracy.tolerance * (16 * (16 : Fraction.Rational)⁻¹ + 4 * 8⁻¹ + 2) := by ring1
    _ = accuracy.tolerance * (7 / 2 : Fraction.Rational) :=
      congrArg (fun scalar : Fraction.Rational => accuracy.tolerance * scalar) (by decide +kernel)
    _ = _ := Fraction.Field.mul_comm _ _

include retained in
/-- The actual new arithmetic witness and original polynomial query pay one common independently verified allowance.

The model's allowance payment is a spatial request condition on the SAME
cell. The numerical witness has its own original sixteenth-radius payment;
the comparison's actual selected samples pay its eighth request internally.
No old radius or replaced uniform reading occurs in this estimate.
-/
theorem polynomial_error_le_tolerance (allowancePaid : cell.localAllowance ≤ accuracy.tolerance) :
    Norm.Basic.normSq (numeric.reading - Evaluation.eval cell.polynomial ⟨time, 0⟩) ≤
      (7 / 2 : Fraction.Rational) * accuracy.tolerance := by
  have paid := Arithmetic.add_le_add_direct
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct numeric.asObservation_radius_lt.le
        (by decide +kernel : (0 : Fraction.Rational) ≤ 16))
      (Fraction.Order.Basic.le_refl (4 * (comparisonRequest accuracy).tolerance)))
    (Arithmetic.mul_le_mul_of_nonneg_left_direct allowancePaid
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2))
  exact (retained.polynomial_error_le.trans paid).trans_eq (request_budget accuracy)

include retained in
/-- The same independently paid query discrepancy also fits a parameter-fourth request on the actual increment. -/
theorem polynomial_error_le_fourth (increment : Canonical)
    (allowancePaid : cell.localAllowance ≤ accuracy.tolerance)
    (parameterPaid : accuracy.tolerance ≤ Norm.Basic.normSq increment ^ 2) :
    Norm.Basic.normSq (numeric.reading - Evaluation.eval cell.polynomial ⟨time, 0⟩) ≤
      (7 / 2 : Fraction.Rational) * Norm.Basic.normSq increment ^ 2 :=
  (retained.polynomial_error_le_tolerance allowancePaid).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct parameterPaid
      (by decide +kernel : (0 : Fraction.Rational) ≤ 7 / 2))

end ArithmeticComparison

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation

end
