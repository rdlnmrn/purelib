module

public import Purelib.Algebra.Quadratic.Pair.Affine
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Sidecar
public import Purelib.Approximation.Gaussian.Affine.Integral
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Homogeneous
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Data.Gaussian.Cast.Real
import Purelib.LinearAlgebra.Matrix.Inverse.Right
import Purelib.Riemann.Integration.LegendreModularMonodromy
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Integral row preparation at an admitted irrational quadratic input

Every nonzero integer row has nonzero pair coordinates when the input's
generator coordinate is nonzero. The same retained realization then computes
norm-factor observations and finite preparation at the actual row channel.
No imaginary-coordinate separation of the numerical input is required.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Quadratic

open Purelib.Algebra.Quadratic (Pair)
open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Affine
open Purelib.Riemann.Integration.LegendreModularMonodromy
  (fractionalDenominator)
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)
open Purelib.LinearAlgebra.Matrix.Inverse

variable {realization : Realization Rational} {tau : CoherentNamed}

/-- Interpret one exact integer channel as a scalar at the same original admitted realization. -/
private def integerScalar (realization : Realization Rational)
    (coefficients : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (value : Int) : Realization.Sidecar realization (CoherentNamed.Coherence.exact (Cast.integralGaussian value)) :=
  Realization.Sidecar.scalar realization (value : Rational)
    (CoherentNamed.Coherence.exact (Cast.integralGaussian value)) (by
      rewrite [coefficients (value : Rational)]
      exact NamedEquivalent.refl _)

/-- Retain admitted coordinates at the actual original integral affine operation. -/
@[noinline, nospecialize] def affineSidecar (input : Realization.Sidecar realization tau)
    (coefficients : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (constant coefficient : Int) : Realization.Sidecar realization (Integral.affine constant coefficient tau) :=
  let first := integerScalar realization coefficients constant
  let second := integerScalar realization coefficients coefficient
  first.add (second.mul input)

/-- The affine sidecar uses the same original input pair and the actual requested integer coefficients. -/
theorem affineSidecar_value (input : Realization.Sidecar realization tau)
    (coefficients : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (constant coefficient : Int) :
    (affineSidecar input coefficients constant coefficient).value =
      Pair.affine (constant : Rational) (coefficient : Rational) input.value := by
  unfold affineSidecar integerScalar
  dsimp only
  rewrite [Realization.Sidecar.add_value, Realization.Sidecar.mul_value, Realization.Sidecar.scalar_value,
    Realization.Sidecar.scalar_value]
  rfl

set_option genInjectivity false in
/-- One actual integral row with its original input, coordinate cache, norm observations and prepared presentation. -/
structure RowObservation (input : Realization.Sidecar realization tau) (constant coefficient : Int) where
  /-- The complete original input sidecar and its actual cached interpretation. -/
  source : Realization.Sidecar realization tau
  /-- The retained input is the actual original source. -/
  source_eq : source = input
  /-- The actual requested constant coefficient as executable data. -/
  constantValue : Int
  /-- The retained constant is the original request's coefficient. -/
  constant_eq : constantValue = constant
  /-- The actual requested generator coefficient as executable data. -/
  coefficientValue : Int
  /-- The retained generator coefficient is the original request's coefficient. -/
  coefficient_eq : coefficientValue = coefficient
  /-- The actual original row channel with admitted coordinate evidence. -/
  row : Realization.Sidecar realization (Integral.affine constant coefficient tau)
  /-- The row uses the actual requested integers and the same original input coordinates. -/
  value_eq : row.value = Pair.affine (constant : Rational) (coefficient : Rational) input.value
  /-- The actual cached pair channel is nonzero. -/
  nonzero : row.retained.value ≠ 0
  /-- The finite norm-factor observations at that same actual cached row channel. -/
  observation : Prepared.Factor.Observation row.retained.channel
    (realization.denote row.retained.value.conjugate) (realization.coefficient row.retained.value.norm)
  /-- The original row's prepared presentation, reusing those same finite observations. -/
  prepared : Prepared (Integral.affine constant coefficient tau)
  /-- Preparation consumes this exact cached observation and original-channel comparison. -/
  prepared_eq : prepared = observation.prepare.transport (NamedEquivalent.symm row.equivalent)

constructive_injectivity RowObservation

/-- Compute finite preparation for one nonzero integral row at the same original admitted irrational input. -/
@[noinline, nospecialize] def observeRow (input : Realization.Sidecar realization tau)
    (coefficients : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (generator_ne : input.value.im ≠ 0) (constant coefficient : Int)
    (row_ne : constant ≠ 0 ∨ coefficient ≠ 0) : RowObservation input constant coefficient := by
  let row := affineSidecar input coefficients constant coefficient
  have value_eq := affineSidecar_value input coefficients constant coefficient
  have nonzero : row.retained.value ≠ 0 := by
    intro zero
    have actual := row.retained.value_eq.symm.trans zero
    rewrite [value_eq] at actual
    exact Pair.affine_ne_zero_integer input.value generator_ne constant coefficient row_ne actual
  let observation := row.retained.observe nonzero
  let prepared := observation.prepare.transport (NamedEquivalent.symm row.equivalent)
  exact ⟨input, rfl, constant, rfl, coefficient, rfl, row, value_eq, nonzero, observation, prepared, rfl⟩

/-- The exact existing right-inverse certificate type for an original matrix request. -/
@[expose] def InverseData (matrix : IntegralMatrix) : Type := Right.RightInverse matrix

/-- The exact existing denominator-preparation type at the original matrix action. -/
@[expose] def DenominatorData (matrix : IntegralMatrix) (tau : CoherentNamed) : Type 1 :=
  Prepared.DenominatorPreparation (fractionalDenominator matrix tau)

/-- The exact first-row observation type with its original matrix positions. -/
@[expose] def MatrixRow (input : Realization.Sidecar realization tau) (matrix : IntegralMatrix) : Type 1 :=
  RowObservation input (matrix 0 0) (matrix 0 1)

/-- Read the matrix denominator from an already computed observation of its actual first row. -/
@[noinline, nospecialize] def RowObservation.forMatrix {input : Realization.Sidecar realization tau}
    (matrix : IntegralMatrix) (observed : MatrixRow input matrix) : DenominatorData matrix tau :=
  ⟨observed.prepared.denominator, observed.prepared.apart,
    NamedEquivalent.trans (Homogeneous.fractionalRow_affine matrix tau 0) observed.prepared.equivalent⟩

set_option genInjectivity false in
/-- A matrix request with its original inverse, row observations and actual prepared denominator. -/
structure MatrixPreparation (input : Realization.Sidecar realization tau) (matrix : IntegralMatrix)
    (inverse : InverseData matrix) where
  /-- The entire original requested matrix as executable data. -/
  request : IntegralMatrix
  /-- The retained matrix is the actual original request. -/
  request_eq : request = matrix
  /-- The entire original supplied right-inverse certificate. -/
  inverseValue : InverseData matrix
  /-- The retained inverse is the actual supplied request witness. -/
  inverse_eq : inverseValue = inverse
  /-- The actual first-row observation, including its input and both original integer coefficients. -/
  row : MatrixRow input matrix
  /-- The actual original matrix denominator retained as executable data. -/
  channel : CoherentNamed
  /-- The cached denominator is the actual original matrix action. -/
  channel_eq : channel = fractionalDenominator matrix tau
  /-- The actual cached preparation at this same retained denominator channel. -/
  cachedDenominator : Prepared.DenominatorPreparation channel
  /-- Preparation uses the exact presentation already computed by the retained row observation. -/
  prepared_eq : cachedDenominator.prepared = row.prepared.denominator

constructive_injectivity MatrixPreparation

/-- Read the same cached denominator preparation at its original matrix request using the retained channel identity. -/
@[noinline, nospecialize] def MatrixPreparation.denominator {input : Realization.Sidecar realization tau}
    {matrix : IntegralMatrix} {inverse : InverseData matrix} (prepared : MatrixPreparation input matrix inverse) :
    DenominatorData matrix tau := by
  change Prepared.DenominatorPreparation (fractionalDenominator matrix tau)
  exact prepared.channel_eq ▸ prepared.cachedDenominator

/-- Prepare an actual matrix denominator and retain its complete request and original input cache. -/
@[noinline, nospecialize] def prepare (input : Realization.Sidecar realization tau)
    (coefficients : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (generator_ne : input.value.im ≠ 0) (matrix : IntegralMatrix) (inverse : InverseData matrix) :
    MatrixPreparation input matrix inverse :=
  let observed := observeRow input coefficients generator_ne (matrix 0 0) (matrix 0 1)
    (Right.row_nonzero_of_inverse _ _ inverse.identity)
  let channel := fractionalDenominator matrix tau
  let denominator := RowObservation.forMatrix matrix observed
  have prepared_eq : denominator.prepared = observed.prepared.denominator :=
    (Eq.refl _).trans (Eq.refl _)
  ⟨matrix, rfl, inverse, rfl, observed, channel, rfl, denominator, prepared_eq⟩

/-- Supply finite preparation for every requested invertible integral matrix at the same admitted input. -/
@[noinline, nospecialize] def provider (input : Realization.Sidecar realization tau)
    (coefficients : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (generator_ne : input.value.im ≠ 0) : Basic.Provider tau :=
  fun matrix inverse => (prepare input coefficients generator_ne matrix inverse).denominator

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Quadratic

end
