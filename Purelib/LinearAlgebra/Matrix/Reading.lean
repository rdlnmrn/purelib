module

public import Purelib.Algebra.Ring.GaussianReading.FiniteSum
public import Purelib.LinearAlgebra.Matrix.Rectangular
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Weight
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paid readings of original finite matrix actions

Original matrices and vectors remain indices. Certified source-weight caches
prepare rational discrepancy coefficients before observations. Actual additive
Gaussian readings then pay both original product errors and any displayed
input-vector model error, without exact multiplicativity or weight rescanning.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Reading

open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order

variable {K : Type*} [CommRing K] {rows columns : Nat}

/-- A retained rectangular rational table bounds the weights of the same original matrix entries. -/
abbrev MatrixBounds (weight : Weight K) (matrix : Rectangular K rows columns)
    (bounds : Rectangular Rational rows columns) := ∀ row column, weight.value (matrix row column) ≤ bounds row column

/-- A retained rational vector bounds the weights of the same original vector entries. -/
abbrev VectorBounds (weight : Weight K) (values : Vec K columns) (bounds : Vec Rational columns) :=
  ∀ column, weight.value (values column) ≤ bounds column

/-- Certified source-weight bounds pay the same actual original product discrepancy. -/
private theorem product_error_le {weight : Weight K} {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (left right : K) (leftWeight rightWeight : Rational)
    (leftBound : weight.value left ≤ leftWeight) (rightBound : weight.value right ≤ rightWeight) :
    Norm.Basic.normSq (reading.read (left * right) - reading.read left * reading.read right) ≤
      reading.error * (leftWeight * rightWeight) := by
  have products := Arithmetic.mul_le_mul_direct leftBound rightBound (weight.nonnegative right)
    ((weight.nonnegative left).trans leftBound)
  exact (reading.productBound left right).trans ((by
    have bounded := Arithmetic.mul_le_mul_of_nonneg_left_direct products reading.errorNonnegative
    exact (show reading.error * weight.value left * weight.value right =
      reading.error * (weight.value left * weight.value right) by ring1).trans_le bounded) :
        reading.error * weight.value left * weight.value right ≤ reading.error * (leftWeight * rightWeight))

set_option genInjectivity false in
/-- The original matrix and input vector retain source-weight bounds and cached finite product-error coefficients.

The supplied bounds certify original source payloads and contain no reading.
The same cache computes one coefficient per original output row. No source
weight, matrix product or input vector is reconstructed by the constructor.
-/
structure Application (weight : Weight K) (matrix : Rectangular K rows columns) (values : Vec K columns) where
  /-- The retained original matrix-entry weight bounds. -/
  matrixWeights : Rectangular Rational rows columns
  /-- The same original matrix entries obey those stored source bounds. -/
  matrixBound : MatrixBounds weight matrix matrixWeights
  /-- The retained original input-entry weight bounds. -/
  valueWeights : Vec Rational columns
  /-- The same original input entries obey those stored source bounds. -/
  valuesBound : VectorBounds weight values valueWeights
  /-- The once-computed finite squared-triangle factor. -/
  factor : Rational
  /-- The factor retains the original input dimension. -/
  factor_eq : factor = (2 : Rational) ^ columns
  /-- The materialized original row-product discrepancy coefficients. -/
  coefficients : Vec Rational rows
  /-- Every coefficient uses the same already retained source-weight tables. -/
  coefficients_eq : ∀ row, coefficients row = factor *
    sumFin (fun column => matrixWeights row column * valueWeights column)

constructive_injectivity Application

namespace Application

/-- Compute the original row-error coefficients from supplied certified source caches, without another weight scan. -/
@[expose] def prepare (weight : Weight K) (matrix : Rectangular K rows columns) (values : Vec K columns)
    (matrixWeights : Rectangular Rational rows columns) (matrixBound : MatrixBounds weight matrix matrixWeights)
    (valueWeights : Vec Rational columns) (valuesBound : VectorBounds weight values valueWeights) :
    Application weight matrix values :=
  let factor := (2 : Rational) ^ columns
  let coefficients := vectorOfFn (fun row => factor *
    sumFin (fun column => matrixWeights row column * valueWeights column))
  { matrixWeights, matrixBound, valueWeights, valuesBound, factor, factor_eq := rfl
    coefficients, coefficients_eq := fun row => vectorOfFn_apply _ row }

variable {weight : Weight K} {matrix : Rectangular K rows columns} {values : Vec K columns}

/-- The complete retained application restores its original constructor on the same source-weight caches. -/
theorem restore (retained : Application weight matrix values) :
    retained = prepare weight matrix values retained.matrixWeights retained.matrixBound
      retained.valueWeights retained.valuesBound := by
  cases retained with
  | mk matrixWeights matrixBound valueWeights valuesBound factor factorEq coefficients coefficientsEq =>
      cases factorEq
      have same : coefficients = vectorOfFn (fun row => (2 : Rational) ^ columns *
          sumFin (fun column => matrixWeights row column * valueWeights column)) := by
        apply vector_ext
        intro row
        exact (coefficientsEq row).trans (vectorOfFn_apply (fun row : Fin rows => (2 : Rational) ^ columns *
          sumFin (fun column => matrixWeights row column * valueWeights column)) row).symm
      cases same
      rfl

/-- Each original cached matrix-entry bound is nonnegative. -/
theorem matrixWeight_nonnegative (retained : Application weight matrix values) (row : Fin rows) (column : Fin columns) :
    0 ≤ retained.matrixWeights row column := (weight.nonnegative _).trans (retained.matrixBound row column)

/-- Each original cached input-entry bound is nonnegative. -/
theorem valueWeight_nonnegative (retained : Application weight matrix values) (column : Fin columns) :
    0 ≤ retained.valueWeights column := (weight.nonnegative _).trans (retained.valuesBound column)

/-- The same original finite sum factor is positive, including zero input dimension. -/
theorem factor_positive (retained : Application weight matrix values) : 0 < retained.factor := by
  rewrite [retained.factor_eq]
  exact Arithmetic.pow_pos_direct (by decide) _

/-- Every stored original row discrepancy coefficient is nonnegative. -/
theorem coefficient_nonnegative (retained : Application weight matrix values) (row : Fin rows) :
    0 ≤ retained.coefficients row := by
  rewrite [retained.coefficients_eq]
  exact Arithmetic.mul_nonneg_direct retained.factor_positive.le (weight_sum_nonnegative _ fun column =>
    Arithmetic.mul_nonneg_direct (retained.matrixWeight_nonnegative row column)
      (retained.valueWeight_nonnegative column))

/-- The same retained product coefficient bounds the original output weight with its original multiplier. -/
theorem weight_bound (retained : Application weight matrix values) (row : Fin rows) :
    weight.value (Rectangular.apply matrix values row) ≤ weight.multiplier * retained.coefficients row := by
  rewrite [Rectangular.apply_at]
  have entries (column : Fin columns) : weight.value (matrix row column * values column) ≤
      weight.multiplier * (retained.matrixWeights row column * retained.valueWeights column) := by
    have products := Arithmetic.mul_le_mul_direct (retained.matrixBound row column) (retained.valuesBound column)
      (weight.nonnegative _) (retained.matrixWeight_nonnegative row column)
    have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct products weight.multiplier_nonnegative
    exact (weight.mul_le _ _).trans ((by
      exact (show weight.multiplier * weight.value (matrix row column) * weight.value (values column) =
        weight.multiplier * (weight.value (matrix row column) * weight.value (values column)) by ring1).trans_le
          scaled) : _)
  have bounded := (weight.sum_le (fun column => matrix row column * values column)).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (IndexedBudget.sumFin_le entries)
      (Arithmetic.pow_nonneg_direct (by decide : (0 : Rational) ≤ 2) columns))
  rewrite [sumFin_mul_left] at bounded
  exact bounded.trans_eq (by rewrite [retained.coefficients_eq, retained.factor_eq]; ring1)

/-- The original output-vector total consumes the same already retained row-product coefficients. -/
theorem weight_total_bound (retained : Application weight matrix values) :
    sumFin (fun row => weight.value (Rectangular.apply matrix values row)) ≤
      weight.multiplier * sumFin (fun row => retained.coefficients row) :=
  (IndexedBudget.sumFin_le retained.weight_bound).trans_eq (sumFin_mul_left _ _)

/-- The reading of the actual original matrix action pays its retained row coefficient. -/
theorem bound (retained : Application weight matrix values) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (row : Fin rows) :
    Norm.Basic.normSq (reading.read (Rectangular.apply matrix values row) -
      sumFin (fun column => reading.read (matrix row column) * reading.read (values column))) ≤
        reading.error * retained.coefficients row := by
  rewrite [Rectangular.apply_at]
  exact (reading.sum_discrepancy_bound _ _
    (fun column => retained.matrixWeights row column * retained.valueWeights column)
    (fun column => product_error_le reading _ _ _ _ (retained.matrixBound row column)
      (retained.valuesBound column))).trans_eq (by
        rewrite [retained.coefficients_eq, retained.factor_eq]
        rfl)

/-- Cached Gaussian entry readbacks retain the same bound for the actual displayed matrix-vector product. -/
theorem bound_of_readback (retained : Application weight matrix values) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (observedMatrix : Rectangular Canonical rows columns)
    (matrixEq : ∀ row column, observedMatrix row column = reading.read (matrix row column))
    (observedValues : Vec Canonical columns) (valuesEq : ∀ column, observedValues column = reading.read (values column))
    (row : Fin rows) :
    Norm.Basic.normSq (reading.read (Rectangular.apply matrix values row) -
      Rectangular.apply observedMatrix observedValues row) ≤ reading.error * retained.coefficients row := by
  have same : Rectangular.apply observedMatrix observedValues row =
      sumFin (fun column => reading.read (matrix row column) * reading.read (values column)) := by
    rewrite [Rectangular.apply_at]
    exact sumFin_congr fun column => by rewrite [matrixEq, valuesEq]; rfl
  rewrite [same]
  exact retained.bound reading row

/-- Materialize output-comparison coefficients from the same cached original product errors and target errors. -/
@[expose] def outputCoefficients (retained : Application weight matrix values) (errors : Vec Rational rows) :
    Vec Rational rows := vectorOfFn fun row => 2 * (retained.coefficients row + errors row)

/-- Each same cached output-comparison coefficient consumes its original row errors. -/
theorem outputCoefficients_at (retained : Application weight matrix values) (errors : Vec Rational rows)
    (row : Fin rows) : retained.outputCoefficients errors row = 2 * (retained.coefficients row + errors row) :=
  vectorOfFn_apply _ row

/-- Nonnegative target errors give nonnegative cached output-comparison coefficients. -/
theorem outputCoefficient_nonnegative (retained : Application weight matrix values) (errors : Vec Rational rows)
    (nonnegative : ∀ row, 0 ≤ errors row) (row : Fin rows) : 0 ≤ retained.outputCoefficients errors row := by
  rewrite [retained.outputCoefficients_at]
  exact Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2)
    (Arithmetic.add_le_add_direct (retained.coefficient_nonnegative row) (nonnegative row))

/-- The Gaussian product of original readbacks pays both its product error and an actual output-model error.

The output-model premise can follow from a separate exact formal identity.
That identity and the numerical discrepancy remain distinct; no nonzero
formal coefficient is presumed to have a nonzero physical reading.
-/
theorem output_bound (retained : Application weight matrix values) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (model : Vec Canonical rows) (errors : Vec Rational rows)
    (paid : ∀ row, Norm.Basic.normSq (reading.read (Rectangular.apply matrix values row) - model row) ≤
      reading.error * errors row) (row : Fin rows) :
    Norm.Basic.normSq (sumFin (fun column => reading.read (matrix row column) * reading.read (values column)) -
      model row) ≤ reading.error * retained.outputCoefficients errors row := by
  have first := (Norm.Bounds.normSq_sub_symm
    (sumFin (fun column => reading.read (matrix row column) * reading.read (values column)))
    (reading.read (Rectangular.apply matrix values row))).le.trans (retained.bound reading row)
  have identity : sumFin (fun column => reading.read (matrix row column) * reading.read (values column)) - model row =
      (sumFin (fun column => reading.read (matrix row column) * reading.read (values column)) -
        reading.read (Rectangular.apply matrix values row)) +
      (reading.read (Rectangular.apply matrix values row) - model row) := by ring1
  rewrite [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct first (paid row))
      (by decide : (0 : Rational) ≤ 2)).trans_eq (by rewrite [retained.outputCoefficients_at]; ring1))

end Application

set_option genInjectivity false in
/-- Cached additional input-model errors for the same original matrix action.

The original product-error cache is reused. Fixed gain and a nonnegative
source-fixed input error table compute one amplification coefficient and one
combined coefficient per row before any actual reading or model is selected.
-/
structure Perturbation {weight : Weight K} {matrix : Rectangular K rows columns} {values : Vec K columns}
    (application : Application weight matrix values) (gain : Rational) (errors : Vec Rational columns) where
  /-- The fixed original reading gain is nonnegative. -/
  gainNonnegative : 0 ≤ gain
  /-- The source-fixed input discrepancy coefficients are nonnegative. -/
  errorsNonnegative : ∀ column, 0 ≤ errors column
  /-- The materialized original row amplification coefficients. -/
  amplification : Vec Rational rows
  /-- Every amplification coefficient consumes the same original matrix-bound table and input errors. -/
  amplification_eq : ∀ row, amplification row = application.factor *
    sumFin (fun column => application.matrixWeights row column * errors column)
  /-- The materialized combined product and input-model error coefficients. -/
  coefficients : Vec Rational rows
  /-- Each coefficient reuses the same original product coefficient and retained amplification. -/
  coefficients_eq : ∀ row, coefficients row = 2 * (application.coefficients row + gain * amplification row)

constructive_injectivity Perturbation

namespace Perturbation

variable {weight : Weight K} {matrix : Rectangular K rows columns} {values : Vec K columns}
variable {application : Application weight matrix values} {gain : Rational} {errors : Vec Rational columns}

/-- Prepare the same original matrix action's combined error table without replaying its product coefficients. -/
@[expose] def prepare (application : Application weight matrix values) (gain : Rational) (gainNonnegative : 0 ≤ gain)
    (errors : Vec Rational columns) (errorsNonnegative : ∀ column, 0 ≤ errors column) :
    Perturbation application gain errors :=
  let amplification := vectorOfFn (fun row => application.factor *
    sumFin (fun column => application.matrixWeights row column * errors column))
  let coefficients := vectorOfFn (fun row => 2 * (application.coefficients row + gain * amplification row))
  { gainNonnegative, errorsNonnegative, amplification, amplification_eq := fun row => vectorOfFn_apply _ row
    coefficients, coefficients_eq := fun row => vectorOfFn_apply _ row }

/-- Every same retained row amplification coefficient is nonnegative. -/
theorem amplification_nonnegative (retained : Perturbation application gain errors) (row : Fin rows) :
    0 ≤ retained.amplification row := by
  rewrite [retained.amplification_eq]
  exact Arithmetic.mul_nonneg_direct application.factor_positive.le (weight_sum_nonnegative _ fun column =>
    Arithmetic.mul_nonneg_direct (application.matrixWeight_nonnegative row column) (retained.errorsNonnegative column))

/-- Every combined original row discrepancy coefficient is nonnegative. -/
theorem coefficient_nonnegative (retained : Perturbation application gain errors) (row : Fin rows) :
    0 ≤ retained.coefficients row := by
  rewrite [retained.coefficients_eq]
  exact Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2)
    (Arithmetic.add_le_add_direct (application.coefficient_nonnegative row)
      (Arithmetic.mul_nonneg_direct retained.gainNonnegative (retained.amplification_nonnegative row)))

/-- The actual Gaussian matrix readback amplifies the same paid input-model error by its retained coefficient. -/
theorem amplification_bound (retained : Perturbation application gain errors) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain) (model : Vec Canonical columns)
    (paid : ∀ column, Norm.Basic.normSq (reading.read (values column) - model column) ≤ reading.error * errors column)
    (row : Fin rows) :
    Norm.Basic.normSq (sumFin (fun column => reading.read (matrix row column) * reading.read (values column)) -
      sumFin (fun column => reading.read (matrix row column) * model column)) ≤
        reading.error * (gain * retained.amplification row) := by
  have same : sumFin (fun column => reading.read (matrix row column) * reading.read (values column)) -
      sumFin (fun column => reading.read (matrix row column) * model column) =
      sumFin (fun column => reading.read (matrix row column) * (reading.read (values column) - model column)) := by
    exact (sumFin_sub _ _).symm.trans (sumFin_congr fun _ => by ring1)
  rewrite [same]
  have bounded := Norm.normSq_sumFin_mul_le
    (fun column => reading.read (matrix row column)) (fun column => reading.read (values column) - model column)
    (fun column => gain * application.matrixWeights row column) (fun column => reading.error * errors column)
    (fun column => by
      have bound := reading.gainBound (matrix row column)
      rewrite [gain_eq] at bound
      exact bound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (application.matrixBound row column) retained.gainNonnegative)) paid
  have collected : sumFin (fun column => (gain * application.matrixWeights row column) *
      (reading.error * errors column)) = (gain * reading.error) *
        sumFin (fun column => application.matrixWeights row column * errors column) :=
    (sumFin_congr fun _ => by ring1).trans (sumFin_mul_left _ _)
  rewrite [collected] at bounded
  exact bounded.trans_eq (by rewrite [retained.amplification_eq, application.factor_eq]; ring1)

/-- The reading of the same actual formal matrix action pays both retained product and input-model errors. -/
theorem bound (retained : Perturbation application gain errors) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain) (model : Vec Canonical columns)
    (paid : ∀ column, Norm.Basic.normSq (reading.read (values column) - model column) ≤ reading.error * errors column)
    (row : Fin rows) :
    Norm.Basic.normSq (reading.read (Rectangular.apply matrix values row) -
      sumFin (fun column => reading.read (matrix row column) * model column)) ≤
        reading.error * retained.coefficients row := by
  have identity : reading.read (Rectangular.apply matrix values row) -
      sumFin (fun column => reading.read (matrix row column) * model column) =
      (reading.read (Rectangular.apply matrix values row) -
        sumFin (fun column => reading.read (matrix row column) * reading.read (values column))) +
      (sumFin (fun column => reading.read (matrix row column) * reading.read (values column)) -
        sumFin (fun column => reading.read (matrix row column) * model column)) := by ring1
  rewrite [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct (application.bound reading row)
        (retained.amplification_bound reading gain_eq model paid row)) (by decide : (0 : Rational) ≤ 2)).trans_eq (by
          rewrite [retained.coefficients_eq]
          ring1))

end Perturbation

/-- Materialize finite matrix-product error coefficients from the same two certified source-bound tables. -/
@[expose] def productCoefficients {middle : Nat} (left : Rectangular Rational rows middle)
    (right : Rectangular Rational middle columns) : Rectangular Rational rows columns :=
  let factor := (2 : Rational) ^ middle
  Rectangular.ofFn fun row column => factor * sumFin (fun index => left row index * right index column)

/-- Every materialized product coefficient reads the original shared intermediate dimension and cached entries. -/
theorem productCoefficients_at {middle : Nat} (left : Rectangular Rational rows middle)
    (right : Rectangular Rational middle columns) (row : Fin rows) (column : Fin columns) :
    productCoefficients left right row column = (2 : Rational) ^ middle *
      sumFin (fun index => left row index * right index column) := Rectangular.ofFn_apply _ _ _

/-- Actual original matrix multiplication pays the same retained two-table product coefficient. -/
theorem product_bound {middle : Nat} {weight : Weight K} {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (left : Rectangular K rows middle)
    (right : Rectangular K middle columns) (leftWeights : Rectangular Rational rows middle)
    (rightWeights : Rectangular Rational middle columns) (leftBound : MatrixBounds weight left leftWeights)
    (rightBound : MatrixBounds weight right rightWeights) (row : Fin rows) (column : Fin columns) :
    Norm.Basic.normSq (reading.read (Rectangular.mul left right row column) -
      sumFin (fun index => reading.read (left row index) * reading.read (right index column))) ≤
        reading.error * productCoefficients leftWeights rightWeights row column := by
  rewrite [Rectangular.mul_at]
  exact (reading.sum_discrepancy_bound _ _ _ (fun index =>
    product_error_le reading _ _ _ _ (leftBound row index) (rightBound index column))).trans_eq (by
      rewrite [productCoefficients_at]
      rfl)

end Purelib.LinearAlgebra.Matrix.Reading

end
