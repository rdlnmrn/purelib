module

public import Purelib.LinearAlgebra.Matrix.Reading
public import Purelib.LinearAlgebra.Matrix.Arithmetic
public import Purelib.Data.Vector.Scan
import Purelib.LinearAlgebra.Matrix.Rectangular.Identity
import Purelib.Data.Fin
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Source-fixed paid propagation through original finite matrix powers

One retained matrix-action cache supplies the source weights. A rational
scan bounds the original power trajectory's total weight and its uniform
Gaussian reading error. No formal matrix power or vector action is computed
by this request constructor; the bounds concern the original power engine.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Reading.Power

open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector.Scan
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix

variable {K : Type*} [CommRing K] {dimension : Nat}

/-- Advance the original total source-weight bound and uniform paid Gaussian error coefficient. -/
@[expose] def step (factor multiplier matrixTotal gain : Rational) (state : Rational × Rational) (_edge : Unit) :
    Rational × Rational :=
  (factor * multiplier * matrixTotal * state.1,
    2 * factor * matrixTotal * (state.1 + gain * state.2))

/-- The original power acts on the same retained initial vector at its finite natural exponent. -/
abbrev trajectory (matrix : SquareMatrix K dimension) (initial : Vec K dimension) (time : Nat) :=
  Rectangular.apply (Arithmetic.power matrix time) initial

/-- The original zero-power trajectory is the same actual initial vector. -/
theorem trajectory_zero (matrix : SquareMatrix K dimension) (initial : Vec K dimension) :
    trajectory matrix initial 0 = initial := Rectangular.apply_unit initial

/-- The original successor power applies the same original matrix to its preceding retained trajectory. -/
theorem trajectory_step (matrix : SquareMatrix K dimension) (initial : Vec K dimension) (time : Nat) :
    trajectory matrix initial (time + 1) = Rectangular.apply matrix (trajectory matrix initial time) := by
  change Rectangular.apply (Arithmetic.power matrix (time + 1)) initial =
    Rectangular.apply matrix (Rectangular.apply (Arithmetic.power matrix time) initial)
  rewrite [Arithmetic.power_succ, ← Arithmetic.commute_power matrix matrix rfl time]
  have same : Multiplication.mul matrix (Arithmetic.power matrix time) =
      Rectangular.mul matrix (Arithmetic.power matrix time) :=
    Rectangular.ext fun row column => (Multiplication.mul_apply _ _ row column).trans
      (Rectangular.mul_at _ _ row column).symm
  rewrite [same]
  exact Rectangular.apply_mul _ _ _

set_option genInjectivity false in
/-- A single rational propagation table reusing the original matrix-action source-weight cache.

Its first coordinate bounds the total weight of the original formal power
trajectory. The second bounds every actual Gaussian coordinate discrepancy,
linearly in the same reading's multiplication error. All data precede any
reading or physical matrix, and no invertibility premise is required.
-/
structure Parameters {weight : Weight K} {matrix : SquareMatrix K dimension} {initial : Vec K dimension}
    (application : Application weight matrix initial) (gain : Rational) (count : Nat) where
  /-- The fixed original reading gain is nonnegative. -/
  gainNonnegative : 0 ≤ gain
  /-- The once-computed total of the original cached matrix-entry bounds. -/
  matrixTotal : Rational
  /-- The matrix total consumes the exact original bound table. -/
  matrixTotal_eq : matrixTotal = sumFin (fun row => sumFin (fun column => application.matrixWeights row column))
  /-- The once-computed total of the original cached initial-entry bounds. -/
  initialTotal : Rational
  /-- The initial total consumes the exact same original coefficient-vector bound table. -/
  initialTotal_eq : initialTotal = sumFin (fun column => application.valueWeights column)
  /-- The retained rational weight/error scan through the finite requested power horizon. -/
  table : Vec (Rational × Rational) (count + 1)
  /-- The table is the original structural scan on those exact retained parameters. -/
  table_eq : table = scan (step application.factor weight.multiplier matrixTotal gain) (initialTotal, 0)
    (vectorOfFn (fun _ : Fin count => Unit.unit))

constructive_injectivity Parameters

namespace Parameters

variable {weight : Weight K} {matrix : SquareMatrix K dimension} {initial : Vec K dimension}
variable {application : Application weight matrix initial} {gain : Rational} {count : Nat}

/-- Prepare one rational bound table without rescanning weights or computing any formal power trajectory. -/
@[expose] def prepare (application : Application weight matrix initial) (gain : Rational) (gainNonnegative : 0 ≤ gain)
    (count : Nat) : Parameters application gain count :=
  let matrixTotal := sumFin (fun row => sumFin (fun column => application.matrixWeights row column))
  let initialTotal := sumFin (fun column => application.valueWeights column)
  let table := scan (step application.factor weight.multiplier matrixTotal gain) (initialTotal, 0)
    (vectorOfFn (fun _ : Fin count => Unit.unit))
  { gainNonnegative, matrixTotal, matrixTotal_eq := rfl, initialTotal, initialTotal_eq := rfl, table, table_eq := rfl }

/-- The complete retained propagation table restores its original constructor on the same application cache. -/
theorem restore (parameters : Parameters application gain count) :
    parameters = prepare application gain parameters.gainNonnegative count := by
  cases parameters with
  | mk gainNonnegative matrixTotal matrixTotalEq initialTotal initialTotalEq table tableEq =>
      cases matrixTotalEq
      cases initialTotalEq
      cases tableEq
      rfl

/-- The original cached matrix-bound total is nonnegative. -/
theorem matrixTotal_nonnegative (parameters : Parameters application gain count) : 0 ≤ parameters.matrixTotal := by
  rewrite [parameters.matrixTotal_eq]
  exact weight_sum_nonnegative _ fun row => weight_sum_nonnegative _ (application.matrixWeight_nonnegative row)

/-- The original cached initial-bound total is nonnegative. -/
theorem initialTotal_nonnegative (parameters : Parameters application gain count) : 0 ≤ parameters.initialTotal := by
  rewrite [parameters.initialTotal_eq]
  exact weight_sum_nonnegative _ application.valueWeight_nonnegative

/-- Every same cached original matrix row has weight sum at most the retained complete matrix total. -/
theorem row_le_total (parameters : Parameters application gain count) (row : Fin dimension) :
    sumFin (fun column => application.matrixWeights row column) ≤ parameters.matrixTotal := by
  rewrite [parameters.matrixTotal_eq]
  exact entry_le_sumFin _ (fun row => weight_sum_nonnegative _ (application.matrixWeight_nonnegative row)) row

/-- The retained scan starts at the same initial-bound total and zero discrepancy. -/
theorem table_zero (parameters : Parameters application gain count) :
    parameters.table ⟨0, Nat.zero_lt_succ count⟩ = (parameters.initialTotal, 0) := by
  rewrite [parameters.table_eq]
  cases count <;> rfl

/-- Each retained successor consumes only its same preceding rational state. -/
theorem table_step (parameters : Parameters application gain count) (index : Fin count) :
    parameters.table index.succ = step application.factor weight.multiplier parameters.matrixTotal gain
      (parameters.table index.castSucc) Unit.unit := by
  rewrite [parameters.table_eq, scan_step, vectorOfFn_apply]
  rfl

/-- Both coefficients of every retained rational scan state are nonnegative. -/
theorem table_nonnegative (parameters : Parameters application gain count) (index : Fin (count + 1)) :
    0 ≤ (parameters.table index).1 ∧ 0 ≤ (parameters.table index).2 := by
  refine Purelib.Data.Fin.induction (motive := fun index =>
    0 ≤ (parameters.table index).1 ∧ 0 ≤ (parameters.table index).2) ?_ ?_ index
  · rewrite [parameters.table_zero]
    exact ⟨parameters.initialTotal_nonnegative, le_refl _⟩
  · intro index previous
    rewrite [parameters.table_step]
    constructor
    · exact Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct application.factor_positive.le weight.multiplier_nonnegative)
          parameters.matrixTotal_nonnegative) previous.1
    · exact Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2)
          application.factor_positive.le) parameters.matrixTotal_nonnegative)
        (Arithmetic.add_le_add_direct previous.1 (Arithmetic.mul_nonneg_direct parameters.gainNonnegative previous.2))

/-- The same original matrix acts on uniformly bounded source entries with a bounded total source weight. -/
private theorem source_step (parameters : Parameters application gain count) (values : Vec K dimension)
    (bound : Rational) (bounded : ∀ column, weight.value (values column) ≤ bound) :
    sumFin (fun row => weight.value (Rectangular.apply matrix values row)) ≤
      application.factor * weight.multiplier * parameters.matrixTotal * bound := by
  let current := Application.prepare weight matrix values application.matrixWeights application.matrixBound
    (vectorOfFn (fun _ => bound)) (fun column =>
      (bounded column).trans_eq (vectorOfFn_apply (fun _ : Fin dimension => bound) column).symm)
  have each (row : Fin dimension) : current.coefficients row =
      application.factor * sumFin (fun column => application.matrixWeights row column) * bound := by
    rewrite [current.coefficients_eq, current.factor_eq, ← application.factor_eq]
    have entries : sumFin (fun column => current.matrixWeights row column * current.valueWeights column) =
        sumFin (fun column => application.matrixWeights row column * bound) :=
      sumFin_congr fun column => congrArg (fun value => application.matrixWeights row column * value)
        (vectorOfFn_apply (fun _ : Fin dimension => bound) column)
    rewrite [entries, sumFin_mul_right]
    ring1
  have total : sumFin (fun row => current.coefficients row) =
      application.factor * parameters.matrixTotal * bound := by
    rewrite [sumFin_congr each, sumFin_mul_right, sumFin_mul_left, ← parameters.matrixTotal_eq]
    rfl
  have result := current.weight_total_bound
  rewrite [total] at result
  exact result.trans_eq (by ring1)

/-- Every original formal power trajectory has total source weight bounded by its same retained scan state. -/
theorem source_bound (parameters : Parameters application gain count) (index : Fin (count + 1)) :
    sumFin (fun row => weight.value (trajectory matrix initial index.val row)) ≤ (parameters.table index).1 := by
  refine Purelib.Data.Fin.induction (motive := fun index =>
    sumFin (fun row => weight.value (trajectory matrix initial index.val row)) ≤ (parameters.table index).1)
      ?_ ?_ index
  · rewrite [trajectory_zero, parameters.table_zero, parameters.initialTotal_eq]
    exact IndexedBudget.sumFin_le application.valuesBound
  · intro index previous
    change sumFin (fun row => weight.value (trajectory matrix initial (index.val + 1) row)) ≤
      (parameters.table index.succ).1
    rewrite [trajectory_step, parameters.table_step]
    exact parameters.source_step _ _ (fun column =>
      (entry_le_sumFin _ (fun column => weight.nonnegative _) column).trans previous)

/-- Every coordinate of the original trajectory inherits the same retained total source-weight bound. -/
theorem source_entry_bound (parameters : Parameters application gain count) (index : Fin (count + 1))
    (row : Fin dimension) : weight.value (trajectory matrix initial index.val row) ≤ (parameters.table index).1 :=
  (entry_le_sumFin _ (fun row => weight.nonnegative (trajectory matrix initial index.val row)) row).trans
    (parameters.source_bound index)

/-- A uniform same-reading input discrepancy propagates through the same actual original matrix. -/
private theorem reading_step (parameters : Parameters application gain count) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (values : Vec K dimension) (model : Vec Canonical dimension) (sourceBound errorBound : Rational)
    (sourceNonnegative : 0 ≤ sourceBound) (errorNonnegative : 0 ≤ errorBound)
    (sourcePaid : ∀ column, weight.value (values column) ≤ sourceBound)
    (errorPaid : ∀ column, Norm.Basic.normSq (reading.read (values column) - model column) ≤
      reading.error * errorBound) (row : Fin dimension) :
    Norm.Basic.normSq (reading.read (Rectangular.apply matrix values row) -
      sumFin (fun column => reading.read (matrix row column) * model column)) ≤
      reading.error * (2 * application.factor * parameters.matrixTotal * (sourceBound + gain * errorBound)) := by
  let current := Application.prepare weight matrix values application.matrixWeights application.matrixBound
    (vectorOfFn (fun _ => sourceBound)) (fun column =>
      (sourcePaid column).trans_eq
        (vectorOfFn_apply (fun _ : Fin dimension => sourceBound) column).symm)
  let perturbation := Perturbation.prepare current gain parameters.gainNonnegative
    (vectorOfFn (fun _ => errorBound)) (fun column =>
      (vectorOfFn_apply (fun _ : Fin dimension => errorBound) column).symm ▸ errorNonnegative)
  have paid : ∀ column, Norm.Basic.normSq (reading.read (values column) - model column) ≤
      reading.error * (vectorOfFn (fun _ : Fin dimension => errorBound)) column := fun column =>
    (errorPaid column).trans_eq (congrArg (reading.error * ·)
      (vectorOfFn_apply (fun _ : Fin dimension => errorBound) column).symm)
  have coefficient : perturbation.coefficients row =
      2 * application.factor * sumFin (fun column => application.matrixWeights row column) *
        (sourceBound + gain * errorBound) := by
    rewrite [perturbation.coefficients_eq, perturbation.amplification_eq, current.coefficients_eq,
      current.factor_eq, ← application.factor_eq]
    have sources : sumFin (fun column => current.matrixWeights row column * current.valueWeights column) =
        sumFin (fun column => application.matrixWeights row column) * sourceBound :=
      (sumFin_congr fun column => congrArg (fun value => application.matrixWeights row column * value)
        (vectorOfFn_apply (fun _ : Fin dimension => sourceBound) column)).trans (sumFin_mul_right _ _)
    have errors : sumFin (fun column => current.matrixWeights row column *
        (vectorOfFn (fun _ : Fin dimension => errorBound)) column) =
        sumFin (fun column => application.matrixWeights row column) * errorBound :=
      (sumFin_congr fun column => congrArg (fun value => application.matrixWeights row column * value)
        (vectorOfFn_apply (fun _ : Fin dimension => errorBound) column)).trans (sumFin_mul_right _ _)
    rewrite [sources, errors]
    ring1
  have bracketNonnegative := Arithmetic.add_le_add_direct sourceNonnegative
    (Arithmetic.mul_nonneg_direct parameters.gainNonnegative errorNonnegative)
  have rowBound := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (parameters.row_le_total row)
      (Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2) application.factor_positive.le))
    bracketNonnegative
  exact (perturbation.bound reading gain_eq model paid row).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (coefficient.trans_le rowBound) reading.errorNonnegative)

/-- The same actual original power and the Gaussian readback power have a paid finite-coordinate discrepancy.

Both cached physical entry tables read the original matrix and initial
coefficients pointwise. Formal nonzero coefficients need not have nonzero
physical readings; no inverse or lower-bound premise enters this estimate.
-/
theorem bound (parameters : Parameters application gain count) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (observedMatrix : SquareMatrix Canonical dimension)
    (matrixEq : ∀ row column, observedMatrix row column = reading.read (matrix row column))
    (observedInitial : Vec Canonical dimension)
    (initialEq : ∀ column, observedInitial column = reading.read (initial column))
    (index : Fin (count + 1)) (row : Fin dimension) :
    Norm.Basic.normSq (reading.read (trajectory matrix initial index.val row) -
      trajectory observedMatrix observedInitial index.val row) ≤ reading.error * (parameters.table index).2 := by
  refine Purelib.Data.Fin.induction (motive := fun index => ∀ row,
    Norm.Basic.normSq (reading.read (trajectory matrix initial index.val row) -
      trajectory observedMatrix observedInitial index.val row) ≤ reading.error * (parameters.table index).2)
        ?_ ?_ index row
  · intro row
    rewrite [trajectory_zero, trajectory_zero, initialEq row, sub_self, Norm.Basic.normSq_zero,
      parameters.table_zero, mul_zero]
    exact le_refl _
  · intro index previous row
    change Norm.Basic.normSq (reading.read (trajectory matrix initial (index.val + 1) row) -
      trajectory observedMatrix observedInitial (index.val + 1) row) ≤ reading.error * (parameters.table index.succ).2
    rewrite [trajectory_step, trajectory_step, parameters.table_step]
    have bounded := parameters.reading_step reading gain_eq _ _ (parameters.table index.castSucc).1
      (parameters.table index.castSucc).2 (parameters.table_nonnegative index.castSucc).1
      (parameters.table_nonnegative index.castSucc).2 (parameters.source_entry_bound index.castSucc) previous row
    have modelEq : Rectangular.apply observedMatrix
        (trajectory observedMatrix observedInitial index.val) row =
        sumFin (fun column => reading.read (matrix row column) *
          trajectory observedMatrix observedInitial index.val column) := by
      rewrite [Rectangular.apply_at]
      exact sumFin_congr fun column => congrArg (· * trajectory observedMatrix observedInitial index.val column)
        (matrixEq row column)
    rewrite [modelEq]
    exact bounded

/-- Exact retained trajectory readbacks transport the bound without evaluating another matrix power or action. -/
theorem bound_of_trajectories (parameters : Parameters application gain count) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (observedMatrix : SquareMatrix Canonical dimension)
    (matrixEq : ∀ row column, observedMatrix row column = reading.read (matrix row column))
    (observedInitial : Vec Canonical dimension)
    (initialEq : ∀ column, observedInitial column = reading.read (initial column))
    (index : Fin (count + 1)) (originalValues : Vec K dimension)
    (originalEq : originalValues = trajectory matrix initial index.val) (model : Vec Canonical dimension)
    (modelEq : model = trajectory observedMatrix observedInitial index.val) (row : Fin dimension) :
    Norm.Basic.normSq (reading.read (originalValues row) - model row) ≤ reading.error * (parameters.table index).2 := by
  cases originalEq
  cases modelEq
  exact parameters.bound reading gain_eq observedMatrix matrixEq observedInitial initialEq index row

end Parameters
end Purelib.LinearAlgebra.Matrix.Reading.Power

end
