module

meta import Lean.Elab.Tactic.RCases
public import Purelib.Curves.Legendre.Periods.Jets.Connection.Matrix
public import Purelib.Calculus.Linear.Euler
public import Purelib.Calculus.Jet.Quadratic.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Legendre.PicardFuchs.Connection
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Gaussian.Norm
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Vector.Basic
import Purelib.Data.Fin.Two
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Local Euler defects from actual Legendre Taylor and connection samples

The original quadratic certificates supply both endpoint readings and the
symbolic derivative reading. The original admitted source supplies its
synchronized connection residual at that same stage. One original finite
selection pays this residual before callbacks. No differential equation,
endpoint agreement or local defect inequality is an input.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Connection

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin_succ sumFin_congr sumFin_mul_left)
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Rational.Geometric
open Purelib.Calculus.Jet.Quadratic.Basic (Certificate)
open Purelib.Calculus.Linear
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Scale (scale normSq_scale scale_mul_product)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Data.Vector (map)
open Purelib.Data.Vector.Basic (map_apply vectorOfFn vectorOfFn_apply zipWith_apply)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.LinearAlgebra renaming Matrix → Mat
open Purelib.LinearAlgebra.Gaussian
open Purelib.LinearAlgebra.Matrix (matrix_eq_at matrixOfFn_apply)
open Purelib.LinearAlgebra.Matrix.Multiplication

/-- Pull the original connection matrix back along one exact Gaussian affine direction. -/
def alongMatrix (parameter direction : Canonical) : Mat Canonical 2 :=
  mul (scaleIdentity direction) (matrix parameter)

/-- Each pulled-back entry retains the same original connection coefficient and Gaussian direction. -/
theorem alongMatrix_apply (parameter direction : Canonical) (row column : Fin 2) :
    alongMatrix parameter direction row column = direction * matrix parameter row column :=
  (matrix_eq_at (scaleIdentity_mul direction (matrix parameter)) row column).trans
    (matrixOfFn_apply (fun row column => direction * matrix parameter row column) row column)

/-- Pullback multiplies the complete original matrix quadrance by the actual direction quadrance. -/
theorem alongMatrix_norm (parameter direction : Canonical) :
    Norm.matrix (alongMatrix parameter direction) = Norm.Basic.normSq direction * Norm.matrix (matrix parameter) := by
  have rows (row : Fin 2) : Norm.vector (alongMatrix parameter direction row) =
      Norm.Basic.normSq direction * Norm.vector (matrix parameter row) :=
    (sumFin_congr (fun column =>
      (congrArg Norm.Basic.normSq (alongMatrix_apply parameter direction row column)).trans
        (Norm.Basic.normSq_mul _ _))).trans (sumFin_mul_left _ _)
  exact (sumFin_congr rows).trans (sumFin_mul_left _ _)

/-- The original parameter clearance bounds the pulled-back matrix uniformly on its admitted increment ball.

The same literal direction scales the original fixed matrix ceiling. No
source stage, adaptive child count or transported period enters this bound.
-/
theorem alongMatrix_le {parameter : Canonical} (clearance : ParameterClearance parameter)
    (increment direction : Canonical) (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound) :
    Norm.matrix (alongMatrix (parameter + increment) direction) ≤
      Norm.Basic.normSq direction * matrixCeiling clearance :=
  (alongMatrix_norm (parameter + increment) direction).trans_le
    (mul_le_mul_of_nonneg_left_direct (matrix_le clearance increment admitted)
      (Norm.Basic.normSq_nonneg direction))

/-- The retained pulled-back matrix acts by the original direction times the original connection action. -/
theorem alongMatrix_vector (parameter direction : Canonical) (values : Vec Canonical 2) (row : Fin 2) :
    matrixVector (alongMatrix parameter direction) values row =
      direction * matrixVector (matrix parameter) values row := by
  unfold alongMatrix
  rewrite [matrixVector_mul, matrixVector_scaleIdentity, vectorOfFn_apply]
  rfl

/-- A zero parameter direction gives zero original connection action on every retained vector coordinate. -/
theorem alongMatrix_zero_vector (parameter : Canonical) (values : Vec Canonical 2) (row : Fin 2) :
    matrixVector (alongMatrix parameter 0) values row = 0 :=
  (alongMatrix_vector parameter 0 values row).trans (by ring1)

/-- Independent finite connection transport in the constant parameter direction preserves its exact initial vector.

The zero action is derived from the original directional coefficient
matrix. No nonzero-increment preparation, source query or endpoint
identity is supplied to this trace.
-/
theorem constant_trace (parameter : Canonical) (widths : Nat → Rational) (initial : Vec Canonical 2) (count : Nat) :
    Euler.trace (fun _ => alongMatrix parameter 0) widths initial count = initial :=
  Euler.trace_eq_of_action_zero (fun _ => alongMatrix parameter 0) widths initial count
    (fun _index _before row => alongMatrix_zero_vector parameter initial row)

/-- The actual same-stage period readings are unchanged by independent constant-parameter connection transport.

Both coordinates retain their original jet, integral programmes and source
sample index. The trace starts from those literal readings and needs no
shifted source family or zero-increment Taylor acquisition.
-/
theorem constant_period_trace {parameter : Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (index : Nat) (widths : Nat → Rational) (count : Nat) :
    Euler.trace (fun _ => alongMatrix parameter 0) widths
        (vectorOfFn (fun coordinate => ((jet.value coordinate).integral.model index).integralSample)) count =
      vectorOfFn (fun coordinate => ((jet.value coordinate).integral.model index).integralSample) :=
  constant_trace parameter widths _ count

/-- Read the original synchronized residual through the original symbolic row coefficients. -/
private theorem residual_sample {parameter : Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (index : Nat) (row : Fin 2) :
    (connectionResidualGeometric jet row).sample index =
      ParameterClearance.connectionDenominator parameter *
        (((jet.first row).integral.model index).integralSample) -
      ((connectionReduction parameter row).basisConstant *
        (((jet.value 0).integral.model index).integralSample) +
        (connectionReduction parameter row).basisLinear *
          (((jet.value 1).integral.model index).integralSample)) := by
  rcases Data.Fin.Two.finTwo_cases row with equal | equal
  · subst row
    rewrite [connectionReduction_zero]
    dsimp only [connectionResidualGeometric, connectionScaledFirstGeometric, connectionActionGeometric]
    rewrite [if_pos rfl]
    simp only [GeometricApproximation.sub_sample, GeometricApproximation.mul_sample,
      GeometricApproximation.exact_sample, RefinementProgram.geometric_sample]
    change _ = _ - (parameter * _ + (-1) * _)
    ring1
  · subst row
    rewrite [connectionReduction_one]
    dsimp only [connectionResidualGeometric, connectionScaledFirstGeometric, connectionActionGeometric]
    rewrite [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    simp only [GeometricApproximation.sub_sample, GeometricApproximation.mul_sample,
      GeometricApproximation.exact_sample, RefinementProgram.geometric_sample]
    change _ = _ - (parameter * _ + (-parameter) * _)
    ring1

/-- The same source stage pays its actual symbolic-slope discrepancy from the original connection matrix action.

Both displayed equalities are exact original sample readbacks. The retained
finite selection supplies the stage payment; the bound comes from the
source's actual connection residual and original positive denominator floor.
-/
theorem sourceSlope_le {parameter : Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (width : Rational) (start index : Nat)
    (selection : Search.Selection 1 start
      (width ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq))
    (after : selection.stage ≤ index) (values : Vec Canonical 2) (slope : Canonical) (row : Fin 2)
    (values_eq : ∀ coordinate, values coordinate = ((jet.value coordinate).integral.model index).integralSample)
    (slope_eq : slope = ((jet.first row).integral.model index).integralSample) :
    Norm.Basic.normSq (slope - matrixVector (matrix parameter) values row) ≤ width ^ 2 := by
  let clearance := ParameterClearance.ofFrame frame
  let denominator := ParameterClearance.connectionDenominator parameter
  have cleared := matrixVector_cleared clearance values row
  have action := congrArg₂ (fun first last : Canonical =>
      (connectionReduction parameter row).basisConstant * first +
        (connectionReduction parameter row).basisLinear * last) (values_eq 0) (values_eq 1)
  have residual : denominator * (slope - matrixVector (matrix parameter) values row) =
      (connectionResidualGeometric jet row).sample index := by
    calc
      _ = denominator * slope - denominator * matrixVector (matrix parameter) values row := by ring1
      _ = denominator * ((jet.first row).integral.model index).integralSample -
          ((connectionReduction parameter row).basisConstant *
            ((jet.value 0).integral.model index).integralSample +
              (connectionReduction parameter row).basisLinear *
                ((jet.value 1).integral.model index).integralSample) :=
        congrArg₂ (fun first last : Canonical => first - last)
          (congrArg (fun value : Canonical => denominator * value) slope_eq) (cleared.trans action)
      _ = _ := (residual_sample jet index row).symm
  have paid := (connectionResidual_error_le jet row index).trans (selection.later_accurate after).le
  have floorPaid := mul_le_mul_of_nonneg_left_direct clearance.connectionLowerSq_le_normSq
    (sq_nonneg_direct width)
  have multiplied : Norm.Basic.normSq (slope - matrixVector (matrix parameter) values row) *
      Norm.Basic.normSq denominator ≤ width ^ 2 * Norm.Basic.normSq denominator := by
    calc
      _ = Norm.Basic.normSq (denominator * (slope - matrixVector (matrix parameter) values row)) :=
        (Data.Rat.Fraction.Field.mul_comm _ _).trans (Norm.Basic.normSq_mul _ _).symm
      _ = Norm.Basic.normSq ((connectionResidualGeometric jet row).sample index) :=
        congrArg Norm.Basic.normSq residual
      _ ≤ width ^ 2 * clearance.connectionLowerSq := paid
      _ ≤ _ := floorPaid
  exact le_of_mul_le_mul_right_direct multiplied
    (Norm.Basic.normSq_pos clearance.connectionDenominator_ne_zero)

/-- Construct the original finite synchronized-source residual payment before any sample callback. -/
def connectionSelection {parameter : Canonical} (frame : Paths.Frame parameter)
    (width : Rational) (positive : 0 < width) (start : Nat) :
    Search.Selection 1 start (width ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq) :=
  Search.Selection.build 1 (by decide) start _
    (mul_pos_direct (pow_pos_direct positive 2) (ParameterClearance.ofFrame frame).connectionLowerSq_positive)

/-- The whole selection cache is the original search on the same width and original source denominator floor. -/
theorem connectionSelection_eq {parameter : Canonical} (frame : Paths.Frame parameter)
    (width : Rational) (positive : 0 < width) (start : Nat) :
    connectionSelection frame width positive start =
      Search.Selection.build 1 (by decide) start
        (width ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq)
        (mul_pos_direct (pow_pos_direct positive 2)
          (ParameterClearance.ofFrame frame).connectionLowerSq_positive) := by rfl

/-- Compute the directional local Euler factor from both original Taylor factors. -/
@[expose] def eulerFactor {increment : Canonical} (entries : Vec (Certificate increment) 2)
    (direction : Canonical) : Rational :=
  2 * (((entries 0).factor + (entries 1).factor) * Norm.Basic.normSq direction ^ 2 +
    2 * Norm.Basic.normSq direction)

/-- The actual two-coordinate Euler factor is nonnegative, including a zero Gaussian direction. -/
theorem eulerFactor_nonnegative {increment : Canonical} (entries : Vec (Certificate increment) 2)
    (direction : Canonical) : 0 ≤ eulerFactor entries direction :=
  mul_nonneg_direct (by decide)
    ((show (0 : Rational) = 0 + 0 by ring1).trans_le
      (add_le_add_direct
        (mul_nonneg_direct
          ((show (0 : Rational) = 0 + 0 by ring1).trans_le
            (add_le_add_direct (entries 0).factor_nonneg (entries 1).factor_nonneg))
          (sq_nonneg_direct _))
        (mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg direction))))

/-- The original Taylor entries and internally bounded connection samples give the actual Euler quadrance defect.

The increment remains the original certificate index. Its equality to the
displayed rational-width Gaussian movement is an exact scalar identity.
The original base/output fields produce the two structural endpoint vectors;
the conclusion concerns those same caches, not an assumed next source jet.
-/
theorem eulerDefect_le {parameter increment : Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (width : Rational) (direction : Canonical)
    (scaled : increment = scale width direction) (start index : Nat)
    (selection : Search.Selection 1 start
      (width ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq))
    (after : selection.stage ≤ index) (entries : Vec (Certificate increment) 2)
    (base_eq : ∀ coordinate, (entries coordinate).base =
      ((jet.value coordinate).integral.model index).integralSample)
    (slope_eq : ∀ coordinate, (entries coordinate).slope =
      ((jet.first coordinate).integral.model index).integralSample) :
    Norm.vector (Euler.defect (alongMatrix parameter direction) width
      (map Certificate.base entries) (map Certificate.output entries)) ≤
      eulerFactor entries direction * width ^ 4 := by
  let values := map Certificate.base entries
  have values_eq (coordinate : Fin 2) : values coordinate =
      ((jet.value coordinate).integral.model index).integralSample :=
    (map_apply Certificate.base entries coordinate).trans (base_eq coordinate)
  have incrementNorm : Norm.Basic.normSq increment = width ^ 2 * Norm.Basic.normSq direction :=
    (congrArg Norm.Basic.normSq scaled).trans (normSq_scale width direction)
  have rows (row : Fin 2) :
      Norm.Basic.normSq (Euler.defect (alongMatrix parameter direction) width values
        (map Certificate.output entries) row) ≤
        2 * ((entries row).factor * Norm.Basic.normSq direction ^ 2 + Norm.Basic.normSq direction) * width ^ 4 := by
    let acted := matrixVector (matrix parameter) values row
    have slopeBound := sourceSlope_le jet width start index selection after values (entries row).slope row
      values_eq (slope_eq row)
    have movement : scale width (direction * acted) = increment * acted :=
      (scale_mul_product width direction acted).trans (congrArg (fun value : Canonical => value * acted) scaled.symm)
    have exactRow : Euler.defect (alongMatrix parameter direction) width values
        (map Certificate.output entries) row =
        (entries row).remainder + increment * ((entries row).slope - acted) := by
      unfold Euler.defect
      rewrite [zipWith_apply, map_apply, Euler.step_apply, alongMatrix_vector, movement]
      have original := (entries row).expansion
      change (entries row).output - (values row + increment * acted) = _
      rewrite [show values row = (entries row).base from map_apply Certificate.base entries row]
      exact (show (entries row).output - ((entries row).base + increment * acted) =
        ((entries row).output - (entries row).base - increment * (entries row).slope) +
          increment * ((entries row).slope - acted) by ring1).trans
            (congrArg (fun value : Canonical => value + increment * ((entries row).slope - acted)) original)
    have original : Norm.Basic.normSq (entries row).remainder ≤
        (entries row).factor * Norm.Basic.normSq increment ^ 2 :=
      ((Norm.Basic.normSq_eq_canonical _).trans_le (entries row).remainder_le).trans_eq
        (congrArg (fun value : Rational => (entries row).factor * value ^ 2)
          (Norm.Basic.normSq_eq_canonical increment).symm)
    have remainderBound : Norm.Basic.normSq (entries row).remainder ≤
        (entries row).factor * Norm.Basic.normSq direction ^ 2 * width ^ 4 :=
      original.trans_eq ((congrArg (fun value : Rational => (entries row).factor * value ^ 2)
        incrementNorm).trans (by ring1))
    have slopeContribution : Norm.Basic.normSq (increment * ((entries row).slope - acted)) ≤
        Norm.Basic.normSq direction * width ^ 4 :=
      (Norm.Basic.normSq_mul _ _).trans_le
        ((mul_le_mul_of_nonneg_left_direct slopeBound (Norm.Basic.normSq_nonneg increment)).trans_eq
          ((congrArg (fun value : Rational => value * width ^ 2) incrementNorm).trans (by ring1)))
    exact (congrArg Norm.Basic.normSq exactRow).trans_le
      ((Norm.Bounds.normSq_add_le_two _ _).trans
        ((mul_le_mul_of_nonneg_left_direct (add_le_add_direct remainderBound slopeContribution)
          (by decide : (0 : Rational) ≤ 2)).trans_eq (by ring1)))
  have summed := add_le_add_direct (rows 0) (rows 1)
  have same : Norm.vector (Euler.defect (alongMatrix parameter direction) width values
      (map Certificate.output entries)) =
      Norm.Basic.normSq (Euler.defect (alongMatrix parameter direction) width values
        (map Certificate.output entries) 0) +
      Norm.Basic.normSq (Euler.defect (alongMatrix parameter direction) width values
        (map Certificate.output entries) 1) := by
    unfold Norm.vector
    rewrite [sumFin_succ, sumFin_succ]
    let actual := Euler.defect (alongMatrix parameter direction) width values (map Certificate.output entries)
    change Norm.Basic.normSq (actual 0) + (Norm.Basic.normSq (actual 1) + 0) =
      Norm.Basic.normSq (actual 0) + Norm.Basic.normSq (actual 1)
    ring1
  exact same.trans_le (summed.trans_eq (by unfold eulerFactor; ring1))

end Purelib.Curves.Legendre.Periods.Jets.Connection

end
