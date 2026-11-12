module

public import Purelib.Curves.Legendre.Paths.AxisSegment
public import Purelib.Curves.Legendre.Periods.Jets.Connection.Euler
public import Purelib.Calculus.Linear.Euler.Blocks
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Algebra.Recurrence.Affine.Constant
import Purelib.Tactic.Ring

/-! # Independent connection execution on whole safe Legendre axes

The original whole-axis clearances give one coefficient ceiling before
choosing the Euler grid. The executor retains its actual coarse count,
fine count and endpoint. Its stability compares two independently supplied
initial vectors; no geometric period or monodromy matrix defines a value.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment

open Purelib
open Purelib.Calculus.Linear
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Scale (scale normSq_scale)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Data.Vector (zipWith)
open Purelib.LinearAlgebra (Matrix)
open Purelib.LinearAlgebra.Gaussian

variable {start finish : Canonical} (segment : AxisSegment start finish)

/-- The original direction-scaled connection coefficients on the displayed uniform axis grid. -/
@[expose] def connectionCoefficients (count index : Nat) : Matrix Canonical 2 :=
  Connection.alongMatrix (segment.pointAt ((index : Rational) / (count : Rational))) (finish - start)

namespace Safe

variable {segment} (safe : Safe segment)

/-- The actual two whole-axis distance floors give a uniform connection matrix ceiling. -/
@[expose] def connectionMatrixCeiling : Rational :=
  4 * ((segment.quadranceCeiling + 1) *
    (4 * safe.avoidsZero.bound * safe.avoidsOne.bound)⁻¹)

/-- The whole-axis matrix ceiling is nonnegative from the two retained positive clearances. -/
theorem connectionMatrixCeiling_nonnegative : 0 ≤ safe.connectionMatrixCeiling :=
  mul_nonneg_direct (by decide +kernel)
    (mul_nonneg_direct
      (add_pos_of_nonneg_of_pos_direct segment.quadranceCeiling_nonnegative (by decide +kernel)).le
      (Order.Field.inv_pos_direct
        (mul_pos_direct (mul_pos_direct (by decide +kernel) safe.avoidsZero.positive)
          safe.avoidsOne.positive)).le)

/-- The original safe-axis clearances bound the actual connection matrix throughout the entire unit interval. -/
theorem connectionMatrix_le (fraction : Rational) (nonnegative : 0 ≤ fraction) (unit : fraction ≤ 1) :
    Norm.matrix (Connection.matrix (segment.pointAt fraction)) ≤ safe.connectionMatrixCeiling :=
  Connection.matrix_le_of_clearance (ParameterClearance.ofAxisSegmentPoint safe fraction nonnegative unit)
    segment.quadranceCeiling (segment.pointAt_normSq_le fraction nonnegative unit)

/-- The oriented axis Jacobian multiplies the same retained whole-axis matrix ceiling. -/
@[expose] def connectionCoefficientCeiling : Rational :=
  Norm.Basic.normSq (finish - start) * safe.connectionMatrixCeiling

/-- The actual direction-scaled coefficient ceiling is nonnegative for every safe axis. -/
theorem connectionCoefficientCeiling_nonnegative : 0 ≤ safe.connectionCoefficientCeiling :=
  mul_nonneg_direct (Norm.Basic.normSq_nonneg (finish - start)) safe.connectionMatrixCeiling_nonnegative

/-- Every actual finite grid coefficient is bounded by the same precomputed whole-axis ceiling. -/
theorem connectionCoefficients_le (count : Nat) (positive : 0 < count) (index : Nat) (before : index < count) :
    Norm.matrix (segment.connectionCoefficients count index) ≤ safe.connectionCoefficientCeiling := by
  have denominator := Cast.Order.natCast_pos_direct (n := count) positive
  have nonnegative : (0 : Rational) ≤ (index : Rational) / (count : Rational) :=
    Order.Field.div_nonneg_direct (Cast.Order.natCast_le_direct (m := 0) (n := index) (Nat.zero_le index))
      denominator.le
  have unit : (index : Rational) / (count : Rational) ≤ 1 :=
    (Order.Field.div_le_iff_pos denominator).mpr
      ((Cast.Order.natCast_le_direct (m := index) (n := count) (Nat.le_of_lt before)).trans_eq
        (Field.one_mul _).symm)
  exact (Connection.alongMatrix_norm _ _).trans_le
    (mul_le_mul_of_nonneg_left_direct (safe.connectionMatrix_le _ nonnegative unit)
      (Norm.Basic.normSq_nonneg (finish - start)))

/-- The actual selected coarse/fine counts and independently computed Euler endpoint with their whole factories.

The coarse subtype binds the original interval selector. The fine count
retains that coarse count times the requested refinement and its positive
bound. The endpoint retains the full execution on that same grid.
-/
@[expose] def ConnectionPreparation (refinement : Nat) (initial : Vec Canonical 2) : Type _ :=
  Σ coarse : {value : Nat // value = Euler.intervalCount 2 safe.connectionCoefficientCeiling
      safe.connectionCoefficientCeiling_nonnegative},
  Σ count : {value : Nat // value = coarse.val * refinement ∧ 0 < value},
    {value : Vec Canonical 2 // value = Euler.trace (segment.connectionCoefficients count.val)
      (fun _ => 1 / (count.val : Rational)) initial count.val}

/-- Construct the independent axis connection endpoint from its actual clearances and a positive refinement.

The original interval selector runs once. The fine count is retained
before one original Euler execution; each original coefficient matrix is
materialized once per step. No root acquisition or period reading occurs.
-/
def prepareConnection (refinement : Nat) (positive : 0 < refinement) (initial : Vec Canonical 2) :
    safe.ConnectionPreparation refinement initial :=
  let coarse := Euler.intervalCount 2 safe.connectionCoefficientCeiling
    safe.connectionCoefficientCeiling_nonnegative
  let count := coarse * refinement
  let value := Euler.trace (segment.connectionCoefficients count) (fun _ => 1 / (count : Rational)) initial count
  ⟨⟨coarse, rfl⟩, ⟨count, rfl, Nat.mul_pos (Euler.intervalCount_positive 2 _ _) positive⟩, ⟨value, rfl⟩⟩

namespace ConnectionPreparation

variable {safe} {refinement : Nat} {initial : Vec Canonical 2}
variable (prepared : safe.ConnectionPreparation refinement initial)

/-- Read the same computed coarse count without repeating its interval search. -/
@[expose] def coarse : Nat := prepared.1.val

/-- The retained coarse count is its whole original interval-selector result. -/
theorem coarse_eq : prepared.coarse = Euler.intervalCount 2 safe.connectionCoefficientCeiling
    safe.connectionCoefficientCeiling_nonnegative := prepared.1.property

/-- Read the same actual fine count retained before coefficient execution. -/
@[expose] def count : Nat := prepared.2.1.val

/-- The same retained fine count is the selected coarse count times the actual requested refinement. -/
theorem count_eq : prepared.count =
    Euler.intervalCount 2 safe.connectionCoefficientCeiling safe.connectionCoefficientCeiling_nonnegative *
      refinement :=
  prepared.2.1.property.1.trans (congrArg (fun value : Nat => value * refinement) prepared.coarse_eq)

/-- The actual retained grid has a positive fine count. -/
theorem count_positive : 0 < prepared.count := prepared.2.1.property.2

/-- Read the same independently executed connection endpoint. -/
@[expose] def value : Vec Canonical 2 := prepared.2.2.val

/-- The retained endpoint is its original whole Euler execution on the retained actual grid. -/
theorem value_eq : prepared.value = Euler.trace (segment.connectionCoefficients prepared.count)
    (fun _ => 1 / (prepared.count : Rational)) initial prepared.count := prepared.2.2.property

/-- Exact count transport reads the same endpoint on the original selected grid without executing it again. -/
theorem trace_eq : prepared.value =
    let count := Euler.intervalCount 2 safe.connectionCoefficientCeiling
      safe.connectionCoefficientCeiling_nonnegative * refinement
    Euler.trace (segment.connectionCoefficients count) (fun _ => 1 / (count : Rational)) initial count :=
  prepared.value_eq.trans (congrArg (fun count : Nat =>
    Euler.trace (segment.connectionCoefficients count) (fun _ => 1 / (count : Rational)) initial count)
      prepared.count_eq)

/-- A stationary original axis leaves the same initial vector unchanged at every retained refinement. -/
theorem stationary_value (same : finish = start) : prepared.value = initial := by
  have direction : finish - start = 0 :=
    (congrArg (fun value : Canonical => value - start) same).trans (Basic.sub_self start)
  have zero (index : Nat) (_before : index < prepared.count) (row : Fin 2) :
      Matrix.Multiplication.matrixVector (segment.connectionCoefficients prepared.count index) initial row = 0 := by
    unfold connectionCoefficients
    rewrite [direction]
    exact Connection.alongMatrix_zero_vector _ _ _
  exact prepared.value_eq.trans
    (Euler.trace_eq_of_action_zero (segment.connectionCoefficients prepared.count)
      (fun _ => 1 / (prepared.count : Rational)) initial prepared.count zero)

/-- Actual whole-axis clearances derive finite initial-value stability between two retained independent executions.

Both original initial vectors and endpoint caches remain separate.
The coefficient ceiling and coarse interval count pay growth internally;
the actual original traces have zero local defects.
-/
theorem difference_le (positive : 0 < refinement) {otherInitial : Vec Canonical 2}
    (other : safe.ConnectionPreparation refinement otherInitial) :
    Norm.vector (zipWith (fun first last => first - last) prepared.value other.value) ≤
      Algebra.Recurrence.Affine.iterate (fun _ => 2) (fun _ => 0) 1
        (Euler.intervalCount 2 safe.connectionCoefficientCeiling safe.connectionCoefficientCeiling_nonnegative) *
      Norm.vector (zipWith (fun first last => first - last) initial otherInitial) := by
  let coarse := Euler.intervalCount 2 safe.connectionCoefficientCeiling
    safe.connectionCoefficientCeiling_nonnegative
  have bound := Euler.trace_difference_blocks_le (segment.connectionCoefficients (coarse * refinement))
    initial otherInitial safe.connectionCoefficientCeiling safe.connectionCoefficientCeiling_nonnegative
    refinement positive (fun index before => safe.connectionCoefficients_le (coarse * refinement)
      (Nat.mul_pos (Euler.intervalCount_positive 2 _ _) positive) index before)
  have same := congrArg₂ (fun first last : Vec Canonical 2 =>
    Norm.vector (zipWith (fun left right => left - right) first last) ≤
      Algebra.Recurrence.Affine.iterate (fun _ => 2) (fun _ => 0) 1 coarse *
        Norm.vector (zipWith (fun left right => left - right) initial otherInitial))
    prepared.trace_eq other.trace_eq
  exact Eq.mpr same bound

/-- Compute the original finite growth factor from the retained coarse count without another interval selection. -/
@[expose] def amplification : Rational :=
  Algebra.Recurrence.Affine.iterate (fun _ => 2) (fun _ => 0) 1 prepared.coarse

/-- The cached coarse-count amplification is nonnegative. -/
theorem amplification_nonnegative : 0 ≤ prepared.amplification :=
  Algebra.Recurrence.Affine.iterate_nonnegative _ _ _ _ (by decide +kernel)
    (fun _ _ => by decide +kernel) (fun _ _ => by decide +kernel)

/-- Two retained axis endpoints satisfy initial-value stability with the first cache's actual growth factor. -/
theorem difference_le_amplification (positive : 0 < refinement) {otherInitial : Vec Canonical 2}
    (other : safe.ConnectionPreparation refinement otherInitial) :
    Norm.vector (zipWith (fun first last => first - last) prepared.value other.value) ≤
      prepared.amplification * Norm.vector (zipWith (fun first last => first - last) initial otherInitial) := by
  have bound := prepared.difference_le positive other
  have same := congrArg (fun count : Nat =>
    Norm.vector (zipWith (fun first last => first - last) prepared.value other.value) ≤
      Algebra.Recurrence.Affine.iterate (fun _ => 2) (fun _ => 0) 1 count *
        Norm.vector (zipWith (fun first last => first - last) initial otherInitial)) prepared.coarse_eq
  exact Eq.mpr same bound

end ConnectionPreparation

end Safe

end Purelib.Curves.Legendre.Paths.AxisSegment

end
