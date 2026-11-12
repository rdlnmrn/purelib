module

public import Purelib.Integration.Path.Primitive.Polynomial
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Primitive comparisons at shared original lifted vertices

Each actual integration cell retains its own polynomial primitive and
compares its two finite values with canonical readings at the same original
lifted vertices. Adjacent cells share the vertex reading, including across
charts. Finite telescoping then uses original lifted endpoint closure.
-/

public section

namespace Purelib.Integration.Path.Primitive.PrimitiveEdge.CellEndpoints

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Path.Gaussian.Lifted.Basic
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

set_option genInjectivity false in
/-- Local primitive comparisons following the exact original lifted path and original ordered integration cells.

Each local primitive may belong to a different chart. Its endpoint errors
refer to the same retained vertex function on both sides of every join,
and its residual ceiling is checked on the actual cell polynomial. -/
inductive Cells {sheets : Nat} (endpoint : LiftedPoint sheets → Basic.Canonical)
    (localBound endpointBound : Fraction.Rational) :
    {start finish : LiftedPoint sheets} → List Cell.Basic.CellModel → LiftedPath sheets start finish → Type
  /-- The original empty lifted path retains its same vertex reading. -/
  | nil (point : LiftedPoint sheets) : Cells endpoint localBound endpointBound [] (.nil point)
  /-- Prepend the original cell, its exact geometric occurrence and its local primitive comparison. -/
  | cons {start middle finish : LiftedPoint sheets} {remaining : List Cell.Basic.CellModel}
      {path : LiftedPath sheets middle finish}
      (cell : Cell.Basic.CellModel) (lifted : LiftedCell start middle)
      (start_eq : cell.start = start.coordinate) (finish_eq : cell.finish = middle.coordinate)
      (comparison : Cell.Primitive.Comparison cell)
      (local_le : comparison.bound ≤ localBound)
      (start_le : Norm.Basic.normSq (comparison.value.eval 0 - endpoint start) ≤ endpointBound)
      (finish_le : Norm.Basic.normSq (comparison.value.eval 1 - endpoint middle) ≤ endpointBound)
      (tail : Cells endpoint localBound endpointBound remaining path) :
      Cells endpoint localBound endpointBound (cell :: remaining) (.cons lifted path)

constructive_injectivity Cells

namespace Cells

variable {sheets : Nat} {endpoint : LiftedPoint sheets → Basic.Canonical}
  {localBound endpointBound : Fraction.Rational}
  {start finish : LiftedPoint sheets} {cells : List Cell.Basic.CellModel}
  {path : LiftedPath sheets start finish}

/-- Retain the exact original per-occurrence primitive endpoint defect in ordered cell order. -/
@[expose] def errorTerms : {start finish : LiftedPoint sheets} →
    {cells : List Cell.Basic.CellModel} → {path : LiftedPath sheets start finish} →
    Cells endpoint localBound endpointBound cells path → List Basic.Canonical
  | _, _, _, _, .nil _ => []
  | _, _, _, _, .cons (start := left) (middle := right) cell _ _ _ _ _ _ _ tail =>
      (endpoint right - endpoint left - cell.integralSample) :: tail.errorTerms

/-- The retained defect list has exactly the original integration cell count. -/
theorem errorTerms_length (chain : Cells endpoint localBound endpointBound cells path) :
    chain.errorTerms.length = cells.length := by
  induction chain with
  | nil point => rfl
  | cons cell lifted start_eq finish_eq comparison local_le start_le finish_le tail ih =>
      change tail.errorTerms.length + 1 = _
      rw [ih]
      rfl

/-- The retained defects telescope at the original lifted vertices to the endpoint difference minus actual integral. -/
theorem errorTerms_sum (chain : Cells endpoint localBound endpointBound cells path) :
    Norm.Sum.Basic.gaussianSum chain.errorTerms = endpoint finish - endpoint start -
      (Path.Basic.PathModel.mk cells).integralSample := by
  induction chain with
  | nil point =>
      change (0 : Basic.Canonical) = endpoint point - endpoint point - 0
      ring1
  | cons cell lifted start_eq finish_eq comparison local_le start_le finish_le tail ih =>
      change endpoint _ - endpoint _ - cell.integralSample + Norm.Sum.Basic.gaussianSum tail.errorTerms =
        endpoint _ - endpoint _ - (cell.integralSample + (Path.Basic.PathModel.mk _).integralSample)
      rw [ih]
      ring1

/-- Local derivative residual and endpoint defects bound one actual cell's integral against shared vertex readings. -/
theorem cell_error_le {cell : Cell.Basic.CellModel} (comparison : Cell.Primitive.Comparison cell)
    {left right : Basic.Canonical} (local_le : comparison.bound ≤ localBound)
    (start_le : Norm.Basic.normSq (comparison.value.eval 0 - left) ≤ endpointBound)
    (finish_le : Norm.Basic.normSq (comparison.value.eval 1 - right) ≤ endpointBound) :
    Norm.Basic.normSq (right - left - cell.integralSample) ≤ 4 * localBound + 8 * endpointBound := by
  have localEstimate := comparison.integral_error_le
  have endpointError : Norm.Basic.normSq
      ((right - left) - (comparison.value.eval 1 - comparison.value.eval 0)) ≤ 4 * endpointBound := by
    rw [show (right - left) - (comparison.value.eval 1 - comparison.value.eval 0) =
      (comparison.value.eval 0 - left) - (comparison.value.eval 1 - right) by ring1]
    exact (Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add start_le finish_le) (by decide)).trans (le_of_eq (by ring1)))
  rw [show right - left - cell.integralSample =
    ((right - left) - (comparison.value.eval 1 - comparison.value.eval 0)) +
      (comparison.value.eval 1 - comparison.value.eval 0 - cell.integralSample) by ring1]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add endpointError (localEstimate.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct local_le (by decide))))
        (by decide)).trans (le_of_eq (by ring1)))

/-- Sum the actual ordered cell defects' squared norms with the retained common local ceilings. -/
theorem errorTerms_normMass (chain : Cells endpoint localBound endpointBound cells path) :
    Norm.Sum.Basic.gaussianNormSqSum chain.errorTerms ≤
      (cells.length : Fraction.Rational) * (4 * localBound + 8 * endpointBound) := by
  induction chain with
  | nil point =>
      change (0 : Fraction.Rational) ≤ 0 * _
      rw [Fraction.Field.zero_mul_direct]
  | cons cell lifted start_eq finish_eq comparison local_le start_le finish_le tail ih =>
      change Basic.Canonical.normSq (endpoint _ - endpoint _ - cell.integralSample) +
        Norm.Sum.Basic.gaussianNormSqSum tail.errorTerms ≤ _
      rw [← Norm.Basic.normSq_eq_canonical]
      have bound := cell_error_le comparison local_le start_le finish_le
      have total := add_le_add bound ih
      rw [List.length_cons, Algebra.NatCast.add, Nat.cast_one]
      exact total.trans (le_of_eq (by ring1))

/-- Original finite Cauchy–Schwarz and shared lifted vertices derive the complete original path integral error. -/
theorem integral_error_le (chain : Cells endpoint localBound endpointBound cells path) :
    Norm.Basic.normSq
        ((Path.Basic.PathModel.mk cells).integralSample - (endpoint finish - endpoint start)) ≤
      (cells.length : Fraction.Rational) *
        ((cells.length : Fraction.Rational) * (4 * localBound + 8 * endpointBound)) := by
  have cauchy := Norm.Sum.Basic.normSq_gaussianSum_le chain.errorTerms
  rw [← Norm.Basic.normSq_eq_canonical, chain.errorTerms_sum, chain.errorTerms_length] at cauchy
  rw [Norm.Bounds.normSq_sub_symm]
  exact cauchy.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    chain.errorTerms_normMass (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))

/-- The local primitive comparison chain retains the actual original lifted-path following witnesses. -/
theorem follows (chain : Cells endpoint localBound endpointBound cells path) : LiftedPath.FollowedBy cells path := by
  induction chain with
  | nil point => exact .nil point
  | cons cell lifted start_eq finish_eq comparison local_le start_le finish_le tail ih =>
      exact .cons start_eq finish_eq ih

end Cells

set_option genInjectivity false in
/-- Per-stage shared-vertex primitive comparisons on one original whole integration program.

The actual stage path and cells remain indexed by the original program.
Different cells retain different polynomial primitives. The two original
endpoint sample streams agree with the shared vertex readings, and a finite
count-paid budget bounds the whole original program comparison. -/
structure Models {sheets : Nat} (start finish : LiftedPoint sheets)
    (startSource finishSource : GeometricApproximation)
    (program : Integration.Program.Comparison.RefinementProgram) where
  /-- The same original displayed lifted path at every actual program stage. -/
  lifted : Nat → LiftedPath sheets start finish
  /-- Shared canonical primitive readings at all original lifted vertices of one stage. -/
  endpoint : Nat → LiftedPoint sheets → Basic.Canonical
  /-- The original starting endpoint stream is the retained stage's starting vertex reading. -/
  startReadback : ∀ index, endpoint index start = startSource.sample index
  /-- The original finishing endpoint stream is the retained stage's finishing vertex reading. -/
  finishReadback : ∀ index, endpoint index finish = finishSource.sample index
  /-- The retained finite per-cell derivative residual ceiling. -/
  localBound : Nat → Fraction.Rational
  /-- The retained finite original-root endpoint comparison ceiling. -/
  endpointBound : Nat → Fraction.Rational
  /-- The actual ordered cell comparison chain on the original lifted stage path. -/
  comparisons : ∀ index,
    Cells (endpoint index) (localBound index) (endpointBound index) (program.model index).cells (lifted index)
  /-- The retained whole-program geometric comparison scale. -/
  scale : Fraction.Rational
  /-- The original comparison scale is nonnegative. -/
  scale_nonnegative : 0 ≤ scale
  /-- The finite actual cell count pays all local derivative and original-root endpoint errors. -/
  budget_le : ∀ index,
    ((program.model index).cells.length : Fraction.Rational) *
        (((program.model index).cells.length : Fraction.Rational) *
          (4 * localBound index + 8 * endpointBound index)) ≤ quarterRadius scale index

constructive_injectivity Models

namespace Models

/-- The original whole-program samples are close to the retained original endpoint difference by finite telescoping. -/
theorem sample_error_le {sheets : Nat} {start finish : LiftedPoint sheets}
    {startSource finishSource : GeometricApproximation}
    {program : Integration.Program.Comparison.RefinementProgram}
    (models : Models start finish startSource finishSource program) (index : Nat) :
    Norm.Basic.normSq
        ((program.model index).integralSample - (finishSource.sample index - startSource.sample index)) ≤
      quarterRadius models.scale index := by
  have bound := (models.comparisons index).integral_error_le
  rw [models.startReadback index, models.finishReadback index] at bound
  exact bound.trans (models.budget_le index)

/-- Construct the original whole-program primitive edge from actual local chart models and shared vertex readings. -/
def edge {sheets : Nat} {start finish : LiftedPoint sheets}
    {startSource finishSource : GeometricApproximation}
    {program : Integration.Program.Comparison.RefinementProgram}
    (models : Models start finish startSource finishSource program) :
    PrimitiveEdge (Riemann.Periods.PeriodMatrix.geometricNamed startSource)
      (Riemann.Periods.PeriodMatrix.geometricNamed finishSource) :=
  ofSampleComparison startSource finishSource program models.scale models.scale_nonnegative models.sample_error_le

/-- The whole-stage primitive edge preserves the exact original integration program. -/
theorem edge_program {sheets : Nat} {start finish : LiftedPoint sheets}
    {startSource finishSource : GeometricApproximation}
    {program : Integration.Program.Comparison.RefinementProgram}
    (models : Models start finish startSource finishSource program) :
    models.edge.program = program := by
  unfold edge
  exact ofSampleComparison_program _ _ _ _ _ _

end Models
end Purelib.Integration.Path.Primitive.PrimitiveEdge.CellEndpoints
