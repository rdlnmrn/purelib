module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Rational.Squares
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.List.Sum
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Finite primitive comparison for actual path samples

Telescoping is supplied by the geometry of a connected path.  The comparison
then uses finite Cauchy--Schwarz, retaining both occurrences of the cell count
when each cell has a uniform squared-error bound.  Dyadic cancellation pays
that count exactly; it is not a fixed-list convergence argument.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Primitive

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Sum the original cells' primitive endpoint differences in retained path order. -/
@[expose] def incrementSum (primitive : Basic.Canonical → Basic.Canonical) : List Basic.CellModel → Basic.Canonical
  | [] => 0
  | cell :: cells => primitive cell.finish - primitive cell.start +
    Purelib.Integration.Polynomial.Gaussian.Path.Primitive.incrementSum primitive cells

open Purelib.Integration in
open Purelib.Data in
/-- Primitive increments over concatenated cell lists add their two totals.

Structural recursion retains the ordered cells of both lists and separates
the current primitive increment from the unchanged tail. -/
theorem incrementSum_append (primitive : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical)
    (first second : List Polynomial.Gaussian.Cell.Basic.CellModel) :
    incrementSum primitive (first ++ second) =
      incrementSum primitive first + incrementSum primitive second := by
  induction first with
  | nil =>
      change incrementSum primitive second = 0 + incrementSum primitive second
      ring1
  | cons head tail ih =>
      simp only [List.cons_append, incrementSum, ih]
      ring1

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Read each original cell's primitive endpoint difference minus its exact integral sample. -/
@[expose] def errorTerms (primitive : Basic.Canonical → Basic.Canonical) (cells : List Basic.CellModel) : List
  Basic.Canonical :=
  cells.map fun cell => primitive cell.finish - primitive cell.start - cell.integralSample

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original error sum equals the primitive-increment sum minus the original path sample. -/
theorem errorTerms_sum (primitive : Basic.Canonical → Basic.Canonical) (cells : List Basic.CellModel) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (Primitive.errorTerms primitive cells) =
      Primitive.incrementSum primitive cells - (Basic.PathModel.mk cells).integralSample := by
  induction cells with
  | nil => change (0 : Basic.Canonical) = 0 - 0; ring1
  | cons cell cells ih =>
      change (primitive cell.finish - primitive cell.start - cell.integralSample) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (Primitive.errorTerms primitive cells) =
          (primitive cell.finish - primitive cell.start + Primitive.incrementSum primitive cells) -
            (cell.integralSample + (Basic.PathModel.mk cells).integralSample)
      rw [ih]
      ring1

section
open Purelib.Algebra
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Original per-cell error certificates bound the total squared-norm error mass by the retained budget sum. -/
private theorem errors_bounded (primitive : Basic.Canonical → Basic.Canonical) (budget : Basic.CellModel →
  Fraction.Rational)
    (cells : List Basic.CellModel)
    (bounded : ∀ cell ∈ cells,
      Basic.Canonical.normSq (primitive cell.finish - primitive cell.start - cell.integralSample) ≤ budget cell) :
    Norm.Sum.Basic.gaussianNormSqSum (Primitive.errorTerms primitive cells) ≤ FiniteSum.Rational.Squares.coordinateSum
      (cells.map budget) := by
  induction cells with
  | nil => exact le_rfl
  | cons cell cells ih =>
      exact add_le_add (bounded cell (List.mem_cons_self ..))
        (ih fun other member => bounded other (List.mem_cons_of_mem cell member))

/-- A telescoping original primitive path has integral error controlled by its retained per-cell budgets.

The estimate keeps the exact original cell count and budget sum, using the supplied endpoint telescoping identity. -/
theorem integral_error_le (primitive : Basic.Canonical → Basic.Canonical) (path : Basic.PathModel)
    {start finish : Basic.Canonical}
    (telescopes : Primitive.incrementSum primitive path.cells = primitive finish - primitive start)
    (budget : Basic.CellModel → Fraction.Rational)
    (bounded : ∀ cell ∈ path.cells,
      Basic.Canonical.normSq (primitive cell.finish - primitive cell.start - cell.integralSample) ≤ budget cell) :
    Basic.Canonical.normSq (primitive finish - primitive start - path.integralSample) ≤
      (path.cells.length : Fraction.Rational) * FiniteSum.Rational.Squares.coordinateSum (path.cells.map budget) := by
  rw [← telescopes, ← Primitive.errorTerms_sum]
  have sumBound := Norm.Sum.Basic.normSq_gaussianSum_le (Primitive.errorTerms primitive path.cells)
  rewrite [Primitive.errorTerms, Purelib.Data.List.Map.length_map] at sumBound
  exact sumBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Primitive.errors_bounded primitive budget path.cells bounded)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- A common original cell error budget bounds the path's integral error by cell count squared times that budget.

The exact original endpoint telescoping certificate and retained cell membership bounds are preserved. -/
theorem integral_error_le_uniform (primitive : Basic.Canonical → Basic.Canonical) (path : Basic.PathModel)
    {start finish : Basic.Canonical}
    (telescopes : Primitive.incrementSum primitive path.cells = primitive finish - primitive start)
    (budget : Fraction.Rational)
    (bounded : ∀ cell ∈ path.cells,
      Basic.Canonical.normSq (primitive cell.finish - primitive cell.start - cell.integralSample) ≤ budget) :
    Basic.Canonical.normSq (primitive finish - primitive start - path.integralSample) ≤
      (path.cells.length : Fraction.Rational) * ((path.cells.length : Fraction.Rational) * budget) := by
  have bound := Primitive.integral_error_le primitive path telescopes (fun _ => budget) bounded
  rewrite [List.Sum.constantSum] at bound
  exact bound
end Purelib.Integration.Polynomial.Gaussian.Path.Primitive
