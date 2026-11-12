module

public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison.Powers
public import Purelib.Riemann.Normalization.RectangularInverseModels
public import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order

/-! # Original overlap bounds cached over one retained rectangular geometry

Every original cell keeps its actual clearance/numerator cache in a finite
stored vector. Its finite power-scale sum is available before selecting a
source or grid refinement stage. A later literal cell selection reads the
same stored cache, including its original complete factory equation.
-/

public section

namespace Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds

open Purelib
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Algebra.FiniteSum.Rational.Order (weight_le_sum weight_sum_nonnegative)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Box)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)

variable {polynomial : Polynomial} {ambient : Box} {columns rows : Nat}

/-- The original numerator bounds materialized once at every cell of the SAME rectangular geometry.

The outer vector stores columns and the inner vector stores rows. Every
entry retains its original restricted-clearance owner. No source model,
reading, stage, Point or chosen cell is needed to construct the cache.
-/
abbrev Rectangular (clearance : RegionClearance polynomial ambient) (geometry : Geometry columns rows)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) (numerator : Polynomial) :=
  DependentVector (fun column : Fin (columns + 1) =>
    DependentVector (fun row : Fin (rows + 1) =>
      PrimitiveOverlapBounds (clearance.restrict (refines column row)) numerator))

namespace Rectangular

variable {clearance : RegionClearance polynomial ambient} {geometry : Geometry columns rows}
    {refines : ∀ column row, (geometry.box column row).Refines ambient} {numerator : Polynomial}

/-- Construct every original cell bound once, before any later numerical stage selection. -/
def build (clearance : RegionClearance polynomial ambient) (geometry : Geometry columns rows)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) (numerator : Polynomial) :
    Rectangular clearance geometry refines numerator :=
  DependentVector.ofFn (fun column => DependentVector.ofFn (fun row =>
    PrimitiveOverlapBounds.build (clearance.restrict (refines column row)) numerator))

/-- Read the SAME original bound at its retained column and row, without reconstructing that entry. -/
abbrev entry (cached : Rectangular clearance geometry refines numerator)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    PrimitiveOverlapBounds (clearance.restrict (refines column row)) numerator :=
  (cached.get column).get row

/-- The actual selected cache retains its complete original cell-bound factory. -/
theorem build_entry (clearance : RegionClearance polynomial ambient) (geometry : Geometry columns rows)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) (numerator : Polynomial)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    entry (build clearance geometry refines numerator) column row =
      PrimitiveOverlapBounds.build (clearance.restrict (refines column row)) numerator := by
  unfold entry build
  rewrite [DependentVector.ofFn_get, DependentVector.ofFn_get]
  rfl

/-- A retained whole-cache factory equation gives that SAME selected entry's original factory equation. -/
theorem entry_eq_of_factory (cached : Rectangular clearance geometry refines numerator)
    (factory : cached = build clearance geometry refines numerator)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    entry cached column row = PrimitiveOverlapBounds.build (clearance.restrict (refines column row)) numerator :=
  (congrArg (fun value : Rectangular clearance geometry refines numerator => entry value column row) factory).trans
    (build_entry clearance geometry refines numerator column row)

/-- Sum every actual cached power scale over the literal original cells before choosing numerical stages. -/
def powerScale (cached : Rectangular clearance geometry refines numerator) (exponent : Nat) : Rational :=
  sumFin (fun column : Fin (columns + 1) =>
    sumFin (fun row : Fin (rows + 1) => (entry cached column row).powerScale exponent))

/-- Every actual finite rectangular power-scale sum is nonnegative. -/
theorem powerScale_nonnegative (cached : Rectangular clearance geometry refines numerator) (exponent : Nat) :
    0 ≤ cached.powerScale exponent :=
  weight_sum_nonnegative _ (fun column => weight_sum_nonnegative _
    (fun row => (entry cached column row).powerScale_nonnegative exponent))

/-- Each actual retained cell power scale is at most the same complete pre-stage rectangular sum. -/
theorem entry_powerScale_le (cached : Rectangular clearance geometry refines numerator) (exponent : Nat)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (entry cached column row).powerScale exponent ≤ cached.powerScale exponent :=
  (weight_le_sum (fun row : Fin (rows + 1) => (entry cached column row).powerScale exponent)
    (fun row => (entry cached column row).powerScale_nonnegative exponent) row).trans
      (weight_le_sum (fun column : Fin (columns + 1) =>
        sumFin (fun row : Fin (rows + 1) => (entry cached column row).powerScale exponent))
        (fun column => weight_sum_nonnegative _
          (fun row => (entry cached column row).powerScale_nonnegative exponent)) column)

end Rectangular

end Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds

end
