module
import Purelib.Data.Nat.Order

import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Approximation.Rational.Geometric.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

@[expose] public section

/-!
# Synchronizing scalar grid budgets before polynomial construction

An explicitly supplied later index changes only the scalar residual bounds.
It is retained literally, so shared polynomial data have the same dependent
index across independently budgeted segment occurrences.
-/

section

open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)

open Purelib.Riemann.Normalization.InverseRootPolynomial

variable {polynomial numerator : Purelib.Riemann.Normalization.InverseRootPolynomial.Polynomial} {ambient :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box} {clearance :
  Purelib.Riemann.Comparison.PrimitiveEdgeComparison.RegionClearance polynomial ambient}
  {bounds : Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance numerator} {columns
    fragments : Nat} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

section

namespace Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy

open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Integration in
open Purelib.Data.Nat in
/-- Raise the grid request to the supplied index known to be at least its original index.

The construction uses the existing refinement operation and retains the exact requested index with its updated bounds.
-/
def atIndex (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns target) (index : Nat) (later :
  request.index ≤ index) :
    RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns target :=
  let raised := Accuracy.Fragment.GridPrimitiveAccuracy.atLeast request index
  { raised with index := index
                edgeBound_eq := by
                  rw [raised.edgeBound_eq]
                  have maximum : max index request.index = index :=
                    (Order.max_eq_natMax index request.index).trans
                      (Nat.le_antisymm
                        (Order.max_le (Nat.le_refl index) later)
                        (Order.le_max_left index request.index))
                  exact congrArg _ maximum
                globalBound_eq := raised.globalBound_eq }

open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Integration in
/-- The refined grid request has exactly the supplied index. -/
theorem atIndex_index (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns target) (index : Nat)
  (later : request.index ≤ index) :
    (atIndex request index later).index = index := rfl

end Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy

end

section

open Purelib.Integration.Polynomial.Rectangle

namespace Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy

/-- Raise only the retained fragment budget's grid request to a later index.

The original fragment allocation, residual scale and analytic minimum remain unchanged. -/
def atGridIndex (budget :
  Accuracy.Fragment.FragmentAccuracy bounds columns fragments target) (index : Nat) (later : budget.grid.index ≤ index)
  :
    Accuracy.Fragment.FragmentAccuracy bounds columns fragments target :=
  { budget with grid := Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex budget.grid index later
                grid_ge := budget.grid_ge.trans later }

/-- The updated fragment budget's grid index is exactly the supplied index. -/
theorem atGridIndex_index (budget :
  Accuracy.Fragment.FragmentAccuracy bounds columns fragments target) (index : Nat) (later : budget.grid.index ≤ index)
  :
    (atGridIndex budget index later).grid.index = index := rfl

end Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy

end
end
