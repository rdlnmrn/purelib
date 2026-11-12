module

public import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.Floors
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseRootPolynomial

/-! # Whole rectangular primitive requests across an exact step-count identity

Only the Nat owner is reindexed. The complete original request, its actual
stage and all numerical fields are retained, with no selection, model,
request rebuild or promotion to another refinement index.
-/

public section

namespace Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Box Coordinate)

variable {polynomial numerator : Polynomial} {ambient : Box}
    {clearance : RegionClearance polynomial ambient} {bounds : PrimitiveOverlapBounds clearance numerator}
    {first last : Nat} {target : Coordinate}

/-- Reindex the complete original request along an exact equality of its rectangular step counts. -/
def castColumns (equal : first = last) (request : GridPrimitiveAccuracy bounds first target) :
    GridPrimitiveAccuracy bounds last target := by
  cases equal
  exact request

/-- Step-count reindexing retains the whole original request heterogeneously. -/
theorem castColumns_heq (equal : first = last) (request : GridPrimitiveAccuracy bounds first target) :
    HEq (castColumns equal request) request := by
  cases equal
  unfold castColumns
  rfl

/-- The same request keeps its actual selected refinement index after step-count transport. -/
theorem castColumns_index (equal : first = last) (request : GridPrimitiveAccuracy bounds first target) :
    (castColumns equal request).index = request.index := by
  cases equal
  unfold castColumns
  rfl

/-- The original complete gluing bound is unchanged by exact step-count transport. -/
theorem castColumns_globalBound (equal : first = last) (request : GridPrimitiveAccuracy bounds first target) :
    (castColumns equal request).globalBound = request.globalBound := by
  cases equal
  unfold castColumns
  rfl

/-- Exact step-count transport commutes with the original genuine later-index request operation. -/
theorem castColumns_after (equal : first = last) (request : GridPrimitiveAccuracy bounds first target) (floor : Nat) :
    castColumns equal (request.after floor) = (castColumns equal request).after floor := by
  cases equal
  unfold castColumns
  rfl

end Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy

end
