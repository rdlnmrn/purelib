module
public import Purelib.Integration.Cell.Numerical.Common.Intersection
public import Purelib.Integration.Cell.Partitioned.Split

/-!
# Numerical common-child splits

The actual intersected numerical children retain their indexed parents,
lengths and narrowed ranges. The shared finite partitioned-cell theorem
constructs the original split relation in the retained child order.
-/

public section

namespace Purelib.Integration.NumericalFrontier.CommonReadings

open Purelib.Approximation
open Purelib.Data.Rat

/-- Ordered common numerical children meet the shared indexed-refinement contract. -/
theorem indexed {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (common : CommonReadings left right request)
    (ordered : common.readings.Pairwise
      (fun first second => first.entry.leftOwner.index ≤ second.entry.leftOwner.index)) :
    PartitionedCells.IndexedRefinement left.partitioned common.refinement.partition common.readings
      (fun reading => reading.entry.child) (fun reading => reading.entry.leftOwner)
      (fun reading => reading.leftCell.val) CommonReading.intersectionCell := by
  exact
    { domains_eq := common.reading_domains
      valid := fun reading => reading.valid
      selected_read := fun reading => reading.leftCell.property.1
      selected_domain := fun reading => reading.leftCell.property.2
      weight := fun _ => rfl
      ranges := fun reading => by
        have refines := Interval.intersect_refines_left reading.leftCell.val.range reading.rightCell.val.range
          reading.ranges_overlap
        exact ⟨refines.lower, refines.upper⟩
      ordered := ordered }

/-- The actual common numerical children meet the shared indexed-refinement contract. -/
theorem commonReadings_indexed {source : Fraction.Rational → BoundProcess}
    (left right : NumericalFrontier source) (request : AccuracyRequest) :
    let common := commonReadings left right request
    PartitionedCells.IndexedRefinement left.partitioned common.refinement.partition common.readings
      (fun reading => reading.entry.child) (fun reading => reading.entry.leftOwner)
      (fun reading => reading.leftCell.val) CommonReading.intersectionCell :=
  indexed (commonReadings left right request) (commonReadings_left_indices left right request)

/-- The computed numerical intersection is an actual finite split refinement of its saved left frontier. -/
theorem commonReadings_intersection_refines {source : Fraction.Rational → BoundProcess}
    (left right : NumericalFrontier source) (request : AccuracyRequest) :
    IntegrationFrontierRefines (commonReadings left right request).intersection.cells left.cells :=
  (commonReadings_indexed left right request).refines

/-- Shared cache-selected observations produce an actual split refinement of the saved frontier. -/
theorem commonReadingsCached_intersection_refines {source : Fraction.Rational → BoundProcess}
    (left right : NumericalFrontier source) (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    IntegrationFrontierRefines (commonReadingsCached left right cached request).intersection.cells left.cells :=
  (indexed (commonReadingsCached left right cached request)
    (commonReadingsCached_left_indices left right cached request)).refines

end Purelib.Integration.NumericalFrontier.CommonReadings

end
