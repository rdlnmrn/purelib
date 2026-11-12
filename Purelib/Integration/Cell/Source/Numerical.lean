module
public import Purelib.Integration.Cell.Source
public import Purelib.Integration.Cell.Numerical
import Purelib.Data.List.Map

/-!
# Exact source frontiers as numerical point processes

Each original exact tag becomes the exact rational point process at that
same tag. The cached reading, original cell range, weight, partition and
ordered occurrences are retained.
-/

public section

namespace Purelib.Integration.SourceFrontier.Numerical

open Purelib.Approximation
open Purelib.Data.Rat

/-- Retain an exact source tag as the corresponding exact numerical point request. -/
@[expose] def point {source : Fraction.Rational → Fraction.Rational}
    (tag : SourcePoint source) (request : AccuracyRequest) :
    NumericalPoint (fun point => BoundProcess.exact (source point)) where
  interval := tag.interval
  point := tag.point
  start_le := tag.start_le
  point_le_finish := tag.point_le_finish
  previous := ()
  request := request
  state := ()
  state_eq := rfl
  reading := Purelib.Data.Rat.Interval.exact tag.reading
  reading_eq := by rw [tag.reading_eq]; rfl

/-- Retain an exact source cell's original weight, range and cached point reading. -/
@[expose] def cell {source : Fraction.Rational → Fraction.Rational}
    (original : IntegrationCell (SourcePoint source)) (request : AccuracyRequest) :
    IntegrationCell (NumericalPoint (fun point => BoundProcess.exact (source point))) where
  item := point original.item request
  weight := original.weight
  weight_nonnegative := original.weight_nonnegative
  lower := original.lower
  upper := original.upper
  range_valid := original.range_valid

/-- Reuse the actual source frontier as a numerical frontier over exact rational point processes. -/
@[expose] def frontier {source : Fraction.Rational → Fraction.Rational}
    (original : SourceFrontier source) (request : AccuracyRequest) :
    NumericalFrontier (fun point => BoundProcess.exact (source point)) where
  partition := original.partition
  cells := original.cells.map (fun retained => cell retained request)
  domains_eq := by
    rw [Purelib.Data.List.Map.map_map]
    exact original.domains_eq
  weight_eq := by
    intro converted member
    obtain ⟨old, oldMember, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
    rw [← equal]
    exact original.weight_eq old oldMember
  source_overlap := by
    intro converted member query lower upper state
    cases state
    obtain ⟨old, oldMember, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
    rw [← equal] at lower upper ⊢
    exact original.source_range old oldMember query lower upper

/-- Converting original exact cells preserves their lower integral sum. -/
private theorem lower_eq {source : Fraction.Rational → Fraction.Rational}
    (request : AccuracyRequest) : ∀ cells : List (IntegrationCell (SourcePoint source)),
    lowerIntegral (cells.map (fun original => cell original request)) = lowerIntegral cells
  | [] => rfl
  | _ :: remaining => by
      change _ + lowerIntegral (remaining.map (fun original => cell original request)) = _ + lowerIntegral remaining
      rw [lower_eq request remaining]
      rfl

/-- Converting original exact cells preserves their upper integral sum. -/
private theorem upper_eq {source : Fraction.Rational → Fraction.Rational}
    (request : AccuracyRequest) : ∀ cells : List (IntegrationCell (SourcePoint source)),
    upperIntegral (cells.map (fun original => cell original request)) = upperIntegral cells
  | [] => rfl
  | _ :: remaining => by
      change _ + upperIntegral (remaining.map (fun original => cell original request)) = _ + upperIntegral remaining
      rw [upper_eq request remaining]
      rfl

/-- The numerical conversion preserves the original exact integral enclosure. -/
theorem integralBound_eq {source : Fraction.Rational → Fraction.Rational}
    (original : SourceFrontier source) (request : AccuracyRequest) :
    integralBound (frontier original request).cells = integralBound original.cells := by
  apply Purelib.Data.Rat.Interval.ext
  · exact lower_eq request original.cells
  · exact upper_eq request original.cells

end Purelib.Integration.SourceFrontier.Numerical

end
