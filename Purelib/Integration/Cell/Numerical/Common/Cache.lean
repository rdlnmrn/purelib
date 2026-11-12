module

public import Purelib.Integration.Cell.Numerical.Common

/-! Common point observations from two independently owned numerical banks. -/

public section

namespace Purelib.Integration.NumericalFrontier.Common.Cache

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Retain independently returned left and right points at the same original common tag. -/
@[expose] def pairFromObservations {leftSource rightSource : Fraction.Rational → BoundProcess}
    (interval : Partition.Interval) (tag : Fraction.Rational)
    (inside : interval.start ≤ tag ∧ tag ≤ interval.finish) (request : AccuracyRequest)
    (left : NumericalPoint.Observation leftSource interval tag request)
    (right : NumericalPoint.Observation rightSource interval tag request) :
    PointPair leftSource rightSource interval tag inside request :=
  let leftPair := pairFromObservation interval tag inside request left
  let rightPair := pairFromObservation interval tag inside request right
  ⟨leftPair.leftOrigin, leftPair.leftPoint, leftPair.left_eq,
    rightPair.rightOrigin, rightPair.rightPoint, rightPair.right_eq⟩

/-- Select each common source point from its own original point bank. -/
@[expose] def cachedPair {leftSource rightSource : Fraction.Rational → BoundProcess}
    (leftBank : List (NumericalPoint leftSource)) (rightBank : List (NumericalPoint rightSource))
    (interval : Partition.Interval) (tag : Fraction.Rational)
    (inside : interval.start ≤ tag ∧ tag ≤ interval.finish) (request : AccuracyRequest) :
    PointPair leftSource rightSource interval tag inside request :=
  pairFromObservations interval tag inside request
    (NumericalPoint.atCached leftSource leftBank interval tag inside.1 inside.2 request)
    (NumericalPoint.atCached rightSource rightBank interval tag inside.1 inside.2 request)

/-- Keep the caller's point bank first, then the actual original frontier points. -/
@[expose] def available {source : Fraction.Rational → BoundProcess}
    (frontier : NumericalFrontier source) (bank : List (NumericalPoint source)) : List (NumericalPoint source) :=
  bank ++ frontier.cells.map (fun cell => cell.item)

/-- Compute the original common refinement using two already retained effective point banks. -/
@[expose] def commonReadings {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource)
    (leftBank : List (NumericalPoint leftSource)) (rightBank : List (NumericalPoint rightSource))
    (request : AccuracyRequest) : CommonReadings left right request :=
  readRefinementWith left right request (Unit.Common.commonRefinement left.partition right.partition)
    Partition.Interval.start (fun _ valid => ⟨le_rfl, valid.2.1.le⟩)
    (fun interval _ tag inside _ _ => cachedPair leftBank rightBank interval tag inside request)

end Purelib.Integration.NumericalFrontier.Common.Cache

end
