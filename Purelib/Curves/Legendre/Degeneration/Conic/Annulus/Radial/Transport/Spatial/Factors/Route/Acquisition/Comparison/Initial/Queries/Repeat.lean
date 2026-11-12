module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial.Queries
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Comparison.Repeat
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Fin

/-! # Signed comparison of actual interior factor queries

Both query caches retain their original Reading and RequestedSamples factories.
Their actual strict child fractions give half-open visits in the SAME fine
Route windows. The original signed factor repeat operation compares the
full-cubic channels; equality of physical points alone never chooses a root.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

namespace Route.Acquisition.Comparison.Initial.Cache.QueryAt

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.RootContinuation
open Segment.Reading.Payment

variable {site : Fin 2} {parameter : Canonical} {firstQuarter lastQuarter : UnitCircuitQuarter}
variable {firstPositive lastPositive : (0 : Fraction.Rational) < 2}
variable {firstActual : Transport.Quarter site parameter 2 firstQuarter firstPositive}
variable {lastActual : Transport.Quarter site parameter 2 lastQuarter lastPositive}
variable {firstReference firstTargetTime lastReference lastTargetTime : Fraction.Rational}
variable {firstReferenceInside : FixedRootBoxPath.Inside firstReference}
variable {firstTargetInside : FixedRootBoxPath.Inside firstTargetTime}
variable {lastReferenceInside : FixedRootBoxPath.Inside lastReference}
variable {lastTargetInside : FixedRootBoxPath.Inside lastTargetTime}
variable {firstSource : Transport.Reading firstActual firstReference firstReferenceInside}
variable {firstTarget : Transport.Reading firstActual firstTargetTime firstTargetInside}
variable {lastSource : Transport.Reading lastActual lastReference lastReferenceInside}
variable {lastTarget : Transport.Reading lastActual lastTargetTime lastTargetInside}
variable {firstAnchor : Parameter.Anchor firstSource.lift} {lastAnchor : Parameter.Anchor lastSource.lift}
variable {firstBudgets : Budgets firstAnchor} {lastBudgets : Budgets lastAnchor}
variable {firstPayment : (firstTargetTime - firstReference) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {lastPayment : (lastTargetTime - lastReference) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable (firstGeometry : Spatial.Parallel.Geometry firstSource firstTarget firstAnchor.regular firstPayment)
variable (lastGeometry : Spatial.Parallel.Geometry lastSource lastTarget lastAnchor.regular lastPayment)
variable (firstEntry : Initial firstSource)
variable {firstFinish : Canonical}
variable (firstPath : ClearPath (Paths.polynomial parameter) (sourceBox firstAnchor)
  (Spatial.coordinate site parameter 2 firstQuarter firstPositive firstReference)
  firstFinish)
variable (firstWithin : firstPath.WithinAmbient) (firstFactors : Path firstBudgets firstPath firstWithin)
variable (firstPaid : CoveredTracedPath.Acquisition.Spine
  (fun {_start _finish} segment => widthRequest firstAnchor segment) firstPath firstWithin firstEntry.owner)
variable (firstRetained : Cache firstEntry firstPath firstWithin firstFactors firstPaid)
variable {frame : Paths.Frame parameter} {basis : Differential 1} {sheet : Fin 2} {count floor : Nat}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable (firstKept : Physical.Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets)
  (fun {_start _finish} segment => widthRequest firstAnchor segment) firstPath firstWithin firstEntry.owner firstPaid)
variable (firstOuter : Fin (Physical.Spine.Sources.parentWords
  (fun {_start _finish} segment => widthRequest firstAnchor segment)
  firstPath firstWithin firstEntry.owner firstPaid firstKept).length)
variable (firstChild : Fin (Physical.Spine.Sources.segmentAt
  (fun {_start _finish} segment => widthRequest firstAnchor segment)
  firstPath firstWithin firstEntry.owner firstPaid firstKept firstOuter).parents.covered.parents.length)
variable {firstFraction : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside firstFraction}
variable (firstQueried : QueryAt firstEntry firstPath firstWithin firstFactors firstPaid firstRetained firstKept
  firstOuter firstChild firstFraction firstInside)
variable (firstBelow : firstFraction < 1)
variable (firstVisits : ∀ point, firstPath.HalfOpen point → firstGeometry.route.path.HalfOpen point)
attribute [local irreducible] Transport.Spatial.coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

section ReadingComparison

variable {lastStart lastFinish : Canonical}
variable {lastSegment : ClearSegment (Paths.polynomial parameter) (sourceBox lastAnchor) lastStart lastFinish}
variable {lastWithin : lastSegment.WithinAmbient} {lastCompleted : Segment lastBudgets lastSegment lastWithin}
variable {lastTime : Fraction.Rational} {lastInside : FixedRootBoxPath.Inside lastTime}
variable (last : Segment.Reading lastCompleted lastTime lastInside)
variable (firstWidth : (firstReference - firstTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
variable (lastWidth : (lastReference - lastTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
variable (lastVisit : lastGeometry.route.path.HalfOpen (lastSegment.pointAt lastTime))
variable (point_eq :
  ((Physical.Spine.Sources.segmentAt (fun {_start _finish} segment => widthRequest firstAnchor segment)
    firstPath firstWithin firstEntry.owner firstPaid firstKept
    firstOuter).parents.covered.parents[firstChild.val]'firstChild.isLt).edge.point firstFraction =
      lastSegment.pointAt lastTime)

/-- A strict actual query compares with a retained physical Reading through both paid signed Route windows. -/
def agree_with_reading :
    NamedEquivalent
      (channel firstEntry firstPath firstWithin firstFactors firstPaid firstRetained firstKept
        firstOuter firstChild firstFraction firstInside firstQueried).name last.values.value.name := by
  revert firstChild firstQueried point_eq
  cases firstPath with
  | nil point => exact Fin.elim0 firstOuter
  | cons firstHead firstTail =>
      cases firstTail with
      | nil firstFinish =>
          cases firstOuter using Data.Fin.casesDependent with
          | first =>
            intro firstChild firstQueried point_eq
            let actualPath := (ClearPath.cons firstHead (.nil firstFinish))
            have visited := Cache.query_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid
              firstRetained firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild firstFraction firstInside firstBelow
            have firstVisit := firstVisits _ visited
            have incidence := Fold.QueryAt.point_eq firstQueried
            have rawVisit := Eq.mp (congrArg (fun point => firstGeometry.route.path.HalfOpen point) incidence)
              firstVisit
            exact Segment.Reading.Comparison.agree_at_repeat firstGeometry lastGeometry
              (Fold.QueryAt.reading firstQueried) last firstWidth lastWidth rawVisit lastVisit
              (incidence.symm.trans point_eq)
          | following empty => exact Fin.elim0 empty
      | cons firstSecond firstRest =>
          cases firstRest with
          | nil firstFinish =>
              cases firstOuter using Data.Fin.casesDependent with
              | first =>
                intro firstChild firstQueried point_eq
                let actualPath := (ClearPath.cons firstHead (.cons firstSecond (.nil firstFinish)))
                have visited := Cache.query_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid
                  firstRetained firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild firstFraction firstInside firstBelow
                have firstVisit := firstVisits _ visited
                have incidence := Fold.QueryAt.point_eq firstQueried
                have rawVisit := Eq.mp (congrArg (fun point => firstGeometry.route.path.HalfOpen point) incidence)
                  firstVisit
                exact Segment.Reading.Comparison.agree_at_repeat firstGeometry lastGeometry
                  (Fold.QueryAt.reading firstQueried) last firstWidth lastWidth rawVisit lastVisit
                  (incidence.symm.trans point_eq)
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  intro firstChild firstQueried point_eq
                  let actualPath := (ClearPath.cons firstHead (.cons firstSecond (.nil firstFinish)))
                  have visited := Cache.query_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid
                    firstRetained firstKept (Fin.succ ⟨0, Nat.zero_lt_succ _⟩) firstChild
                    firstFraction firstInside firstBelow
                  have firstVisit := firstVisits _ visited
                  have incidence := Fold.QueryAt.point_eq firstQueried
                  have rawVisit := Eq.mp (congrArg (fun point => firstGeometry.route.path.HalfOpen point) incidence)
                    firstVisit
                  exact Segment.Reading.Comparison.agree_at_repeat firstGeometry lastGeometry
                    (Fold.QueryAt.reading firstQueried) last firstWidth lastWidth rawVisit lastVisit
                    (incidence.symm.trans point_eq)
                | following empty => exact Fin.elim0 empty
          | cons _third _tail => exact nomatch firstRetained

end ReadingComparison

variable (lastEntry : Initial lastSource)
variable (lastPath : ClearPath (Paths.polynomial parameter) (sourceBox lastAnchor)
  (Spatial.coordinate site parameter 2 lastQuarter lastPositive lastReference)
  (Spatial.coordinate site parameter 2 lastQuarter lastPositive lastTargetTime))
variable (lastWithinPath : lastPath.WithinAmbient) (lastFactors : Path lastBudgets lastPath lastWithinPath)
variable (lastPaid : CoveredTracedPath.Acquisition.Spine
  (fun {_start _finish} segment => widthRequest lastAnchor segment) lastPath lastWithinPath lastEntry.owner)
variable (lastRetained : Cache lastEntry lastPath lastWithinPath lastFactors lastPaid)
variable (lastKept : Physical.Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets)
  (fun {_start _finish} segment => widthRequest lastAnchor segment)
  lastPath lastWithinPath lastEntry.owner lastPaid)
variable (lastOuter : Fin (Physical.Spine.Sources.parentWords
  (fun {_start _finish} segment => widthRequest lastAnchor segment)
  lastPath lastWithinPath lastEntry.owner lastPaid lastKept).length)
variable (lastChild : Fin (Physical.Spine.Sources.segmentAt
  (fun {_start _finish} segment => widthRequest lastAnchor segment)
  lastPath lastWithinPath lastEntry.owner lastPaid lastKept lastOuter).parents.covered.parents.length)
variable {lastFraction : Fraction.Rational} {lastInsideQuery : FixedRootBoxPath.Inside lastFraction}
variable (lastQueried : QueryAt lastEntry lastPath lastWithinPath lastFactors lastPaid lastRetained lastKept
  lastOuter lastChild lastFraction lastInsideQuery)
variable (lastBelow : lastFraction < 1)
variable (lastPath_eq : lastPath = lastGeometry.route.path)
variable (firstWidth : (firstReference - firstTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
variable (lastWidth : (lastReference - lastTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
variable (samePoint :
  ((Physical.Spine.Sources.segmentAt (fun {_start _finish} segment => widthRequest firstAnchor segment)
    firstPath firstWithin firstEntry.owner firstPaid firstKept
    firstOuter).parents.covered.parents[firstChild.val]'firstChild.isLt).edge.point firstFraction =
  ((Physical.Spine.Sources.segmentAt (fun {_start _finish} segment => widthRequest lastAnchor segment)
    lastPath lastWithinPath lastEntry.owner lastPaid lastKept
    lastOuter).parents.covered.parents[lastChild.val]'lastChild.isLt).edge.point lastFraction)

/-- Two retained strict-fraction queries compare through their original factor windows and full physical incidence.

Only the actual zero/one/two Route branches are eliminated. Both complete
query caches, original factor owners and independent requests survive;
no observation, continuation, source preparation or query is rerun.
-/
def agree_at_repeat :
    NamedEquivalent
      (channel firstEntry firstPath firstWithin firstFactors firstPaid firstRetained firstKept
        firstOuter firstChild firstFraction firstInside firstQueried).name
      (channel lastEntry lastPath lastWithinPath lastFactors lastPaid lastRetained lastKept
        lastOuter lastChild lastFraction lastInsideQuery lastQueried).name := by
  have lastVisits (point : Canonical) (visited : lastPath.HalfOpen point) :
      lastGeometry.route.path.HalfOpen point :=
    Eq.mp (congrArg (fun path => path.HalfOpen point) lastPath_eq) visited
  clear lastPath_eq
  revert firstChild firstQueried samePoint
  cases firstPath with
  | nil point => exact Fin.elim0 firstOuter
  | cons firstHead firstTail =>
      cases firstTail with
      | nil firstFinish =>
          cases firstOuter using Data.Fin.casesDependent with
          | first =>
            intro firstChild firstQueried samePoint
            let actualPath := (ClearPath.cons firstHead (.nil firstFinish))
            have visited := Cache.query_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid
              firstRetained firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild firstFraction firstInside firstBelow
            have firstVisit := firstVisits _ visited
            have incidence := Fold.QueryAt.point_eq firstQueried
            have rawVisit := Eq.mp (congrArg (fun point => firstGeometry.route.path.HalfOpen point) incidence)
              firstVisit
            exact (agree_with_reading lastGeometry firstGeometry lastEntry lastPath lastWithinPath
              lastFactors lastPaid lastRetained lastKept lastOuter lastChild lastQueried lastBelow
              lastVisits (Fold.QueryAt.reading firstQueried) lastWidth firstWidth rawVisit
              (samePoint.symm.trans incidence)).symm
          | following empty => exact Fin.elim0 empty
      | cons firstSecond firstRest =>
          cases firstRest with
          | nil firstFinish =>
              cases firstOuter using Data.Fin.casesDependent with
              | first =>
                intro firstChild firstQueried samePoint
                let actualPath := (ClearPath.cons firstHead (.cons firstSecond (.nil firstFinish)))
                have visited := Cache.query_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid
                  firstRetained firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild firstFraction firstInside firstBelow
                have firstVisit := firstVisits _ visited
                have incidence := Fold.QueryAt.point_eq firstQueried
                have rawVisit := Eq.mp (congrArg (fun point => firstGeometry.route.path.HalfOpen point) incidence)
                  firstVisit
                exact (agree_with_reading lastGeometry firstGeometry lastEntry lastPath lastWithinPath
                  lastFactors lastPaid lastRetained lastKept lastOuter lastChild lastQueried lastBelow
                  lastVisits (Fold.QueryAt.reading firstQueried) lastWidth firstWidth rawVisit
                  (samePoint.symm.trans incidence)).symm
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  intro firstChild firstQueried samePoint
                  let actualPath := (ClearPath.cons firstHead (.cons firstSecond (.nil firstFinish)))
                  have visited := Cache.query_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid
                    firstRetained firstKept (Fin.succ ⟨0, Nat.zero_lt_succ _⟩) firstChild
                    firstFraction firstInside firstBelow
                  have firstVisit := firstVisits _ visited
                  have incidence := Fold.QueryAt.point_eq firstQueried
                  have rawVisit := Eq.mp (congrArg (fun point => firstGeometry.route.path.HalfOpen point) incidence)
                    firstVisit
                  exact (agree_with_reading lastGeometry firstGeometry lastEntry lastPath lastWithinPath
                    lastFactors lastPaid lastRetained lastKept lastOuter lastChild lastQueried lastBelow
                    lastVisits (Fold.QueryAt.reading firstQueried) lastWidth firstWidth rawVisit
                    (samePoint.symm.trans incidence)).symm
                | following empty => exact Fin.elim0 empty
          | cons _third _tail => exact nomatch firstRetained

end Route.Acquisition.Comparison.Initial.Cache.QueryAt

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

end
