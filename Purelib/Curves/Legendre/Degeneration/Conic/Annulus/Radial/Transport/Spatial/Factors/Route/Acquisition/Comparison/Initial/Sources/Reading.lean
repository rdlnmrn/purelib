module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial.Sources.Dispatch
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Comparison.Repeat
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Fin

/-! # Signed comparison of an actual retained Route source and an independently retained physical Reading

The actual zero/one/two-edge Cache and its same ordinary/corner SourceAt
are consumed without rebuilding a Reading, observation or root. Original
repeat-window geometry derives the signed full-cubic comparison. The second
edge's preceding terminal Reading remains the actual source when selected.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Route.Acquisition.Comparison.Initial.Cache.SourceAt

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
variable (firstOrigin : SourceAt firstEntry firstPath firstWithin firstFactors firstPaid firstRetained firstKept
  firstOuter firstChild)
variable (firstFactory : firstOrigin = Cache.sourceAt firstEntry firstPath firstWithin firstFactors firstPaid
  firstRetained firstKept firstOuter firstChild)
variable (firstVisits : ∀ point, firstPath.HalfOpen point → firstGeometry.route.path.HalfOpen point)
variable {lastStart lastFinish : Canonical}
variable {lastSegment : ClearSegment (Paths.polynomial parameter) (sourceBox lastAnchor) lastStart lastFinish}
variable {lastWithin : lastSegment.WithinAmbient} {lastCompleted : Segment lastBudgets lastSegment lastWithin}
variable {lastTime : Fraction.Rational} {lastInside : FixedRootBoxPath.Inside lastTime}
variable (last : Segment.Reading lastCompleted lastTime lastInside)
variable (firstWidth : (firstReference - firstTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
variable (lastWidth : (lastReference - lastTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
variable (lastVisit : lastGeometry.route.path.HalfOpen (lastSegment.pointAt lastTime))
variable (point_eq : point firstEntry firstPath firstWithin firstFactors firstPaid firstRetained firstKept
  firstOuter firstChild firstOrigin = lastSegment.pointAt lastTime)

attribute [local irreducible] Transport.Spatial.coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Actual fine repeated visits compare this SAME retained ordinary-or-corner source with the original physical Reading.

The actual source getter's whole factory equality and retained Route-visit transport
supply the first geometric occurrence. Every branch consumes its literal
preceding/current Reading and original factor windows. Both full-cubic
owners survive; no desired signed relation or lookup-key argument is an input.
-/
def agree_with_reading :
    NamedEquivalent
      (channel firstEntry firstPath firstWithin firstFactors firstPaid firstRetained firstKept
        firstOuter firstChild firstOrigin).name last.values.value.name := by
  revert firstChild firstOrigin firstFactory point_eq
  cases firstPath with
  | nil point => exact Fin.elim0 firstOuter
  | cons firstHead firstTail =>
      cases firstTail with
      | nil firstFinish =>
          cases firstOuter using Data.Fin.casesDependent with
          | first =>
            intro firstChild firstOrigin firstFactory point_eq
            let actualPath := (ClearPath.cons firstHead (.nil firstFinish))
            have visited : actualPath.HalfOpen
                (point firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                  firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild firstOrigin) := by
              rewrite [firstFactory]
              exact Cache.sourceAt_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild
            have firstVisit := firstVisits _ visited
            cases firstOrigin with
            | inl _previous =>
                exact Reading.Comparison.agree_at_repeat firstGeometry lastGeometry
                  firstRetained.1.val last firstWidth lastWidth firstVisit lastVisit point_eq
            | inr current =>
                exact Reading.Comparison.agree_at_repeat firstGeometry lastGeometry
                  current.1 last firstWidth lastWidth firstVisit lastVisit point_eq
          | following empty => exact Fin.elim0 empty
      | cons firstSecond firstRest =>
          cases firstRest with
          | nil firstFinish =>
              cases firstOuter using Data.Fin.casesDependent with
              | first =>
                intro firstChild firstOrigin firstFactory point_eq
                let actualPath := (ClearPath.cons firstHead (.cons firstSecond (.nil firstFinish)))
                have visited : actualPath.HalfOpen
                    (point firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                      firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild firstOrigin) := by
                  rewrite [firstFactory]
                  exact Cache.sourceAt_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                    firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild
                have firstVisit := firstVisits _ visited
                cases firstOrigin with
                | inl _previous =>
                    exact Reading.Comparison.agree_at_repeat firstGeometry lastGeometry
                      firstRetained.1.1.val last firstWidth lastWidth firstVisit lastVisit point_eq
                | inr current =>
                    exact Reading.Comparison.agree_at_repeat firstGeometry lastGeometry
                      current.1 last firstWidth lastWidth firstVisit lastVisit point_eq
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  intro firstChild firstOrigin firstFactory point_eq
                  let actualPath := (ClearPath.cons firstHead (.cons firstSecond (.nil firstFinish)))
                  have visited : actualPath.HalfOpen
                      (point firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                        firstKept (Fin.succ ⟨0, Nat.zero_lt_succ _⟩) firstChild firstOrigin) := by
                    rewrite [firstFactory]
                    exact Cache.sourceAt_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                      firstKept (Fin.succ ⟨0, Nat.zero_lt_succ _⟩) firstChild
                  have firstVisit := firstVisits _ visited
                  cases firstOrigin with
                  | inl _previous =>
                      exact Reading.Comparison.agree_at_repeat firstGeometry lastGeometry
                        (Second.terminal firstEntry firstRetained.2).1 last firstWidth lastWidth firstVisit lastVisit
                        point_eq
                  | inr current =>
                      exact Reading.Comparison.agree_at_repeat firstGeometry lastGeometry
                        current.1 last firstWidth lastWidth firstVisit lastVisit point_eq
                | following empty => exact Fin.elim0 empty
          | cons _third _tail => exact nomatch firstRetained

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
variable (lastOrigin : SourceAt lastEntry lastPath lastWithinPath lastFactors lastPaid lastRetained lastKept
  lastOuter lastChild)
variable (lastFactory : lastOrigin = Cache.sourceAt lastEntry lastPath lastWithinPath lastFactors lastPaid
  lastRetained lastKept lastOuter lastChild)
variable (lastPath_eq : lastPath = lastGeometry.route.path)
variable (samePoint : point firstEntry firstPath firstWithin firstFactors firstPaid firstRetained firstKept
  firstOuter firstChild firstOrigin = point lastEntry lastPath lastWithinPath lastFactors lastPaid lastRetained
    lastKept lastOuter lastChild lastOrigin)

/-- Repeated Route occurrences derive signed full-cubic agreement from both unchanged retained source-origin caches.

Both original physical positions and actual source getter equations remain
inputs. Finite branch elimination preserves each preceding/current Reading
and its old Samples. Existing factor-window comparison derives the sign;
no desired root relation, bank Distinct or global closure is assumed.
-/
def agree_at_repeat :
    NamedEquivalent
      (channel firstEntry firstPath firstWithin firstFactors firstPaid firstRetained firstKept
        firstOuter firstChild firstOrigin).name
      (channel lastEntry lastPath lastWithinPath lastFactors lastPaid lastRetained lastKept
        lastOuter lastChild lastOrigin).name := by
  have lastVisits (point : Canonical) (visited : lastPath.HalfOpen point) :
      lastGeometry.route.path.HalfOpen point :=
    Eq.mp (congrArg (fun path => path.HalfOpen point) lastPath_eq) visited
  clear point_eq lastVisit last
  revert firstChild firstOrigin firstFactory samePoint
  cases firstPath with
  | nil point => exact Fin.elim0 firstOuter
  | cons firstHead firstTail =>
      cases firstTail with
      | nil firstFinish =>
          cases firstOuter using Data.Fin.casesDependent with
          | first =>
            intro firstChild firstOrigin firstFactory samePoint
            let actualPath := (ClearPath.cons firstHead (.nil firstFinish))
            have visited : actualPath.HalfOpen
                (point firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                  firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild firstOrigin) := by
              rewrite [firstFactory]
              exact Cache.sourceAt_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild
            have firstVisit := firstVisits _ visited
            cases firstOrigin with
            | inl _previous =>
                exact (agree_with_reading lastGeometry firstGeometry lastEntry lastPath lastWithinPath
                  lastFactors lastPaid lastRetained lastKept lastOuter lastChild lastOrigin lastFactory
                  lastVisits firstRetained.1.val lastWidth firstWidth firstVisit samePoint.symm).symm
            | inr current =>
                exact (agree_with_reading lastGeometry firstGeometry lastEntry lastPath lastWithinPath
                  lastFactors lastPaid lastRetained lastKept lastOuter lastChild lastOrigin lastFactory
                  lastVisits current.1 lastWidth firstWidth firstVisit samePoint.symm).symm
          | following empty => exact Fin.elim0 empty
      | cons firstSecond firstRest =>
          cases firstRest with
          | nil firstFinish =>
              cases firstOuter using Data.Fin.casesDependent with
              | first =>
                intro firstChild firstOrigin firstFactory samePoint
                let actualPath := (ClearPath.cons firstHead (.cons firstSecond (.nil firstFinish)))
                have visited : actualPath.HalfOpen
                    (point firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                      firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild firstOrigin) := by
                  rewrite [firstFactory]
                  exact Cache.sourceAt_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                    firstKept ⟨0, Nat.zero_lt_succ _⟩ firstChild
                have firstVisit := firstVisits _ visited
                cases firstOrigin with
                | inl _previous =>
                    exact (agree_with_reading lastGeometry firstGeometry lastEntry lastPath lastWithinPath
                      lastFactors lastPaid lastRetained lastKept lastOuter lastChild lastOrigin lastFactory
                      lastVisits firstRetained.1.1.val lastWidth firstWidth firstVisit samePoint.symm).symm
                | inr current =>
                    exact (agree_with_reading lastGeometry firstGeometry lastEntry lastPath lastWithinPath
                      lastFactors lastPaid lastRetained lastKept lastOuter lastChild lastOrigin lastFactory
                      lastVisits current.1 lastWidth firstWidth firstVisit samePoint.symm).symm
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  intro firstChild firstOrigin firstFactory samePoint
                  let actualPath := (ClearPath.cons firstHead (.cons firstSecond (.nil firstFinish)))
                  have visited : actualPath.HalfOpen
                      (point firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                        firstKept (Fin.succ ⟨0, Nat.zero_lt_succ _⟩) firstChild firstOrigin) := by
                    rewrite [firstFactory]
                    exact Cache.sourceAt_halfOpen firstEntry actualPath firstWithin firstFactors firstPaid firstRetained
                      firstKept (Fin.succ ⟨0, Nat.zero_lt_succ _⟩) firstChild
                  have firstVisit := firstVisits _ visited
                  cases firstOrigin with
                  | inl _previous =>
                      exact (agree_with_reading lastGeometry firstGeometry lastEntry lastPath lastWithinPath
                        lastFactors lastPaid lastRetained lastKept lastOuter lastChild lastOrigin lastFactory
                        lastVisits (Second.terminal firstEntry firstRetained.2).1 lastWidth firstWidth firstVisit
                        samePoint.symm).symm
                  | inr current =>
                      exact (agree_with_reading lastGeometry firstGeometry lastEntry lastPath lastWithinPath
                        lastFactors lastPaid lastRetained lastKept lastOuter lastChild lastOrigin lastFactory
                        lastVisits current.1 lastWidth firstWidth firstVisit samePoint.symm).symm
                | following empty => exact Fin.elim0 empty
          | cons _third _tail => exact nomatch firstRetained

end Route.Acquisition.Comparison.Initial.Cache.SourceAt

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

end
