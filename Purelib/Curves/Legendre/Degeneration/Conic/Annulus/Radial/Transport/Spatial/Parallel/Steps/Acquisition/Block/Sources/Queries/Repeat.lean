module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block.Sources.Queries
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial.Queries.Repeat
import Purelib.Approximation.Gaussian.Equivalence.Observation

/-! # Signed interior-query comparisons on the same original Block occurrences

The two actual SourceOccurrences keep their independent paid geometry,
query caches and parent incidence. Original factor-window comparison
pays the sign at their strict-fraction repeated physical point.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Block.SourceOccurrence

open Purelib
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Factors.Segment.Reading.Payment (widthRequest)
open Factors.Route.Acquisition.Comparison (Initial)

variable {site : Fin 2} {parameter : Canonical} {firstQuarter lastQuarter : UnitCircuitQuarter}
variable {firstPositive lastPositive : (0 : Fraction.Rational) < 2}
variable {firstActual : Transport.Quarter site parameter 2 firstQuarter firstPositive}
variable {lastActual : Transport.Quarter site parameter 2 lastQuarter lastPositive}
variable {regular : parameter ≠ criticalValue site}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets sourcePath stage}

variable {firstCurrent firstTarget : Endpoint} {firstReading : ReadingAt firstActual firstCurrent}
variable {firstQueried : { retained : ReadingAt firstActual firstTarget //
  QueryCache firstActual firstTarget retained }}
variable {firstPayment : (firstTarget.parameter - firstCurrent.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {firstGeometry : Geometry firstReading firstQueried.val regular firstPayment}
variable {firstOwner : OwnerAt site parameter firstQuarter firstPositive firstCurrent}
variable {firstAgreement : InitialAgreement firstCurrent firstReading firstOwner}
variable {firstBlock : Block firstQueried firstGeometry firstOwner firstAgreement}
variable {firstSources : Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets)
  (fun {_start _finish} segment => widthRequest firstBlock.anchor segment)
  firstGeometry.route.path firstGeometry.route.within firstOwner firstBlock.paid.spine}
variable {firstIndex : Fin (Spine.Sources.assemble
  (fun {_start _finish} segment => widthRequest firstBlock.anchor segment)
  firstGeometry.route.path firstGeometry.route.within firstOwner
    firstBlock.paid.spine firstSources).geometry.parents.length}
variable (first : SourceOccurrence firstBlock firstSources firstIndex)

variable {lastCurrent lastTarget : Endpoint} {lastReading : ReadingAt lastActual lastCurrent}
variable {lastQueried : { retained : ReadingAt lastActual lastTarget // QueryCache lastActual lastTarget retained }}
variable {lastPayment : (lastTarget.parameter - lastCurrent.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {lastGeometry : Geometry lastReading lastQueried.val regular lastPayment}
variable {lastOwner : OwnerAt site parameter lastQuarter lastPositive lastCurrent}
variable {lastAgreement : InitialAgreement lastCurrent lastReading lastOwner}
variable {lastBlock : Block lastQueried lastGeometry lastOwner lastAgreement}
variable {lastSources : Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets)
  (fun {_start _finish} segment => widthRequest lastBlock.anchor segment)
  lastGeometry.route.path lastGeometry.route.within lastOwner lastBlock.paid.spine}
variable {lastIndex : Fin (Spine.Sources.assemble
  (fun {_start _finish} segment => widthRequest lastBlock.anchor segment)
  lastGeometry.route.path lastGeometry.route.within lastOwner lastBlock.paid.spine lastSources).geometry.parents.length}
variable (last : SourceOccurrence lastBlock lastSources lastIndex)

variable (firstWidth : (firstCurrent.parameter - firstTarget.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
variable (lastWidth : (lastCurrent.parameter - lastTarget.parameter) ^ 2 ≤
  Geometric.Basic.quarterRadius 1 10)
variable {firstFraction lastFraction : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside firstFraction}
variable {lastInside : FixedRootBoxPath.Inside lastFraction}
variable (firstQuery : QueryAt first firstFraction firstInside)
variable (lastQuery : QueryAt last lastFraction lastInside)
variable (firstBelow : firstFraction < 1) (lastBelow : lastFraction < 1)
variable (samePoint : first.parent.edge.point firstFraction = last.parent.edge.point lastFraction)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The two SAME retained interior factor caches compare through their actual original signed Route windows. -/
def queryChannels_at_repeat :
    NamedEquivalent
      (QueryAt.channel (retained := first) firstQuery).name
      (QueryAt.channel (retained := last) lastQuery).name :=
  Initial.Cache.QueryAt.agree_at_repeat
    (firstGeometry := firstGeometry)
    (firstEntry := firstBlock.initial)
    (firstPath := firstGeometry.route.path)
    (firstWithin := firstGeometry.route.within)
    (firstFactors := firstBlock.paid.factors.path)
    (firstPaid := firstBlock.paid.spine)
    (firstRetained := firstBlock.comparison.val)
    (firstKept := firstSources)
    (firstOuter := first.position.1)
    (firstChild := first.physicalChild)
    (firstQueried := firstQuery)
    (firstBelow := firstBelow)
    (firstVisits := fun _ visited => visited)
    (lastGeometry := lastGeometry)
    (lastEntry := lastBlock.initial)
    (lastPath := lastGeometry.route.path)
    (lastWithinPath := lastGeometry.route.within)
    (lastFactors := lastBlock.paid.factors.path)
    (lastPaid := lastBlock.paid.spine)
    (lastRetained := lastBlock.comparison.val)
    (lastKept := lastSources)
    (lastOuter := last.position.1)
    (lastChild := last.physicalChild)
    (lastQueried := lastQuery)
    (lastBelow := lastBelow)
    (lastPath_eq := rfl)
    (firstWidth := firstWidth)
    (lastWidth := lastWidth)
    (samePoint :=
      (congrArg (fun parent => parent.edge.point firstFraction) first.physicalParent_eq).symm.trans
        (samePoint.trans (congrArg (fun parent => parent.edge.point lastFraction) last.physicalParent_eq)))

/-- Both original prepared-child query roots agree through these SAME retained factor-query caches.

The query caches are inputs rather than historical source observations.
No factory executes here. Each original query-to-factor relation is
composed with the independently proved signed repeated-window comparison.
-/
def queryRoots_at_repeat :
    NamedEquivalent (first.parent.edge.rootName firstFraction firstInside)
      (last.parent.edge.rootName lastFraction lastInside) :=
  (QueryAt.equivalent (retained := first) firstQuery).trans
    ((queryChannels_at_repeat first last firstWidth lastWidth firstQuery lastQuery firstBelow lastBelow samePoint).trans
      (QueryAt.equivalent (retained := last) lastQuery).symm)

/-- Construct and compare two actual interior query caches on the same retained original source occurrences.

The supplied direct Queries retain their original parents and requests.
Each factor-query producer executes once, in source order. The two whole
results pay the original signed repeated-window comparison immediately;
neither source preparation, physical locator nor paid trace is replayed.
-/
def compareQueries
    (firstDirect : PreparedEdge.Query first.parent.edge firstFraction firstInside)
    (lastDirect : PreparedEdge.Query last.parent.edge lastFraction lastInside) :
    NamedEquivalent (first.parent.edge.rootName firstFraction firstInside)
      (last.parent.edge.rootName lastFraction lastInside) :=
  let firstQueried := queryAt first firstFraction firstInside firstDirect
  let lastQueried := queryAt last lastFraction lastInside lastDirect
  queryRoots_at_repeat first last firstWidth lastWidth firstQueried lastQueried firstBelow lastBelow samePoint

end Steps.Acquisition.Block.SourceOccurrence

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
