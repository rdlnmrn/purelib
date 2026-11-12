module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block.Sources.Occurrence
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial.Sources.Reading
import Purelib.Approximation.Gaussian.Equivalence.Observation

/-! # Signed repeated visits of two SAME actual paid Block source caches

The two original source occurrences retain their literal physical positions,
ordinary/corner factor origins, original queries and OLD observations. Actual
fine Route widths and the original factor windows derive their signed
full-cubic agreement; no desired comparison or bank Distinct is an input.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Block.SourceOccurrence

open Purelib
open Purelib.Approximation.Gaussian
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
variable (samePoint : first.point = last.point)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The two SAME actual fine source occurrences derive full-cubic agreement with their original owners intact. -/
def agree_at_repeat : NamedEquivalent first.channel.name last.channel.name :=
  Initial.Cache.SourceAt.agree_at_repeat
    (firstGeometry := firstGeometry)
    (firstEntry := firstBlock.initial)
    (firstPath := firstGeometry.route.path)
    (firstWithin := firstGeometry.route.within)
    (firstFactors := firstBlock.paid.factors.path)
    (firstPaid := firstBlock.paid.spine)
    (firstRetained := firstBlock.comparison.val)
    (firstKept := firstSources)
    (firstOuter := first.position.1)
    (firstChild := Spine.Sources.child firstGeometry.route.path firstGeometry.route.within firstOwner
      firstBlock.paid.spine firstSources firstIndex first.position)
    (firstOrigin := first.origin)
    (firstFactory := first.origin_eq)
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
    (lastChild := Spine.Sources.child lastGeometry.route.path lastGeometry.route.within lastOwner
      lastBlock.paid.spine lastSources lastIndex last.position)
    (lastOrigin := last.origin)
    (lastFactory := last.origin_eq)
    (lastPath_eq := rfl)
    (firstWidth := firstWidth)
    (lastWidth := lastWidth)
    (samePoint := samePoint)

/-- The two literal aggregate source queries agree through their OWN retained ordinary/corner factor origins. -/
def queries_at_repeat :
    NamedEquivalent (first.parent.edge.rootName 0 first.parent.edge.baseInside)
      (last.parent.edge.rootName 0 last.parent.edge.baseInside) :=
  first.queryEquivalent.trans ((agree_at_repeat first last firstWidth lastWidth samePoint).trans
    last.queryEquivalent.symm)

/-- Compare the two SAME OLD product observations without changing either visible radius or original request. -/
def compare (target : Fraction.Rational) (positive : 0 < target) :
    Equivalence.Observation.Comparison first.product last.product target :=
  Equivalence.Observation.Comparison.build first.product last.product
    (agree_at_repeat first last firstWidth lastWidth samePoint) target positive

/-- The retained comparison is the whole original generic observation factory on those identical OLD inputs. -/
theorem compare_eq (target : Fraction.Rational) (positive : 0 < target) :
    compare first last firstWidth lastWidth samePoint target positive =
      Equivalence.Observation.Comparison.build first.product last.product
        (agree_at_repeat first last firstWidth lastWidth samePoint) target positive := by
  unfold compare
  rfl

end Steps.Acquisition.Block.SourceOccurrence

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
