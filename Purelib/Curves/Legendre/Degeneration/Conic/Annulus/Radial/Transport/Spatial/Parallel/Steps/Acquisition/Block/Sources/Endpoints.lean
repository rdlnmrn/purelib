module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block.Sources.Occurrence
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly.ParentOccurrence.Lookup
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Endpoint incidence below the same retained Block source occurrence

The supplied SourceOccurrence retains the actual physical locator and
ordinary-or-corner factor origin. Only its existing position is consumed;
no locator, factor Reading, Samples, Fold or physical trace is replayed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Block

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.RootContinuation
open Factors.Segment.Reading.Payment (widthRequest)
open Factors.Route.Acquisition.Comparison (Initial)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {current target : Endpoint} {reading : ReadingAt actual current}
variable {queried : { retained : ReadingAt actual target // QueryCache actual target retained }}
variable {payment : (target.parameter - current.parameter) ^ 2 ≤
  Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {geometry : Geometry reading queried.val regular payment}
variable {sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {agreement : InitialAgreement current reading sourceOwner}
variable (block : Block queried geometry sourceOwner agreement)
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets sourcePath stage}
variable (sources : Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets)
  (fun {_start _finish} segment => widthRequest block.anchor segment)
  geometry.route.path geometry.route.within sourceOwner block.paid.spine)
variable (index : Fin (Spine.Sources.assemble
  (fun {_start _finish} segment => widthRequest block.anchor segment)
  geometry.route.path geometry.route.within sourceOwner block.paid.spine sources).geometry.parents.length)

namespace SourceOccurrence

variable {block sources index} (retained : SourceOccurrence block sources index)

/-- Read the exact original physical Segment/child below this SAME stored Block occurrence.

The previous Reading/Samples on a second L-edge remain inside the supplied
whole occurrence and Block. This getter returns only the selected original
SegmentSources view; it does not retag that previous origin or infer any
whole-trace identity from the parent-word transport.
-/
@[expose] def physicalOccurrence : Spine.Sources.ParentOccurrence
    (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
    (targets := targets) retained.parent :=
  Spine.Sources.parentOccurrence geometry.route.path geometry.route.within sourceOwner
    block.paid.spine sources index retained.position

/-- The complete selected physical tuple is the original readonly lookup at the SAME retained location. -/
theorem physicalOccurrence_selected : retained.physicalOccurrence.selected =
    Spine.Sources.selected geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position :=
  Spine.Sources.parentOccurrence_selected geometry.route.path geometry.route.within sourceOwner
    block.paid.spine sources index retained.position

/-- The original local child is read from the SAME physical position, independently of repeated coordinates. -/
theorem physicalOccurrence_child : retained.physicalOccurrence.child =
    Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position :=
  Spine.Sources.parentOccurrence_child geometry.route.path geometry.route.within sourceOwner
    block.paid.spine sources index retained.position

end SourceOccurrence

end Steps.Acquisition.Block

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
