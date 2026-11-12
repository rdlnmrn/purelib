module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints.Crop
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Children
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Paths.RectangularSegmentSplitting

/-! # Strict child geometry on the SAME executed original parent crop

The whole selected SourcePair, old completed acquisition and both original
retained operation closures stay actual inputs. The child constructor reads
those exact closures; it never calls the selector or old crop acquisition.
Both new endpoint answers and every genuine geometric cache are passed to
the original child consumer in their actual construction order.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge edgeOfStep)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Data.List
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Branches
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval start)} {widthRequest : AccuracyRequest}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets originalPath stage} {accuracy : AccuracyRequest}

namespace PreparedParents.Trace.Physical.Comparison.EndpointPoints

variable {row : Row}
variable {retained : Acquisition.Segment (segment := segment) (within := within) (owner := sourceOwner) widthRequest}
variable {parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve frame) basis sheet count retained}
variable {prepared : PreparedParents (frame := frame) (basis := basis) parents.coveredParents floor targets}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable {observed : Primitive.Spine (row.expression parameter) accuracy retained.traced.trace.get}
variable {compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) row retained parents prepared allocation observed}
variable {index : Fin parents.covered.parents.length}
variable {firstQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge 0
  (parents.covered.parents[index.val]'index.isLt).edge.baseInside}
variable {lastQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge
  1 (of_decide_eq_true rfl)}
variable (kept : EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery)

namespace Cropped

variable {kept lower upper lowerInside upperInside comparisonRequest requested}
    (acquired : kept.Cropped lower upper lowerInside upperInside comparisonRequest requested)
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {bank : BranchCellBank (Fibre.frameCurve frame) branches higher}
    {rootFrames : RootFrames bank.grid} {face : RegularFace bank}
    (shared : Face.DomainBanks.FaceDomains rootFrames face)
    (ordered : lower ≤ upper)
    (firstInside : face.cell.box.Contains ((parents.covered.parents[index.val]'index.isLt).edge.point lower))
    (entered : Face.Entries.FaceModels.Entry.Acquisition shared.models firstInside
      acquired.acquisition.2.2.samples.1.val.owner)
    (domain : Face.Periods.PeriodDomain shared.models entered.entry.sheet)
    (split : RectangularSegmentSplitting.SegmentSplit domain.cuts
      ((parents.covered.parents[index.val]'index.isLt).edge.point lower)
      ((parents.covered.parents[index.val]'index.isLt).edge.point upper))
    (position : Fin split.pieces.length)

universe u

/-- Construct actual strict-child endpoint geometry using only this SAME completed source cache and selected View.

The exact original prefixes and all-source family are read from the stored
execution. Generic withChildLift binds the two original queryAt answers,
derives their endpoint incidences and selected-sheet transport, and builds
the actual chord lift. No selection, source preparation, original crop or
old observation is executed here.
-/
def withChildLift {Result : Type u}
    (consume : PreparedParent.Crop.Observation.Points.ChildConsumer
      (frame := frame) (basis := basis) (points := acquired.acquisition.2.2)
      shared acquired.prefixes ordered firstInside entered domain acquired.families split position Result) : Result :=
  PreparedParent.Crop.Observation.Points.withChildLift
    (frame := frame) (basis := basis) (points := acquired.acquisition.2.2)
    shared acquired.prefixes ordered firstInside entered domain acquired.families split position consume

end Cropped

end PreparedParents.Trace.Physical.Comparison.EndpointPoints

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
