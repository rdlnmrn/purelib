module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.FaceEntries.Fragments.Crop
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # Separate row observations on a retained physical fragment crop

The literal physical source pair, its whole old row Spine and the supplied
Point-owned crop remain inputs. One new row-expression Spine observes that
stored crop at the unchanged old accuracy. The original payment operation
checks its actual ordered occurrence count, retaining an unpaid allocation
when that old accuracy does not pay the requested target. This execution
is separate from both the old Spine and the crop's formal-root observer.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison.EndpointPoints

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (PrimitiveFragmentCell)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCell (RegularRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval start)} {widthRequest : AccuracyRequest}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {accuracy : AccuracyRequest} {row : Row}
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
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {bank : BranchCellBank (Fibre.frameCurve frame) branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}
variable {fragment : PrimitiveFragmentCell axes (parents.covered.parents[index.val]'index.isLt) partition interval}
variable {samples : PreparedParent.FragmentSamples kept.entry fragment}
variable {localCount : Nat} {localTolerance : Rational}
variable {request : LocalRequest (parents.covered.parents[index.val]'index.isLt) localCount localTolerance}
variable {domains : FaceDomainBank frames faces.regulars}
variable {location : RegularLocation faces.regulars fragment.cell}
variable {regular : RegularRequest domains request fragment location} {upper : regular.UpperEndpoint}
variable {query : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge
  interval.lower fragment.lower_inside}
variable {entries : samples.FaceEntries regular upper query}
variable {physical : PreparedTraceBudget.Trace.CropComparisons (parents.covered.parents[index.val]'index.isLt)
  interval.lower interval.upper fragment.lower_inside fragment.upper_inside}
variable (cropped : entries.Crop physical) (requested : AccuracyRequest)

/-- A new row observation and its allocation retain the original physical source pair, old Spine and whole crop.

The original containers preserve the independent caches and all factory
identities. The actual crop vertex list is retained before observing. Its
count includes both new endpoint handoffs, every moving-path occurrence,
and any stationary or repeated occurrences. No fixed three-link count is
assumed for a supplied crop operation.
-/
@[expose] def FragmentObservation :=
  Σ originals : {values : EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery ×
      Primitive.Spine (row.expression parameter) accuracy retained.traced.trace.get × entries.Crop physical //
    values = (kept, observed, cropped)},
  Σ vertices : {values : List Canonical // values = originals.val.2.2.path.vertices},
  Σ sampled : {value : Primitive.Spine (row.expression parameter) accuracy originals.val.2.2.path //
    value = Primitive.Spine.build (accuracy := accuracy) originals.val.2.2.path
      (Trace.defined row originals.val.2.2.path)},
  {value : Primitive.Spine.Payment sampled.val requested vertices.val.length //
    value = Primitive.Spine.Payment.build sampled.val requested vertices.val.length
      (congrArg List.length vertices.property).symm}

/-- Observe the same stored crop once at the old accuracy, then retain its actual finite allocation outcome.

The original old Spine, source pair and crop are retained literally. The
new Spine executes the row expression, using each exact Owner's original
denominator guard. The payment factory neither upgrades that accuracy nor
rebuilds any crop, Query, Point, Entry, OwnerJoin or source selection.
-/
def observeFragment : kept.FragmentObservation cropped requested :=
  let originals := (kept, observed, cropped)
  let vertices := cropped.path.vertices
  let sampled := Primitive.Spine.build (accuracy := accuracy) cropped.path (Trace.defined row cropped.path)
  let payment := Primitive.Spine.Payment.build sampled requested vertices.length rfl
  ⟨⟨originals, rfl⟩, ⟨vertices, rfl⟩, ⟨sampled, rfl⟩, ⟨payment, rfl⟩⟩

namespace FragmentObservation

variable {kept cropped requested}
variable (acquired : kept.FragmentObservation cropped requested)

/-- Read the whole original endpoint/source cache, including its unchanged complete covering pair. -/
abbrev source : EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery :=
  acquired.1.val.1

/-- Read the entire old physical row Spine with its exact original path, observations and accuracy. -/
abbrev old : Primitive.Spine (row.expression parameter) accuracy retained.traced.trace.get := acquired.1.val.2.1

/-- Read the whole original supplied crop and all of its retained comparison functions, paths and joins. -/
abbrev crop : entries.Crop physical := acquired.1.val.2.2

/-- Read the ordered crop occurrence list retained before the new observation execution. -/
abbrev vertices : List Canonical := acquired.2.1.val

/-- Read the separate new row-expression Spine on the identical retained crop at unchanged old accuracy. -/
abbrev sampled : Primitive.Spine (row.expression parameter) accuracy acquired.crop.path := acquired.2.2.1.val

/-- Read the original payment attempt, including its exact count, budgets, positive or negative allocation proof. -/
abbrev payment : Primitive.Spine.Payment acquired.sampled requested acquired.vertices.length :=
  acquired.2.2.2.val

/-- The complete original source pair, old Spine and supplied crop remain the same literal input values. -/
theorem originals_eq : (acquired.source, acquired.old, acquired.crop) = (kept, observed, cropped) :=
  acquired.1.property

/-- The new finite count belongs to the actual stored crop, preserving repeated and stationary occurrences. -/
theorem vertices_eq : acquired.vertices = acquired.crop.path.vertices := acquired.2.1.property

/-- The entire separate new row Spine is its original observation factory on the same stored crop. -/
theorem sampled_eq : acquired.sampled = Primitive.Spine.build (accuracy := accuracy) acquired.crop.path
    (Trace.defined row acquired.crop.path) := acquired.2.2.1.property

/-- The whole payment attempt uses that SAME new Spine and its actual cached occurrence count. -/
theorem payment_eq : acquired.payment = Primitive.Spine.Payment.build acquired.sampled requested
    acquired.vertices.length (congrArg List.length acquired.vertices_eq).symm := acquired.2.2.2.property

end FragmentObservation

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison.EndpointPoints

end
