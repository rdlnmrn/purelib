module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.FaceEntries.Fragments
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Between
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # A retained query crop between the actual physical fragment Points

The supplied whole crop cache remains stored with its original endpoint
comparison functions. Its moving operation runs once on the retained
Queries. Two new joins attach the independent physical Points using their
already derived operational comparisons. The final path retains those
exact joins and moving path; it changes no Point, Entry or Query owner.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.FragmentSamples.FaceEntries

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
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent}
variable {physicalCount floor : Nat}
variable {covered : (patch.neighborhood physicalCount).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {bank : BranchCellBank (Fibre.frameCurve frame) branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}
variable {prepared : PreparedParent patch physicalCount floor covered targets}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {samples : FragmentSamples prepared fragment}
variable {localCount : Nat} {localTolerance : Rational} {request : LocalRequest parent localCount localTolerance}
variable {domains : FaceDomainBank frames faces.regulars}
variable {location : RegularLocation faces.regulars fragment.cell}
variable {regular : RegularRequest domains request fragment location} {upper : regular.UpperEndpoint}
variable {query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside}
variable (entries : samples.FaceEntries regular upper query)
variable (physical : PreparedTraceBudget.Trace.CropComparisons parent interval.lower interval.upper
  fragment.lower_inside fragment.upper_inside)

/-- One whole supplied crop, its actual moving path, both new joins and the resulting physical-Point-owned path.

The existing products and subtypes store each complete value with its
original factory equation. The supplied crop remains runtime data rather
than a factory expression used as a type-index reader. The two Point/Query
joins have separate signed evidence and are not identified with any old
regular-fragment or closing join.
-/
@[expose] def Crop :=
  Σ selected : {value : PreparedTraceBudget.Trace.CropComparisons parent interval.lower interval.upper
      fragment.lower_inside fragment.upper_inside // value = physical},
  Σ pieces : {values :
      OwnerPath (Fibre.frameCurve frame).polynomial
        (parent.edge.point interval.lower) query.owner (parent.edge.point interval.upper) upper.query.owner ×
      OwnerJoin samples.first.owner query.owner × OwnerJoin upper.query.owner samples.last.owner //
    values.1 = selected.val.2 query upper.query ∧
    values.2.1 = OwnerJoin.acquire samples.first.owner query.owner entries.queries.1.symm ∧
    values.2.2 = OwnerJoin.acquire upper.query.owner samples.last.owner entries.queries.2},
  {value : OwnerPath (Fibre.frameCurve frame).polynomial
      (parent.edge.point interval.lower) samples.first.owner (parent.edge.point interval.upper) samples.last.owner //
    value = .cons (OwnerLink.stationary (Fibre.frameCurve frame).polynomial
        (parent.edge.point interval.lower) pieces.val.2.1)
      (pieces.val.1.append
        (.cons (OwnerLink.stationary (Fibre.frameCurve frame).polynomial
          (parent.edge.point interval.upper) pieces.val.2.2)
          (.nil (parent.edge.point interval.upper) samples.last.owner)))}

namespace Crop

/-- Package the abstract original crop, joins and path with their whole construction equations.

All dependent endpoint Owners are supplied together before the result is
packed. The equations retain their original factories without converting
through a computed join or replaying its acquisition.
-/
private def ofParts
    (selected : PreparedTraceBudget.Trace.CropComparisons parent interval.lower interval.upper
      fragment.lower_inside fragment.upper_inside) (selectedEq : selected = physical)
    (moving : OwnerPath (Fibre.frameCurve frame).polynomial
      (parent.edge.point interval.lower) query.owner (parent.edge.point interval.upper) upper.query.owner)
    (movingEq : moving = selected.2 query upper.query)
    (source : OwnerJoin samples.first.owner query.owner)
    (sourceEq : source = OwnerJoin.acquire samples.first.owner query.owner entries.queries.1.symm)
    (target : OwnerJoin upper.query.owner samples.last.owner)
    (targetEq : target = OwnerJoin.acquire upper.query.owner samples.last.owner entries.queries.2)
    (path : OwnerPath (Fibre.frameCurve frame).polynomial
      (parent.edge.point interval.lower) samples.first.owner (parent.edge.point interval.upper) samples.last.owner)
    (pathEq : path = .cons (OwnerLink.stationary (Fibre.frameCurve frame).polynomial
      (parent.edge.point interval.lower) source)
      (moving.append (.cons (OwnerLink.stationary (Fibre.frameCurve frame).polynomial
        (parent.edge.point interval.upper) target) (.nil (parent.edge.point interval.upper) samples.last.owner)))) :
    entries.Crop physical :=
  ⟨⟨selected, selectedEq⟩, ⟨⟨moving, source, target⟩, movingEq, sourceEq, targetEq⟩, ⟨path, pathEq⟩⟩

/-- Run the supplied moving operation once, acquire its two physical endpoint joins, and retain their exact path.

The operation order is moving crop, source join, target join, path assembly.
No Query, Point, Entry, physical View or existing crop cache is acquired.
The retained supplied product still contains its old endpoint functions.
-/
def build : entries.Crop physical :=
  let moving := physical.2 query upper.query
  let source := OwnerJoin.acquire samples.first.owner query.owner entries.queries.1.symm
  let target := OwnerJoin.acquire upper.query.owner samples.last.owner entries.queries.2
  let path : OwnerPath (Fibre.frameCurve frame).polynomial
      (parent.edge.point interval.lower) samples.first.owner (parent.edge.point interval.upper) samples.last.owner :=
    .cons (OwnerLink.stationary (Fibre.frameCurve frame).polynomial (parent.edge.point interval.lower) source)
      (moving.append (.cons
        (OwnerLink.stationary (Fibre.frameCurve frame).polynomial (parent.edge.point interval.upper) target)
        (.nil (parent.edge.point interval.upper) samples.last.owner)))
  ofParts (frame := frame) (basis := basis) entries physical physical rfl moving rfl source rfl target rfl path rfl

variable {entries physical}
variable (cropped : entries.Crop physical)

/-- Read the whole supplied original crop product, including its actual source/moving/reset functions. -/
abbrev selected : PreparedTraceBudget.Trace.CropComparisons parent interval.lower interval.upper
    fragment.lower_inside fragment.upper_inside := cropped.1.val

/-- Read the single retained moving path on the two original Query Owners. -/
abbrev moving : OwnerPath (Fibre.frameCurve frame).polynomial
    (parent.edge.point interval.lower) query.owner (parent.edge.point interval.upper) upper.query.owner :=
  cropped.2.1.val.1

/-- Read the complete new lower physical-Point-to-Query join without acquiring another tail. -/
abbrev source : OwnerJoin samples.first.owner query.owner := cropped.2.1.val.2.1

/-- Read the separate complete upper Query-to-physical-Point join unchanged. -/
abbrev target : OwnerJoin upper.query.owner samples.last.owner := cropped.2.1.val.2.2

/-- Read the actual Point-owned path assembled from those exact three retained parts. -/
abbrev path : OwnerPath (Fibre.frameCurve frame).polynomial
    (parent.edge.point interval.lower) samples.first.owner (parent.edge.point interval.upper) samples.last.owner :=
  cropped.2.2.val

/-- The retained whole crop is literally the supplied original product. -/
theorem selected_eq : cropped.selected = physical := cropped.1.property

/-- The whole moving path is its once-executed operation on the retained original Queries. -/
theorem moving_eq : cropped.moving = cropped.selected.2 query upper.query := cropped.2.1.property.1

/-- The whole lower join uses the actual stored lower Query-to-Point comparison in reverse. -/
theorem source_eq : cropped.source =
    OwnerJoin.acquire samples.first.owner query.owner entries.queries.1.symm := cropped.2.1.property.2.1

/-- The whole upper join uses the stored forward upper Query-to-Point comparison. -/
theorem target_eq : cropped.target =
    OwnerJoin.acquire upper.query.owner samples.last.owner entries.queries.2 := cropped.2.1.property.2.2

/-- The whole Point-owned path retains both cached joins and the identical cached moving path in order. -/
theorem path_eq : cropped.path =
    .cons (OwnerLink.stationary (Fibre.frameCurve frame).polynomial
      (parent.edge.point interval.lower) cropped.source)
    (cropped.moving.append
      (.cons (OwnerLink.stationary (Fibre.frameCurve frame).polynomial
        (parent.edge.point interval.upper) cropped.target)
        (.nil (parent.edge.point interval.upper) samples.last.owner))) := cropped.2.2.property

/-- The actual endpoint handoffs add their two ordered occurrences without deleting moving or repeated vertices. -/
theorem vertices_eq : cropped.path.vertices =
    parent.edge.point interval.lower :: (cropped.moving.vertices ++ [parent.edge.point interval.upper]) := by
  have actual := congrArg
    (fun path : OwnerPath (Fibre.frameCurve frame).polynomial
      (parent.edge.point interval.lower) samples.first.owner
      (parent.edge.point interval.upper) samples.last.owner => path.vertices) cropped.path_eq
  have following := cropped.moving.append_vertices
    (.cons (OwnerLink.stationary (Fibre.frameCurve frame).polynomial
      (parent.edge.point interval.upper) cropped.target)
      (.nil (parent.edge.point interval.upper) samples.last.owner))
  change cropped.path.vertices = parent.edge.point interval.lower ::
    (cropped.moving.append
      (.cons (OwnerLink.stationary (Fibre.frameCurve frame).polynomial
        (parent.edge.point interval.upper) cropped.target)
        (.nil (parent.edge.point interval.upper) samples.last.owner))).vertices at actual
  exact actual.trans (congrArg (fun points : List Canonical => parent.edge.point interval.lower :: points) following)

/-- Acquire count-paid formal root observations on this SAME stored Point-owned path.

The original Acquisition retains the literal vertex list, chooses its
positive local request before observing, and stores the entire Spine.
Its error_lt bounds only the actual stationary root-expression jump sum;
it gives no moving integral estimate or analytic primitive normalization.
-/
def observeRoots (rootRequest : AccuracyRequest) :
    Primitive.Acquisition cropped.path (Primitive.Defined.generator cropped.path) rootRequest :=
  Primitive.Acquisition.build cropped.path (Primitive.Defined.generator cropped.path) rootRequest

end Crop

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.FragmentSamples.FaceEntries

end
