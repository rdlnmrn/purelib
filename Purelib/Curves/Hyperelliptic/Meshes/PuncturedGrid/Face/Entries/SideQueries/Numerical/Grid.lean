module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.SideQueries.Numerical
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Acquisition
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Occurrence
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Position
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid

/-! # Literal canonical-grid fragment incidence for the same numerical side row

The original framed grid is a nominal input. Every parent point is inside
its ambient box by the retained subdivision's original theorem. Splitting,
location and classification run once; the same retained query then selects
only geometric metadata and original cached regular/hole payloads.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
  (PrimitiveFragmentCell PrimitiveFragmentCells LocatedPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenterStates CenteredEdge centeredEdges centeredEdges_point_contains)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace LocatedCell)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
variable {face : RegularFace base.bank.toBranchCellBank} {models : FaceModels frames face} {point : Canonical}
variable {inside : face.cell.box.Contains point} {sourceOwner : Owner (curve.polynomial.eval point)}

namespace SideQuery.Cache.Numerical

variable {acquired : Acquisition models inside sourceOwner} {side : GridSide}
variable {onSide : face.cell.OnSide point side}
variable {lifted : LiftedFace vertices edges face acquired.entry.sheet}
variable {differential : Differential genus} {notFinish : point ≠ side.finish face.cell.box}
variable {queried : SideQuery.Cache acquired side onSide lifted differential notFinish}
variable {centers : CenterStates curve differential acquired.entry.sheet
  (prepared acquired side lifted queried.connection).2.subdivision}
variable {bounds : Bounds queried.connection.forwardSegment} {mesh : Mesh bounds}
variable {covered : ∀ edge ∈ (prepared acquired side lifted queried.connection).2.subdivision.parameterEdges,
  edge ∈ mesh.edges}
variable {count : Nat} {target : Rational} {positive : 0 < target}
variable (numerics : SideQuery.Cache.Numerical queried centers bounds mesh covered count target positive)

/-- Read the identical original centered parent word indexing the retained numerical request bank. -/
@[expose] def parents
    (_numerics : SideQuery.Cache.Numerical queried centers bounds mesh covered count target positive) :
    List (CenteredEdge curve differential) :=
  centeredEdges curve differential acquired.entry.sheet
    (prepared acquired side lifted queried.connection).2.subdivision centers

/-- Every actual parent fraction lies in the SAME original canonical ambient by its stored subdivision certificate. -/
theorem point_inside (parent : CenteredEdge curve differential) (member : parent ∈ numerics.parents)
    (fraction : Rational) (bounded : 0 ≤ fraction ∧ fraction ≤ 1) :
    (Cuts.Ambient curve).Contains (parent.edge.point fraction) :=
  centeredEdges_point_contains curve differential
    (segment := queried.connection.forwardSegment) (within := (prepared acquired side lifted queried.connection).1)
    acquired.entry.sheet (prepared acquired side lifted queried.connection).2.subdivision centers
    parent member fraction bounded

/-- Both endpoints of every exact retained numerical parent lie in the original canonical grid ambient. -/
theorem endpoints_inside : ∀ parent ∈ numerics.parents,
    (Cuts.Ambient curve).Contains (parent.edge.point 0) ∧
      (Cuts.Ambient curve).Contains (parent.edge.point 1) :=
  fun parent member =>
    ⟨numerics.point_inside parent member 0 ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩,
      numerics.point_inside parent member 1 ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩⟩

variable (axes : PrimitiveAxes base.bank.grid)

/-- Original splits, locations and regular/hole outcomes of this SAME numerical parent word in the retained grid. -/
@[expose] def GridFragments :=
  LocatedPrimitiveSplits.Acquisition base axes numerics.parents numerics.endpoints_inside

/-- Split, locate and classify the exact original numerical parents once, without a paid/source/query replay. -/
def acquireGrid : GridFragments numerics axes :=
  LocatedPrimitiveSplits.Acquisition.build base axes numerics.parents numerics.endpoints_inside

namespace GridFragments

variable {numerics axes} (retained : GridFragments numerics axes)

/-- Read the complete original partitions on the same exact numerical parent word. -/
@[expose] def splits : PrimitiveSplits axes numerics.parents :=
  LocatedPrimitiveSplits.Acquisition.splits retained

/-- Read the complete original cell locations on those same cached partitions. -/
@[expose] def locations : LocatedPrimitiveSplits axes retained.splits :=
  LocatedPrimitiveSplits.Acquisition.locations retained

/-- Read the complete original regular/hole product, including each unchanged payload and list position. -/
@[expose] def classifications : LocatedPrimitiveSplits.Classifications base.faces retained.locations :=
  LocatedPrimitiveSplits.Acquisition.classifications retained

/-- The actual bounded parent position equals the raw accepted-request occurrence, including stationary prefixes. -/
@[expose] def parentIndex (_grid : GridFragments numerics axes) : Fin numerics.parents.length :=
  queried.location.centeredIndex differential acquired.entry.sheet centers

/-- Parent dispatch retains the original SideQuery raw request index. -/
theorem parentIndex_val : retained.parentIndex.val = queried.requestIndex.val :=
  queried.location.centeredIndex_val differential acquired.entry.sheet centers

/-- Read the original cached partition of the actual query's identical numerical parent. -/
@[expose] def partition : AxisPartition 0 1 (axes.parameters numerics.parent) :=
  retained.splits.partitionAt retained.parentIndex

/-- Read that parent's identical complete fragment-location spine. -/
@[expose] def fragments : PrimitiveFragmentCells axes numerics.parent retained.partition
    retained.partition.intervals := retained.locations.fragmentsAt retained.parentIndex

/-- Read that same parent's identical regular/hole classifications, without looking up any cell again. -/
@[expose] def classified : PrimitiveFragmentCells.Classifications base.faces retained.fragments :=
  retained.locations.classificationsAt base.faces retained.classifications retained.parentIndex

/-- Retain the original closed-interval query lookup and its literal interval-list position. -/
@[expose] def Focus :=
  Σ located : {value : AxisPartition.Located retained.partition queried.location.fraction //
    value = retained.partition.locate queried.location.fraction queried.location.inside},
  {position : {index : Fin retained.partition.intervals.length //
    retained.partition.intervals[index.val]'index.isLt = located.val.interval} //
    position = PreparedAxisPartitions.Interval.position located.val.interval
      retained.partition.intervals located.val.member}

/-- Locate the query interval once, then inspect only interval metadata to read its original cached occurrence. -/
def focus : Focus retained :=
  let located := retained.partition.locate queried.location.fraction queried.location.inside
  let position := PreparedAxisPartitions.Interval.position located.interval retained.partition.intervals located.member
  ⟨⟨located, rfl⟩, ⟨position, rfl⟩⟩

namespace Focus

variable {retained} (selected : Focus retained)

/-- Read the SAME original closed-interval choice, retaining its first-closed-upper-endpoint boundary rule. -/
@[expose] def location : AxisPartition.Located retained.partition queried.location.fraction := selected.1.val

/-- Read the exact original interval occurrence in this same retained parent partition. -/
@[expose] def index : Fin retained.partition.intervals.length := selected.2.val.val

/-- The geometric interval lookup is the complete original factory on the supplied cached partition and fraction. -/
theorem location_eq : selected.location =
    retained.partition.locate queried.location.fraction queried.location.inside := selected.1.property

/-- The exact cached interval at the retained position is the original lookup's whole chosen interval. -/
theorem interval_eq : retained.partition.intervals[selected.index.val]'selected.index.isLt =
    selected.location.interval := selected.2.val.property

/-- The metadata position is the complete finite reader result on the original selected interval and unchanged list. -/
theorem position_eq : selected.2.val = PreparedAxisPartitions.Interval.position selected.location.interval
    retained.partition.intervals selected.location.member := selected.2.property

/-- Read the whole original cached fragment at the literal selected parent/interval occurrence. -/
@[expose] def fragment : PrimitiveFragmentCell axes numerics.parent retained.partition
    (retained.partition.intervals[selected.index.val]'selected.index.isLt) :=
  retained.fragments.fragmentAt selected.index

/-- Read its SAME original regular/hole outcome and full payload from the retained classification cache. -/
@[expose] def classification : LocatedCell base.faces.regulars base.faces.holes selected.fragment.cell :=
  retained.fragments.classificationAt base.faces retained.classified selected.index

/-- The actual retained query fraction belongs to the identical original selected interval, including boundary ties. -/
theorem query_inside :
    (retained.partition.intervals[selected.index.val]'selected.index.isLt).lower ≤ queried.location.fraction ∧
      queried.location.fraction ≤
        (retained.partition.intervals[selected.index.val]'selected.index.isLt).upper :=
  selected.interval_eq.symm ▸ selected.location.inside

/-- The literal numerical query point lies in this SAME selected original fragment cell. -/
theorem query_point_inside : selected.fragment.cell.box.Contains
    (numerics.parent.edge.point queried.location.fraction) :=
  selected.fragment.point_inside queried.location.fraction selected.query_inside

/-- The SAME actual retained Entry point belongs to the selected cell, separately from its signed Owner transport. -/
theorem entry_point_inside : selected.fragment.cell.box.Contains point :=
  Eq.mp (congrArg selected.fragment.cell.box.Contains numerics.query_point) selected.query_point_inside

end Focus
end GridFragments
end SideQuery.Cache.Numerical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

end
