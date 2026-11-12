module

public import
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints.CommonReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointCorners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.List.Membership
import Purelib.Polynomial.Geometry.Grid.FromPartition
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

/-! # Actual Point sources on the retained common-reading point bank

The common point occurrences determine a new local cut partition before
its rows are prepared. Original root-edge and coarse-restriction caches
remain inputs. Literal supplied Points are classified through those same
new rows, with their old Entry sheet derived by uniqueness on that Owner.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion (CellRows buildCellRows)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher} {faces : PuncturedFaces bank}
variable {frames : RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {parent : CenteredEdge curve differential} {target : Rational}
variable {cuts : List Rational} {partition : Geometry.Rectangle.AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval} {domains : FaceDomainBank frames faces.regulars}
variable {request : LocalRequest parent count target}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}
variable {retained : PrimitiveFragmentCell.RegularRequest domains request fragment location}
variable {upper : retained.UpperEndpoint} {parentSheet : Fin 2}
variable {lower : CoveredTracedPath retained.compared.acquired.inward.path
  (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index)}
variable {forward : CoveredTracedPath upper.acquired.outward.path
  (upper.acquired.faceFrame.owners upper.acquired.entry.sheet)}
variable {lowerParents : ParentCache lower differential parentSheet}
variable {upperParents : ParentCache forward differential parentSheet}

namespace PrimitiveFragmentCell.RegularRequest.UpperEndpoint.CommonReadings.Preparation

variable {tolerance : Rational} {positive : 0 < tolerance}
variable (prepared : Preparation (lowerParents := lowerParents) (upperParents := upperParents) tolerance positive)

/-- The literal first endpoint occurrence is in the SAME materialized common point bank. -/
theorem first_mem : fragment.first ∈ prepared.points := by
  have extra : fragment.first ∈ [fragment.first, location.face.cell.box.anchor, fragment.last] :=
    Membership.mem_cons.mpr (Or.inl rfl)
  exact Eq.mpr (congrArg (fun points : List Canonical => fragment.first ∈ points) prepared.points_eq)
    (List.mem_append_right _ (List.mem_append_right _ extra))

/-- The distinct literal last endpoint occurrence is retained even when its coordinate repeats the first. -/
theorem last_mem : fragment.last ∈ prepared.points := by
  have extra : fragment.last ∈ [fragment.first, location.face.cell.box.anchor, fragment.last] :=
    Membership.mem_cons.mpr (Or.inr (Membership.mem_cons.mpr
      (Or.inr (Membership.mem_cons.mpr (Or.inl rfl)))))
  exact Eq.mpr (congrArg (fun points : List Canonical => fragment.last ∈ points) prepared.points_eq)
    (List.mem_append_right _ (List.mem_append_right _ extra))

variable (old : RootEdgeBank frames) (coarse : frames.CellRestriction location.face.cell location.face.member)

/-- A new local partition and complete row bank retain the exact common points and old root inputs.

These are new finite cut/frame/row preparations. The previous CommonMesh,
Point caches, primitive anchors/offsets and any older local bank stay
independent inputs; no old bank is replaced by coordinate agreement.
-/
@[expose] def LocalRows :=
  Σ requested : {value : CutPartition location.face.cell.box prepared.points //
    value = CutPartition.build location.face.cell.box location.face.cell.box_proper prepared.points},
  {value : CellRows old location.face coarse requested.val //
    value = buildCellRows old location.face coarse requested.val}

/-- Choose the actual common cuts first, then prepare and retain the same local rows once. -/
def prepareRows : prepared.LocalRows old coarse :=
  let requested := CutPartition.build location.face.cell.box location.face.cell.box_proper prepared.points
  let rows := buildCellRows old location.face coarse requested
  ⟨⟨requested, rfl⟩, ⟨rows, rfl⟩⟩

namespace LocalRows

variable {prepared old coarse} (cached : prepared.LocalRows old coarse)

/-- Read the SAME requested cut partition on the actual common point list. -/
abbrev cutPartition : CutPartition location.face.cell.box prepared.points := cached.1.val

/-- Read the complete new local bank, including its retained old root-edge bank and coarse restriction. -/
abbrev rows : CellRows old location.face coarse cached.cutPartition := cached.2.val

/-- The whole partition is its original factory on the identical retained common point bank. -/
theorem cutPartition_eq : cached.cutPartition =
    CutPartition.build location.face.cell.box location.face.cell.box_proper prepared.points := cached.1.property

/-- The whole row bank is its original once-built same-face preparation. -/
theorem rows_eq : cached.rows = buildCellRows old location.face coarse cached.cutPartition := cached.2.property

/-- Actual requested-point membership supplies both cut-axis occurrences in the SAME retained local grid. -/
theorem vertex {point : Canonical} (present : point ∈ prepared.points)
    (inside : location.face.cell.box.Contains point) : FromStates.ContainsVertex cached.rows.grid point :=
  ClearGrid.ofPartition_contains_of_eq cached.cutPartition location.face.clearance cached.rows.grid_eq
    point present inside

variable {point : Canonical} {sampleCount : Nat}
variable {neighborhood : ContinuedNeighborhood curve.polynomial sampleCount}

/-- One actual stem, Point classification and corner lift retain all original factories and derived sheet agreement.

The Point is supplied whole, with its literal coordinate and neighborhood.
The Entry is an actual old acquisition result on that same Owner. The
sheet equation is computed from the retained rows/selection and uniqueness;
it is not a desired relation supplied by the caller.
-/
@[expose] def PointLift (present : point ∈ prepared.points) (inside : location.face.cell.box.Contains point)
    (sample : ContinuedNeighborhood.Point neighborhood point)
    (known : Entry retained.compared.shared.models point sample.owner) (vertices : VertexBank cached.rows.grid) :=
  let member := cached.vertex present inside
  let anchor := FromStates.ContainsPathVertices.start cached.rows.grid cached.rows.boundary.path
    cached.rows.boundary_onGrid
  Σ stem : {value : Walks.Walk cached.rows.grid location.face.cell.box.anchor point //
    value = LoopMonodromy.Grid.connect cached.rows.grid location.face.cell.box.anchor point anchor member},
  Σ classified : {value : cached.rows.PointEntry retained.compared.shared.models stem.val member sample //
    value = cached.rows.classifyPoint retained.compared.shared.models stem.val member sample},
  {value : (Σ selected : {value : ClearGrid.CornerLocation cached.rows.grid point //
      value = cached.rows.locateCorner member},
    {value : classified.val.CellLift selected.val vertices //
      value = classified.val.liftAtCorner selected.val vertices}) //
    value = classified.val.liftAtVertex vertices ∧ classified.val.entry.sheet = known.sheet}

/-- Retain a new coordinate stem, actual Point selection and signed lift from the same old inputs. -/
private def liftPoint (present : point ∈ prepared.points) (inside : location.face.cell.box.Contains point)
    (sample : ContinuedNeighborhood.Point neighborhood point)
    (known : Entry retained.compared.shared.models point sample.owner) (vertices : VertexBank cached.rows.grid) :
    cached.PointLift present inside sample known vertices :=
  let member := cached.vertex present inside
  let anchor := FromStates.ContainsPathVertices.start cached.rows.grid cached.rows.boundary.path
    cached.rows.boundary_onGrid
  let stem := LoopMonodromy.Grid.connect cached.rows.grid location.face.cell.box.anchor point anchor member
  let classified := cached.rows.classifyPoint retained.compared.shared.models stem member sample
  let lifted := classified.liftAtVertex vertices
  have sameSheet : classified.entry.sheet = known.sheet := classified.sheet_eq known
  ⟨⟨stem, rfl⟩, ⟨⟨classified, rfl⟩, ⟨lifted, ⟨rfl, sameSheet⟩⟩⟩⟩

/-- Lift a literal first physical Point using only its original geometric endpoint readback.

The coordinate equation supplies list membership and containment. It
identifies no root Owners. The SAME supplied Point and actual old Entry
then determine their signed incidence by the original row operations.
-/
def firstSource (sample : ContinuedNeighborhood.Point neighborhood point) (atFirst : point = fragment.first)
    (known : Entry retained.compared.shared.models point sample.owner) (vertices : VertexBank cached.rows.grid) :
    cached.PointLift
      (Eq.mpr (congrArg (fun value : Canonical => value ∈ prepared.points) atFirst) prepared.first_mem)
      (Eq.mpr (congrArg location.face.cell.box.Contains atFirst) (fragment.regular_endpoints location).1)
      sample known vertices :=
  cached.liftPoint
    (Eq.mpr (congrArg (fun value : Canonical => value ∈ prepared.points) atFirst) prepared.first_mem)
    (Eq.mpr (congrArg location.face.cell.box.Contains atFirst) (fragment.regular_endpoints location).1)
    sample known vertices

/-- Lift the independent literal last physical Point without deduplicating repeated or stationary occurrences. -/
def lastSource (sample : ContinuedNeighborhood.Point neighborhood point) (atLast : point = fragment.last)
    (known : Entry retained.compared.shared.models point sample.owner) (vertices : VertexBank cached.rows.grid) :
    cached.PointLift
      (Eq.mpr (congrArg (fun value : Canonical => value ∈ prepared.points) atLast) prepared.last_mem)
      (Eq.mpr (congrArg location.face.cell.box.Contains atLast) (fragment.regular_endpoints location).2)
      sample known vertices :=
  cached.liftPoint
    (Eq.mpr (congrArg (fun value : Canonical => value ∈ prepared.points) atLast) prepared.last_mem)
    (Eq.mpr (congrArg location.face.cell.box.Contains atLast) (fragment.regular_endpoints location).2)
    sample known vertices

namespace PointLift

variable {cached} {present : point ∈ prepared.points} {inside : location.face.cell.box.Contains point}
variable {sample : ContinuedNeighborhood.Point neighborhood point}
variable {known : Entry retained.compared.shared.models point sample.owner} {vertices : VertexBank cached.rows.grid}
variable (source : cached.PointLift present inside sample known vertices)

/-- Read the SAME once-built oriented stem from the old face anchor to this literal Point. -/
abbrev stem : Walks.Walk cached.rows.grid location.face.cell.box.anchor point := source.1.val

/-- Read the complete once-built classification of the unchanged original Point. -/
abbrev classified : cached.rows.PointEntry retained.compared.shared.models source.stem
    (cached.vertex present inside) sample := source.2.1.val

/-- Read the actual original corner-incidence result, including its cached cell list and prefix. -/
abbrev cornerLocation : ClearGrid.CornerLocation cached.rows.grid point := source.2.2.val.1.val

/-- Read all four actual signed occurrences and both source-face IDs on the SAME cached Point selection. -/
abbrev lifted : source.classified.CellLift source.cornerLocation vertices := source.2.2.val.2.val

/-- The whole original Point cache is unchanged by its new local-bank classification. -/
theorem original_eq : source.classified.original = sample := source.classified.original_eq

/-- The complete stem is its original coordinate connector on these retained grid/endpoint occurrences. -/
theorem stem_eq : source.stem = LoopMonodromy.Grid.connect cached.rows.grid location.face.cell.box.anchor point
    (FromStates.ContainsPathVertices.start cached.rows.grid cached.rows.boundary.path cached.rows.boundary_onGrid)
    (cached.vertex present inside) := source.1.property

/-- The complete classifier is its original factory on that SAME cached stem and original Point. -/
theorem classified_eq : source.classified = cached.rows.classifyPoint retained.compared.shared.models
    source.stem (cached.vertex present inside) sample := source.2.1.property

/-- The complete corner/lift pair is the original one-time liftAtVertex factory. -/
theorem corners_eq : source.2.2.val = source.classified.liftAtVertex vertices := source.2.2.property.1

/-- Signed agreement with the literal old Point Entry is derived, retaining both actual owners/operations. -/
theorem sheet_eq : source.classified.entry.sheet = known.sheet := source.2.2.property.2

end PointLift
end LocalRows

end PrimitiveFragmentCell.RegularRequest.UpperEndpoint.CommonReadings.Preparation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
