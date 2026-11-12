module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Queries.Refinement
public import Purelib.Riemann.Readings.RectangularPointReadings.Mesh
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.Owners
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic

/-! # New-cut mesh readings from the same retained three-point preparation

The original preparation already owns a new common mesh and all three
vertex locations. This operation reuses its complete PointReadings and
those exact locations. It does not look up the cut again or evaluate its
primitive/query pair again. Only previously unrequested mesh vertices
receive new evaluations on the SAME anchors and offsets.
-/

public section

open Purelib.Riemann.Integration.RectangularSharedPrimitives renaming SharedPrimitiveValues -> SharedValues

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {differential : Differential genus}
variable {axes : PrimitiveAxes base.bank.grid} {parent : CenteredEdge curve differential}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}
variable {domains : FaceDomainBank frames base.faces.regulars} {count : Nat} {target : Rational}
variable {request : LocalRequest parent count target}
variable (assigned : SheetEntry fragment domains request)
variable {index : Nat}
variable (data : DomainPrimitives assigned.domain differential index)
variable {time : Rational} {timeInside : 0 ≤ time ∧ time ≤ 1}
variable {query : PreparedEdge.Query parent.edge time timeInside}
variable {inside : QueryCut.InFragment (interval := interval) (time := time)}
variable {assigned data}
variable (retained : QueryCut.Cache assigned data.primitives query inside)

namespace QueryCut.Cache.Preparation

variable {retained}
variable (prepared : retained.Preparation (data := data))

/-- The actual original first/cut/last occurrence is present in the retained common mesh. -/
theorem point_mem (position : Fin 3) :
    retained.points (data := data) position ∈ prepared.mesh.surface.mesh.vertices := by
  have member : prepared.mesh.surface.mesh.coordinate (prepared.locations.get position).index ∈
      prepared.mesh.surface.mesh.vertices := List.getElem_mem _
  exact prepared.coordinate_eq position ▸ member

/-- The retained point Owner and its cached mesh location use the SAME coordinate and numerical model cell.

The full mesh factory identity supplies the coarse indices; the stored
location supplies the exact coordinate. These are numerical-model owner
readbacks, without a square-root Owner identification.
-/
theorem sameLocation (position : Fin 3) :
    prepared.readings.SameLocation
      (prepared.mesh.surface.owners (prepared.locations.get position).index) position := by
  have meshCell := CommonMesh.owner_cell prepared.mesh prepared.mesh_eq (prepared.locations.get position).index
  have pointCell := prepared.reading_cell position
  exact ⟨pointCell.1.trans meshCell.1.symm, pointCell.2.trans meshCell.2.symm,
    (prepared.readings.point_eq position).trans
      ((prepared.mesh.surface.point_eq (prepared.locations.get position).index).trans
        (prepared.coordinate_eq position)).symm⟩

/-- The exact retained old point bank and materialized same-location selections on its new mesh. -/
@[expose] def MeshReadings : Type := prepared.readings.OnMesh prepared.mesh.surface

/-- Attach the already prepared three-point bank once, evaluating only unmatched new mesh vertices. -/
def acquireMesh : prepared.MeshReadings :=
  PointReadings.OnMesh.build prepared.readings prepared.mesh.surface

/-- The mesh attachment is exactly its original constructor on the supplied retained point bank and surface. -/
theorem acquireMesh_eq : prepared.acquireMesh =
    PointReadings.OnMesh.build prepared.readings prepared.mesh.surface := by
  unfold acquireMesh
  rfl

variable (sampled : prepared.MeshReadings)

/-- Each original endpoint/cut occurrence takes a retained-reading branch, including repeated coordinates. -/
theorem selected_ne_none (position : Fin 3) :
    sampled.selected.val (prepared.locations.get position).index ≠ none :=
  PointReadings.OnMesh.selected_ne_none sampled position (prepared.locations.get position).index
    (prepared.sameLocation position)

/-- The actual new mesh scalar at every retained endpoint/cut occurrence is its SAME old cached aligned reading. -/
theorem mesh_value_eq (position : Fin 3) :
    sampled.shared.values (prepared.locations.get position).index = prepared.readings.values position :=
  sampled.cached_eq position (prepared.locations.get position).index (prepared.sameLocation position)

/-- The original coordinate-reading operation uses actual vertex membership and the SAME retained old scalar. -/
theorem atPoint_eq (position : Fin 3) :
    SharedValues.atPoint sampled.shared
      (retained.points (data := data) position) = prepared.readings.values position := by
  have actual := SharedValues.atPoint_coordinate sampled.shared
    (prepared.locations.get position).index
  have location := congrArg
    (SharedValues.atPoint sampled.shared) (prepared.coordinate_eq position)
  exact location.symm.trans (actual.trans (prepared.mesh_value_eq sampled position))

/-- The inserted cut reads its actual cached primitive pair plus the SAME original selected-cell offset. -/
theorem atPoint_cut_eq :
    SharedValues.atPoint sampled.shared (parent.edge.point time) =
      data.offsets.values retained.location.piece.column retained.location.piece.row + retained.values.1 := by
  have original := prepared.atPoint_eq sampled 1
  change SharedValues.atPoint sampled.shared (parent.edge.point time) =
    prepared.readings.values 1 at original
  exact original.trans ((prepared.reading_eq 1).trans
    (congrArg (fun pair : Canonical × Canonical =>
      data.offsets.values retained.location.piece.column retained.location.piece.row + pair.1) prepared.cut_pair_eq))

/-- Every same-cell mesh increment is the original retained three-point reading increment. -/
theorem mesh_increment_eq (first last : Fin 3) :
    SharedValues.atPoint sampled.shared
        (retained.points (data := data) last) -
      SharedValues.atPoint sampled.shared
        (retained.points (data := data) first) =
      prepared.readings.values last - prepared.readings.values first :=
  congrArg₂ (fun lastValue firstValue => lastValue - firstValue)
    (prepared.atPoint_eq sampled last) (prepared.atPoint_eq sampled first)

/-- The mesh's first partial increment retains the original request polynomial and its actual cached cut error. -/
theorem mesh_before_eq :
    (SharedValues.atPoint sampled.shared
        (retained.points (data := data) 1) -
      SharedValues.atPoint sampled.shared
        (retained.points (data := data) 0)) -
      ((prepared.values.val 1).2 - (prepared.values.val 0).2) = QueryCut.Cache.beforeError retained :=
  (congrArg (fun increment => increment - ((prepared.values.val 1).2 - (prepared.values.val 0).2))
    (prepared.mesh_increment_eq sampled 0 1)).trans prepared.before_eq

/-- The mesh's second partial increment retains the SAME request polynomial and complementary cached error. -/
theorem mesh_after_eq :
    (SharedValues.atPoint sampled.shared
        (retained.points (data := data) 2) -
      SharedValues.atPoint sampled.shared
        (retained.points (data := data) 1)) -
      ((prepared.values.val 2).2 - (prepared.values.val 1).2) = QueryCut.Cache.afterError retained :=
  (congrArg (fun increment => increment - ((prepared.values.val 2).2 - (prepared.values.val 1).2))
    (prepared.mesh_increment_eq sampled 1 2)).trans prepared.after_eq

/-- The first mesh partial increment pays the original old residuals and exact squared cut fraction. -/
theorem mesh_before_le (bounds : FragmentBounds assigned.domain.patch differential) :
    normSq ((SharedValues.atPoint sampled.shared
        (retained.points (data := data) 1) -
      SharedValues.atPoint sampled.shared
        (retained.points (data := data) 0)) -
      ((prepared.values.val 1).2 - (prepared.values.val 0).2)) ≤
      AnalyticComparison.pieceCharge assigned bounds retained.location.piece index *
        retained.location.fraction ^ 2 := by
  have original := QueryCut.Cache.before_le retained bounds
  exact (congrArg (fun error => normSq error ≤
    AnalyticComparison.pieceCharge assigned bounds retained.location.piece index * retained.location.fraction ^ 2)
    (prepared.mesh_before_eq sampled).symm).mp original

/-- The complementary mesh partial increment pays the SAME old residuals and complementary squared fraction. -/
theorem mesh_after_le (bounds : FragmentBounds assigned.domain.patch differential) :
    normSq ((SharedValues.atPoint sampled.shared
        (retained.points (data := data) 2) -
      SharedValues.atPoint sampled.shared
        (retained.points (data := data) 1)) -
      ((prepared.values.val 2).2 - (prepared.values.val 1).2)) ≤
      AnalyticComparison.pieceCharge assigned bounds retained.location.piece index *
        (1 - retained.location.fraction) ^ 2 := by
  have original := QueryCut.Cache.after_le retained bounds
  exact (congrArg (fun error => normSq error ≤
    AnalyticComparison.pieceCharge assigned bounds retained.location.piece index *
      (1 - retained.location.fraction) ^ 2) (prepared.mesh_after_eq sampled).symm).mp original

end QueryCut.Cache.Preparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

end
