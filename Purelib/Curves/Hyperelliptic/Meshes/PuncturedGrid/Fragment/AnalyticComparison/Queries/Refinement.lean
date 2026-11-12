module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Queries
public import Purelib.Geometry.Rectangle.AxisPartition.Refinement
public import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Data.List.Membership
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-! # Actual original readings and geometric preparation at a cached interior cut

The existing direct query, patch Point and original primitive cache remain
inputs. A three-point reading bank reuses the cut pair and computes only
its two endpoint pairs. One genuine extended partition and common mesh
retain the exact ordered first/cut/last requests and original cell owner.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.Topology.Mesh.CoordinateTriangulation (VertexLookup)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
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

namespace QueryCut

/-- The actual parent query inside this retained fragment belongs to the SAME original regular face. -/
theorem face_inside (inside : InFragment (interval := interval) (time := time)) :
    fragment.face.located.face.cell.box.Contains (parent.edge.point time) := by
  have first : fragment.face.located.face.cell.box.Contains fragment.located.first := by
    rewrite [fragment.face.located.cell_eq]
    exact fragment.first_inside
  have last : fragment.face.located.face.cell.box.Contains fragment.located.last := by
    rewrite [fragment.face.located.cell_eq]
    exact fragment.last_inside
  have line := Box.contains_line first last (parameter_inside inside)
  have same := (query_point (fragment := fragment) (time := time)).trans
    (PreparedSegmentCuts.point_eq_line _ _ _)
  exact same.symm ▸ line

end QueryCut

namespace QueryCut.Cache

/-- The exact original face Entry required at this actual retained query Owner.

An existing same-point Entry acquisition supplies this value without any
new owner selection. Its frame owner must be this literal domain-cache
owner; equal coordinates alone do not identify those models or entries.
-/
@[expose] def QueryEntry (query : PreparedEdge.Query parent.edge time timeInside) : Type :=
  Face.Entries.FaceModels.Entry (domainCache fragment domains).models (parent.edge.point time) query.owner

/-- Transport the supplied actual query Entry to the SAME retained patch Point using its already cached comparison. -/
def pointEntry (entry : QueryEntry (fragment := fragment) (domains := domains) query) :
    Face.Entries.FaceModels.Entry (domainCache fragment domains).models (parent.edge.point time)
      retained.point.owner :=
  ⟨entry.sheet, entry.reached.append (Face.Entries.Reached.ofEquivalent retained.compared)⟩

/-- Changing the presented Owner preserves the actual retained source-frame sheet, without another selector. -/
theorem pointEntry_sheet (entry : QueryEntry (fragment := fragment) (domains := domains) query) :
    (retained.pointEntry (data := data) entry).sheet = entry.sheet := by
  unfold pointEntry
  rfl

/-- Read the actual cached query-to-Point comparison in its original parent-query coordinates.

The original query-name readback transports the same retained comparison.
Neither a direct query nor a patch Point is acquired by this operation.
-/
def originalComparison : NamedEquivalent (parent.edge.rootName time timeInside)
    retained.point.certificate.value.name :=
  NamedEquivalent.transport query.name_eq.symm rfl retained.compared

/-- The exact retained patch Point has the original parent's query channel at the inserted global parameter.

Only the cached named comparison and original query name readback are
consumed. No direct-query or patch-point acquisition occurs in this proof.
-/
theorem point_original : Nonempty (NamedEquivalent (parent.edge.rootName time timeInside)
    retained.point.certificate.value.name) :=
  ⟨retained.originalComparison (data := data)⟩

/-- The original selected piece's first point, literal cut point and last point, in their actual order. -/
@[expose] def points (position : Fin 3) : Canonical :=
  if position.val = 0 then retained.location.piece.firstPoint
  else if position.val = 1 then parent.edge.point time
  else retained.location.piece.lastPoint

/-- Each of the three exact requested occurrences lies in the SAME selected original model cell. -/
theorem points_inside (position : Fin 3) :
    (assigned.domain.geometry.box retained.location.piece.column retained.location.piece.row).Contains
      (retained.points (data := data) position) := by
  unfold points
  split
  · exact retained.location.piece.first_inside
  · split
    · exact retained.query_point ▸ Box.contains_line retained.location.piece.first_inside
        retained.location.piece.last_inside retained.location.fraction_inside
    · exact retained.location.piece.last_inside

/-- Reuse the SAME cut pair at every repeated cut coordinate, evaluating only genuinely different endpoints. -/
@[expose] def pairAt (position : Fin 3) : Canonical × Canonical :=
  if position.val = 1 then retained.values
  else if retained.points (data := data) position = parent.edge.point time then retained.values
  else
    (data.primitives.value retained.location.piece.column retained.location.piece.row
      (retained.points (data := data) position),
      request.request.model.primitive.value.eval (retained.points (data := data) position))

/-- The ordered pair at each actual occurrence evaluates the two retained original polynomials there. -/
theorem pairAt_eq (position : Fin 3) : retained.pairAt (data := data) position =
    (data.primitives.value retained.location.piece.column retained.location.piece.row
      (retained.points (data := data) position),
      request.request.model.primitive.value.eval (retained.points (data := data) position)) := by
  by_cases middle : position.val = 1
  · have same : position = 1 := Fin.ext middle
    cases same
    change retained.values = _
    exact retained.values_eq
  · rewrite [pairAt, if_neg middle]
    split
    · rename_i same
      rewrite [same]
      exact retained.values_eq
    · rfl

/-- Cache the original two-polynomial values in first/cut/last occurrence order. -/
def pairs : Data.Vector (Canonical × Canonical) 3 := vectorOfFn (retained.pairAt (data := data))

/-- The whole exact pair bank retained at this preparation stage. -/
@[expose] def Pairs : Type :=
  {values : Data.Vector (Canonical × Canonical) 3 // values = retained.pairs (data := data)}

/-- Read a supplied cached pair through its whole factory equality. -/
theorem pairs_eq (values : retained.Pairs (data := data)) (position : Fin 3) : values.val position =
    (data.primitives.value retained.location.piece.column retained.location.piece.row
      (retained.points (data := data) position),
      request.request.model.primitive.value.eval (retained.points (data := data) position)) := by
  have original := congrArg (fun values : Data.Vector (Canonical × Canonical) 3 => values position)
    values.property
  unfold pairs at original
  rewrite [vectorOfFn_apply] at original
  exact original.trans (retained.pairAt_eq (data := data) position)

/-- Construct original PointReadings from the actual cached pair bank and SAME old anchors and offsets.

No primitive polynomial, anchor, offset or cut evaluation is reconstructed.
The aligned value adds the retained offset to each supplied cached first
component; the second component remains the original request polynomial.
-/
def pointReadings (values : retained.Pairs (data := data)) :
    PointReadings data.anchors data.offsets (retained.points (data := data)) where
  owners := vectorOfFn fun position =>
    (⟨retained.location.piece.column, retained.location.piece.row, retained.points (data := data) position,
      retained.points_inside (data := data) position⟩ : OwnedVertex assigned.domain.geometry)
  point_eq := fun position => by rewrite [vectorOfFn_apply]; rfl
  values := vectorOfFn fun position =>
    data.offsets.values retained.location.piece.column retained.location.piece.row + (values.val position).1
  value_eq := fun position => by
    rewrite [vectorOfFn_apply, vectorOfFn_apply]
    change data.offsets.values retained.location.piece.column retained.location.piece.row + (values.val position).1 =
      data.offsets.values retained.location.piece.column retained.location.piece.row +
        data.primitives.value retained.location.piece.column retained.location.piece.row
          (retained.points (data := data) position)
    exact congrArg (fun value => data.offsets.values retained.location.piece.column retained.location.piece.row + value)
      (congrArg Prod.fst (retained.pairs_eq (data := data) values position))

/-- The exact list requested from the new geometric mesh preserves all three occurrences, even when points repeat. -/
@[expose] def pointList : List Canonical :=
  [retained.points (data := data) 0, retained.points (data := data) 1, retained.points (data := data) 2]

/-- Each original three-point occurrence belongs to the literal finite mesh-request list. -/
theorem pointList_mem (position : Fin 3) :
    retained.points (data := data) position ∈ retained.pointList (data := data) := by
  have zero : position.val = 0 ∨ position.val = 1 ∨ position.val = 2 := by omega0
  rcases zero with first | middle | last
  · have same : position = 0 := Fin.ext first
    cases same
    exact List.mem_cons_self
  · have same : position = 1 := Fin.ext middle
    cases same
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · have same : position = 2 := Fin.ext last
    cases same
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- A genuine new common mesh inside the SAME one selected model cell, containing every ordered cut request. -/
@[expose] def Mesh : Type :=
  CommonMesh assigned.domain.geometry [(retained.location.piece.column, retained.location.piece.row)]
    (retained.pointList (data := data))

/-- A complete original first-match vertex lookup at each requested occurrence of the new actual mesh. -/
@[expose] def Locations (mesh : retained.Mesh (data := data)) : Type 1 :=
  DependentVector (fun position : Fin 3 =>
    VertexLookup mesh.surface.mesh.vertices (retained.points (data := data) position))

/-- Select each requested point in the actual mesh, preserving the original first-match lookup result. -/
def locations (mesh : retained.Mesh (data := data)) : retained.Locations (data := data) mesh :=
  DependentVector.ofFn fun position => mesh.lookup (retained.points (data := data) position)
    (retained.pointList_mem (data := data) position)
    retained.location.piece.column retained.location.piece.row List.mem_cons_self
    (retained.points_inside (data := data) position)

/-- Retain new numerical readings, extended partition, its exact cut endpoint and the actual common-mesh lookups.

The old QueryCut cache and DomainPrimitives are indices, not executed
callbacks. This is a completed local geometric preparation, not a claim
that its new intervals already inhabit the old indexed LiftedFragment.
-/
@[expose] def Preparation : Type 1 :=
  Σ values : retained.Pairs (data := data),
  Σ _readings : {value : PointReadings data.anchors data.offsets (retained.points (data := data)) //
    value = retained.pointReadings (data := data) values},
  Σ fine : AxisPartition.Refinement partition [time],
  Σ _endpoint : {value : AxisPartition.Endpoint fine.val time //
    value = fine.val.endpoint time (fine.additional_mem List.mem_cons_self timeInside)},
  Σ mesh : {value : retained.Mesh (data := data) // value = CommonMesh.build assigned.domain.geometry
    [(retained.location.piece.column, retained.location.piece.row)] (retained.pointList (data := data))},
  {value : retained.Locations (data := data) mesh.val // value = retained.locations (data := data) mesh.val}

/-- Execute only the genuinely new finite reading and refinement operations once on these retained inputs. -/
def prepare : retained.Preparation (data := data) :=
  let values := retained.pairs (data := data)
  let cachedValues : retained.Pairs (data := data) := ⟨values, rfl⟩
  let readings := retained.pointReadings (data := data) cachedValues
  let fine := AxisPartition.Refinement.build partition [time]
  let endpoint := fine.val.endpoint time (fine.additional_mem List.mem_cons_self timeInside)
  let mesh := CommonMesh.build assigned.domain.geometry
    [(retained.location.piece.column, retained.location.piece.row)] (retained.pointList (data := data))
  let locations := retained.locations (data := data) mesh
  ⟨cachedValues, ⟨readings, rfl⟩, fine, ⟨endpoint, rfl⟩, ⟨mesh, rfl⟩, ⟨locations, rfl⟩⟩

namespace Preparation

variable {retained}
variable (prepared : retained.Preparation (data := data))

/-- Read the actual cached endpoint pairs and SAME retained middle pair. -/
@[expose] def values : retained.Pairs (data := data) := prepared.1

/-- Read the complete original numerical PointReadings on these same primitive owners. -/
@[expose] def readings : PointReadings data.anchors data.offsets (retained.points (data := data)) := prepared.2.1.val

/-- Read the complete new axis partition without claiming equality to the old axis-crossing partition. -/
@[expose] def fine : AxisPartition.Refinement partition [time] := prepared.2.2.1

/-- Read the exact original endpoint selector at the inserted cut. -/
@[expose] def endpoint : AxisPartition.Endpoint prepared.fine.val time := prepared.2.2.2.1.val

/-- Read the actual common geometry on the retained single original cell. -/
@[expose] def mesh : retained.Mesh (data := data) := prepared.2.2.2.2.1.val

/-- Read all original first-match vertex lookups, preserving ordered repeated requests. -/
@[expose] def locations : retained.Locations (data := data) prepared.mesh := prepared.2.2.2.2.2.val

/-- The whole original PointReadings constructor consumed the supplied cached pair bank. -/
theorem readings_eq : prepared.readings = retained.pointReadings (data := data) prepared.values := prepared.2.1.property

/-- Each retained numerical reading keeps the SAME selected original model column and row. -/
theorem reading_cell (position : Fin 3) :
    (prepared.readings.owners position).column = retained.location.piece.column ∧
      (prepared.readings.owners position).row = retained.location.piece.row := by
  have same := congrArg
    (fun readings : PointReadings data.anchors data.offsets (retained.points (data := data)) =>
      ((readings.owners position).column, (readings.owners position).row)) prepared.readings_eq
  rewrite [pointReadings, vectorOfFn_apply] at same
  exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

/-- The complete new partition is its original once-built extended-list factory. -/
theorem fine_eq : prepared.fine.val = AxisPartition.build 0 1 partition.proper
    (cuts ++ [time]) := prepared.fine.property

/-- The actual selected cut endpoint is the exact original finite selector on the retained partition. -/
theorem endpoint_eq : prepared.endpoint = prepared.fine.val.endpoint time
    (prepared.fine.additional_mem List.mem_cons_self timeInside) := prepared.2.2.2.1.property

/-- The whole common mesh is its original factory on the SAME selected old cell and ordered point requests. -/
theorem mesh_eq : prepared.mesh = CommonMesh.build assigned.domain.geometry
    [(retained.location.piece.column, retained.location.piece.row)] (retained.pointList (data := data)) :=
  prepared.2.2.2.2.1.property

/-- The complete lookup family is the original finite first-match worker on that SAME actual mesh. -/
theorem locations_eq : prepared.locations = retained.locations (data := data) prepared.mesh :=
  prepared.2.2.2.2.2.property

/-- Each cached original vertex lookup identifies the exact requested physical occurrence. -/
theorem coordinate_eq (position : Fin 3) :
    prepared.mesh.surface.mesh.coordinate (prepared.locations.get position).index =
      retained.points (data := data) position :=
  (prepared.locations.get position).coordinate_eq

/-- The retained cut pair is literally the supplied old query-cut pair, rather than a reevaluation there. -/
theorem cut_pair_eq : prepared.values.val 1 = retained.values := by
  have same := congrArg (fun values : Data.Vector (Canonical × Canonical) 3 => values (1 : Fin 3))
    prepared.values.property
  unfold pairs at same
  rewrite [vectorOfFn_apply] at same
  exact same

/-- Each actual aligned reading adds the SAME original cell offset to its retained raw primitive value. -/
theorem reading_eq (position : Fin 3) : prepared.readings.values position =
    data.offsets.values retained.location.piece.column retained.location.piece.row +
      (prepared.values.val position).1 := by
  have same := congrArg
    (fun readings : PointReadings data.anchors data.offsets (retained.points (data := data)) =>
      readings.values position) prepared.readings_eq
  rewrite [pointReadings, vectorOfFn_apply] at same
  exact same

/-- Reading increments cancel only their SAME retained cell offset, preserving both actual endpoint pairs. -/
theorem increment_eq (first last : Fin 3) :
    prepared.readings.values last - prepared.readings.values first =
      (prepared.values.val last).1 - (prepared.values.val first).1 := by
  have scalar (offset a b : Canonical) : (offset + b) - (offset + a) = b - a := by ring1
  exact (congrArg₂ (fun a b => a - b)
    (reading_eq (retained := retained) (prepared := prepared) last)
    (reading_eq (retained := retained) (prepared := prepared) first)).trans (scalar _ _ _)

/-- The first actual cached endpoint pair evaluates the SAME original two polynomials at the retained first point. -/
theorem first_pair_eq : prepared.values.val 0 =
    (data.primitives.value retained.location.piece.column retained.location.piece.row
      retained.location.piece.firstPoint,
      request.request.model.primitive.value.eval retained.location.piece.firstPoint) := by
  have same := congrArg (fun values : Data.Vector (Canonical × Canonical) 3 => values (0 : Fin 3))
    prepared.values.property
  unfold pairs at same
  rewrite [vectorOfFn_apply] at same
  exact same.trans (retained.pairAt_eq (data := data) 0)

/-- The last actual cached endpoint pair evaluates the SAME original two polynomials at the retained last point. -/
theorem last_pair_eq : prepared.values.val 2 =
    (data.primitives.value retained.location.piece.column retained.location.piece.row
      retained.location.piece.lastPoint,
      request.request.model.primitive.value.eval retained.location.piece.lastPoint) := by
  have same := congrArg (fun values : Data.Vector (Canonical × Canonical) 3 => values (2 : Fin 3))
    prepared.values.property
  unfold pairs at same
  rewrite [vectorOfFn_apply] at same
  exact same.trans (retained.pairAt_eq (data := data) 2)

/-- The first new aligned reading increment keeps the original request increment and its actual partial error. -/
theorem before_eq :
    (prepared.readings.values 1 - prepared.readings.values 0) -
      ((prepared.values.val 1).2 - (prepared.values.val 0).2) =
      QueryCut.Cache.beforeError retained := by
  rewrite [prepared.increment_eq, prepared.cut_pair_eq, prepared.first_pair_eq]
  rfl

/-- The second new aligned reading increment keeps the SAME original request increment and complementary error. -/
theorem after_eq :
    (prepared.readings.values 2 - prepared.readings.values 1) -
      ((prepared.values.val 2).2 - (prepared.values.val 1).2) =
      QueryCut.Cache.afterError retained := by
  rewrite [prepared.increment_eq, prepared.last_pair_eq, prepared.cut_pair_eq]
  rfl

/-- The first actual reading increment pays the two OLD residual indices and its exact squared cut fraction. -/
theorem before_le (bounds : FragmentBounds assigned.domain.patch differential) :
    normSq ((prepared.readings.values 1 - prepared.readings.values 0) -
      ((prepared.values.val 1).2 - (prepared.values.val 0).2)) ≤
      AnalyticComparison.pieceCharge assigned bounds retained.location.piece index *
        retained.location.fraction ^ 2 := by
  have original := QueryCut.Cache.before_le retained bounds
  exact (congrArg (fun error => normSq error ≤
    AnalyticComparison.pieceCharge assigned bounds retained.location.piece index * retained.location.fraction ^ 2)
    prepared.before_eq.symm).mp original

/-- The second actual reading increment pays the SAME OLD residual indices and complementary squared cut fraction. -/
theorem after_le (bounds : FragmentBounds assigned.domain.patch differential) :
    normSq ((prepared.readings.values 2 - prepared.readings.values 1) -
      ((prepared.values.val 2).2 - (prepared.values.val 1).2)) ≤
      AnalyticComparison.pieceCharge assigned bounds retained.location.piece index *
        (1 - retained.location.fraction) ^ 2 := by
  have original := QueryCut.Cache.after_le retained bounds
  exact (congrArg (fun error => normSq error ≤
    AnalyticComparison.pieceCharge assigned bounds retained.location.piece index *
      (1 - retained.location.fraction) ^ 2) prepared.after_eq.symm).mp original

/-- The new intervals retain the exact ordered refinement of every old interval, with the cut occurrence present. -/
theorem intervals_eq : prepared.fine.val.intervals = partition.intervals.flatMap (fun interval =>
    prepared.fine.val.intervals.filter (fun fine => decide
      (interval.lower ≤ fine.lower ∧ fine.upper ≤ interval.upper))) := prepared.fine.intervals_eq

end Preparation
end QueryCut.Cache
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

end
