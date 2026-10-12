module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedMesh
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing

/-!
# Shared face-corner data on every actual lifted triangle

Both triangles of a face/sheet read the same four-value cache. The finite
triangle vector is materialized once by arithmetic indexing; source-edge
readback identifies exactly the increments used by cut-period comparisons.
-/

section

open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (corner)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Topology.Mesh.QuadrilateralDual
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitives FacePrimitiveBank)

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.FaceCorners

/-- Read one retained triangle's three values from its original four-corner face cache. -/
@[expose] def triangleValues (values : PrimitiveSewing.PrimitiveValues 4) (upper : Bool) :
  PrimitiveSewing.PrimitiveValues 3 :=
  Data.Vector.Basic.vectorOfFn fun index => values (SewnPrimitiveFaces.corner (FaceCorners.triangle upper) index)

/-- A retained triangle edge reads the same oriented increment as its original face-corner edge. -/
theorem triangle_increment (values : PrimitiveSewing.PrimitiveValues 4) (kind : RectangleEdge.Kind) :
    triangleValues values
      (QuadOccurrence.upperSide kind) (FaceCorners.lastCorner kind) -
      triangleValues values
        (QuadOccurrence.upperSide kind) (FaceCorners.firstCorner kind) =
        values (FaceCorners.quad.edge kind).finish - values (FaceCorners.quad.edge kind).start := by
  cases kind <;> simp only
    [triangleValues,
    Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] <;> rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.FaceCorners

end

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

/-- Decode the actual sheet index from the retained arithmetic triangle index. -/
@[expose] def sheet {count : Nat} (triangle : Fin count) : Fin 2 := ⟨triangle.val % 4 / 2, by omega⟩

/-- Decode whether the retained arithmetic triangle index denotes the upper triangle. -/
@[expose] def upper {count : Nat} (triangle : Fin count) : Bool := decide (triangle.val % 2 = 1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

end

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}
  {domains : FaceDomainBank frames faces.regulars}
    {differential : Differential genus} {index : Nat}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives

/-- Transporting the cached face owner preserves the exact corner readings on each sheet. -/
theorem castFace_corners
  {first last : PuncturedGridFaces.RegularFace bank} (equal : first = last) {domains : DomainBanks.FaceDomains frames
  first}
    {differential : Differentials.Basic.Differential genus} {index : Nat} (cached : PrimitiveData.FacePrimitives domains
      differential index) (sheet : Fin 2) :
    ((cached.castFace equal).atSheet sheet).corners.values = (cached.atSheet sheet).corners.values := by
  cases equal
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank

/-- Reading the primitive bank through a route preserves the original bounded-position corner cache. -/
theorem atRoute_corners
  (cached : PrimitiveData.FacePrimitiveBank differential index domains)
    {edge : Stokes.OrientedEdge vertices.count} (route : MeshPathWalks.EdgeRoute mesh edge) :
    ((cached.atRoute route).atSheet route.sheet).corners.values = ((cached.get route.position).atSheet
      route.sheet).corners.values :=
  PrimitiveData.FacePrimitives.castFace_corners route.face_eq (cached.get
    route.position) route.sheet

/-- A routed edge increment reads the exact retained face-position, sheet and oriented corner pair. -/
theorem edgeIncrement_eq
  (cached : PrimitiveData.FacePrimitiveBank differential index domains)
    {edge : Stokes.OrientedEdge vertices.count} (route : MeshPathWalks.EdgeRoute mesh edge) :
    cached.edgeIncrement route =
      ((cached.get route.position).atSheet route.sheet).corners.values route.corners.finish -
        ((cached.get route.position).atSheet route.sheet).corners.values route.corners.start :=
  congrArg (fun values : PrimitiveSewing.PrimitiveValues 4 => values route.corners.finish - values route.corners.start)
    (cached.atRoute_corners route)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings

set_option genInjectivity false in
/-- Cached three-corner readings for every retained lifted triangle.

The materialized vector retains the mesh's original triangle indices. Its
readback field certifies each entry against the same face-sheet corner cache. -/
structure TriangleReadings (cached : PrimitiveData.FacePrimitiveBank differential index domains) (mesh :
  GridLiftedMesh.LiftedMesh vertices edges faces) where
  /-- The cached three-corner readings for every actual retained lifted triangle. -/ values : Data.Vector
    (PrimitiveSewing.PrimitiveValues 3) mesh.triangles.length
  /-- Each indexed triangle reads exactly its original face-sheet four-corner cache. -/ values_eq : ∀ position sheet
    upper, values (mesh.triangleIndex position sheet upper) =
    FaceCorners.triangleValues ((cached.get
      position).atSheet sheet).corners.values upper

constructive_injectivity TriangleReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

/-- Decode the actual retained regular-face position from the bounded triangle index. -/
@[expose] def position (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (triangle : Fin mesh.triangles.length) :
  Fin faces.regulars.length :=
  ⟨triangle.val / 4, by have := triangle.isLt.trans_eq mesh.faceCount; omega⟩

/-- Decoding an actual constructed triangle index recovers its original face position. -/
private theorem position_eq (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (face : Fin faces.regulars.length)
  (which : Fin 2) (high : Bool) :
    position mesh
      (mesh.triangleIndex face which high) = face := by
  apply Fin.ext
  have := which.isLt
  cases high <;> simp only
    [position,
    LiftedMesh.triangleIndex, if_neg (by decide : ¬ false = true), if_pos (Eq.refl true), -eq_self, -iff_self] <;> omega

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

/-- Decoding an actual constructed triangle index recovers its original sheet. -/
private theorem sheet_eq (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (face : Fin faces.regulars.length)
  (which : Fin 2) (high : Bool) :
    sheet (mesh.triangleIndex face which high) = which := by
  apply Fin.ext
  have := which.isLt
  cases high <;> simp only [sheet, LiftedMesh.triangleIndex, if_neg (by decide : ¬ false = true), if_pos (Eq.refl true),
    -eq_self, -iff_self] <;> omega

/-- Decoding an actual constructed triangle index recovers its original upper/lower flag. -/
private theorem upper_eq (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (face : Fin faces.regulars.length)
  (which : Fin 2) (high : Bool) :
    upper (mesh.triangleIndex face which high) = high := by
  cases high
  · apply decide_eq_false
    simp only [LiftedMesh.triangleIndex, if_neg (by decide : ¬ false = true), -eq_self, -iff_self]
    omega
  · apply decide_eq_true
    simp only [LiftedMesh.triangleIndex, if_pos (Eq.refl true), -eq_self, -iff_self]
    omega

/-- Materialize the triangle reading vector once from the exact retained face-sheet corner caches. -/
@[expose] def build (cached : PrimitiveData.FacePrimitiveBank differential index domains) (mesh :
  GridLiftedMesh.LiftedMesh vertices edges faces) :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings cached mesh where
  values := Data.Vector.Basic.vectorOfFn fun triangle =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.FaceCorners.triangleValues ((cached.get
      (position mesh
      triangle)).atSheet (sheet
      triangle)).corners.values
      (upper triangle)
  values_eq := by
    intro face which high
    rw [Data.Vector.Basic.vectorOfFn_apply]
    rw [position_eq,
      sheet_eq,
      upper_eq]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

end

variable {cached : FacePrimitiveBank differential
  index domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

/-- The actual located source-edge increment equals the retained face-corner increment. -/
theorem location_increment (readings :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings cached mesh) {edge :
  Stokes.OrientedEdge vertices.count}
    (location : LiftedFaces.EdgeLocation mesh.lifts edge) :
    location.sourceEdge.increment readings.values = cached.edgeIncrement (.forward location) := by
  unfold SewnPrimitiveContacts.SourceEdge.increment LiftedFaces.EdgeLocation.sourceEdge
  rw [readings.values_eq,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.FaceCorners.triangle_increment]
  exact (cached.edgeIncrement_eq (.forward location)).symm

/-- Forward and backward routed source occurrences read their exact oriented retained face-corner increments. -/
theorem route_increment (readings : TrianglePrimitiveReadings.TriangleReadings
  cached mesh) {edge : Stokes.OrientedEdge vertices.count}
    (route : MeshPathWalks.EdgeRoute mesh edge) : route.sourceEdge.increment readings.values = cached.edgeIncrement
      route := by
  cases route with
  | forward location => exact readings.location_increment location
  | backward location =>
      have forward := readings.location_increment location
      have reverse : (EdgeRoute.backward location).sourceEdge.increment readings.values =
          -location.sourceEdge.increment readings.values := by
        unfold EdgeRoute.sourceEdge SewnPrimitiveContacts.SourceEdge.increment
        ring1
      rw [reverse, forward]
      rw [cached.edgeIncrement_eq (.forward location),
        cached.edgeIncrement_eq (.backward location)]
      simp only [EdgeRoute.position,
        EdgeRoute.sheet,
        EdgeRoute.corners,
        Stokes.OrientedEdge.reverse_start,
        Stokes.OrientedEdge.reverse_finish, -eq_self, -iff_self]
      ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

end
end
