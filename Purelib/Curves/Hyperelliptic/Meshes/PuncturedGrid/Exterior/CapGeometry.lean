module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Orientation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedExteriorPathGeometry
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCaps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
import Init.Core
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

public section

/-!
# Cached reciprocal coordinates on the actual exterior attachment

The finite fan vertices receive the original boundary's inverse coordinates
and distinct apex indices at coordinate zero. Every actual cap triangle has
strictly positive projected coordinate area. Original source coordinates
are cached alongside the inverses; radial refinement follows each actual
inverse boundary arc. In odd degree this is the
projection to w, not yet the ramified chart t with t² = w; no primitive-energy
positivity or straight-path substitution is asserted here.
-/

open Purelib
open Purelib.Curves
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration.Energy
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.Walks.Walk
open Purelib.Riemann
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedExteriorPathGeometry
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Boundary
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)

namespace Purelib.Polynomial.Geometry.Grid.Walks.Walk.Edgewise

open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Paths.PreparedExteriorPathGeometry.ClearPath (OnBoxSides)

/-- Every original grid-walk edge lies on one ambient box side when its clear path has that side property. -/
theorem sameSide {polynomial : ClearPath.GaussianPolynomial} {ambient : Rational.Box} {grid :
  ClearGrid polynomial ambient} :
    {start finish : Data.Gaussian.Basic.Canonical} → (walk : Walks.Walk grid start finish) → ClearPath.OnBoxSides
      ambient walk.path →
      walk.Edgewise (PreparedBoundarySegments.SameSide ambient)
  | _, _, .nil _, _ => trivial
  | _, _, .cons _ tail, sides => ⟨sides.1, sameSide tail sides.2⟩

end Purelib.Polynomial.Geometry.Grid.Walks.Walk.Edgewise

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram exteriorWalk_sides)

/-- Each actual indexed exterior-period edge retains the original ambient box-side relation. -/
theorem indexed_sameSide {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
    {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
    (program : PeriodPrograms.ExteriorProgram lifted differential) : ∀ edge ∈ program.indexed,
    PreparedBoundarySegments.SameSide (Cuts.Ambient curve)
      (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish) :=
  Edgewise.indexed lifted.edges lifted.vertices program.period.closed.walk
    (Polynomial.Geometry.Grid.Walks.Walk.Edgewise.sameSide _ (by
        rw [program.walk_eq];
        exact PeriodPrograms.exteriorWalk_sides base)) program.sheet

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Topology.Surface.Boundary.BoundaryCaps
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry (source point)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential}

/-- Every retained exterior attachment edge has strictly positive reciprocal cap orientation. -/
theorem words_reciprocal_oriented (attached : AllSurfacePreparation.CapAttachment prepared) : ∀ word ∈ attached.words, ∀
  edge ∈ word,
    0 < AffineTriangle.coordinateTriangleArea 0 (lifted.vertices.coordinate edge.finish)⁻¹ (lifted.vertices.coordinate
      edge.start)⁻¹ := by
  intro word member edge edgeMember
  rw [attached.words_eq] at member
  obtain ⟨component, _, equal⟩ := Map.mem_map.mp member
  rw [← equal, component.prepared.occurrences_eq] at edgeMember
  exact component.program.indexed_reciprocal_oriented edge edgeMember

/-- Both original inverse endpoint coordinates of every retained attachment edge lie in the reciprocal disk. -/
theorem words_reciprocal_inside (attached : AllSurfacePreparation.CapAttachment prepared) : ∀ word ∈ attached.words, ∀
  edge ∈ word,
    Reciprocal.Bounds.InDisk curve.polynomial (lifted.vertices.coordinate edge.finish)⁻¹ ∧
      Reciprocal.Bounds.InDisk curve.polynomial (lifted.vertices.coordinate edge.start)⁻¹ := by
  intro word member edge edgeMember
  rw [attached.words_eq] at member
  obtain ⟨component, _, equal⟩ := Map.mem_map.mp member
  rw [← equal, component.prepared.occurrences_eq] at edgeMember
  have boundary := component.program.indexed_boundary edge edgeMember
  exact ⟨ReciprocalExteriorCollar.inverse_inDisk curve boundary.2, ReciprocalExteriorCollar.inverse_inDisk curve
    boundary.1⟩

/-- Every retained cap edge keeps its original same-side ambient endpoints and strict source orientation. -/
theorem words_source (attached : AllSurfacePreparation.CapAttachment prepared) : ∀ word ∈ attached.words, ∀ edge ∈ word,
    (Cuts.Ambient curve).Contains (lifted.vertices.coordinate edge.finish) ∧
    (Cuts.Ambient curve).Contains (lifted.vertices.coordinate edge.start) ∧
    PreparedBoundarySegments.SameSide (Cuts.Ambient curve)
      (lifted.vertices.coordinate edge.finish) (lifted.vertices.coordinate edge.start) ∧
    0 < AffineTriangle.coordinateTriangleArea 0 (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate
      edge.finish) := by
  intro word member edge edgeMember
  rw [attached.words_eq] at member
  obtain ⟨component, _, equal⟩ := Map.mem_map.mp member
  rw [← equal, component.prepared.occurrences_eq] at edgeMember
  have boundary := component.program.indexed_boundary edge edgeMember
  refine ⟨boundary.2.1, boundary.1.1, ?_, component.program.indexed_oriented edge edgeMember⟩
  rcases component.program.indexed_sameSide edge edgeMember with side | side | side | side
  · exact Or.inl ⟨side.2, side.1⟩
  · exact Or.inr (Or.inl ⟨side.2, side.1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨side.2, side.1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨side.2, side.1⟩))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment in
/-- A triangle predicate on the original boundary edges transports to every actual fan triangle whose retained apex
coordinate is zero. -/
theorem fans_property {original target : Nat} (predicate : Gaussian → Gaussian → Gaussian → Prop)
    (coordinates : Fin target → Gaussian)
    (vertex : Fin original → Fin target) (words : List (List (Stokes.OrientedEdge original)))
    (apices : Fin words.length → Fin target) (apices_zero : ∀ index, coordinates (apices index) = 0)
    (oriented : ∀ word ∈ words, ∀ edge ∈ word,
      predicate 0 (coordinates (vertex edge.finish)) (coordinates (vertex edge.start))) :
    ∀ triangle ∈ BoundaryCaps.fans vertex words apices,
      predicate (coordinates triangle.first) (coordinates triangle.second) (coordinates triangle.third) := by
  induction words with
  | nil => intro triangle member; exact (List.not_mem_nil member).elim
  | cons word words ih =>
      intro triangle member
      rcases Data.List.Membership.mem_append.mp member with member | member
      · obtain ⟨edge, member, equal⟩ := Map.mem_map.mp member
        obtain ⟨original, member, mapped⟩ := Map.mem_map.mp member
        rw [← equal, ← mapped]
        change predicate (coordinates (apices 0)) (coordinates (vertex original.finish)) (coordinates (vertex
          original.start))
        rw [apices_zero]
        exact oriented word List.mem_cons_self original member
      · exact ih (fun index => apices index.succ) (fun index => apices_zero index.succ)
          (fun other member => oriented other (List.mem_cons_of_mem word member)) triangle member

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment in

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment in
set_option genInjectivity false in
/-- Coordinates are evaluated once and kept with pointwise specifications and the orientation proof for every retained
cap triangle. -/
structure ReciprocalGeometry (attached : AllSurfacePreparation.CapAttachment prepared) where
  /-- The cached original boundary coordinates with a separate zero coordinate at each retained apex index. -/
    sourceCoordinates : Data.Vector Gaussian (lifted.vertices.count + attached.words.length)
  /-- Each original embedded boundary vertex keeps exactly its source coordinate. -/ source_vertex_eq : ∀ index,
    sourceCoordinates (vertex index) = lifted.vertices.coordinate index
  /-- Each distinct retained apex has original source coordinate zero. -/ source_apex_eq : ∀ index, sourceCoordinates
    (CapAttachment.apex index) = 0
  /-- Each actual cap triangle retains its two source endpoints on the same ambient boundary side. -/ source_boundary :
    ∀ triangle ∈ attached.caps,
    (Cuts.Ambient curve).Contains (sourceCoordinates triangle.second) ∧
    (Cuts.Ambient curve).Contains (sourceCoordinates triangle.third) ∧
    PreparedBoundarySegments.SameSide (Cuts.Ambient curve)
      (sourceCoordinates triangle.second) (sourceCoordinates triangle.third)
  /-- The actual cap triangle's source endpoints have the retained strict boundary orientation. -/ source_positive : ∀
    triangle ∈ attached.caps,
    0 < AffineTriangle.coordinateTriangleArea 0 (sourceCoordinates triangle.third) (sourceCoordinates triangle.second)
  /-- The cached inverse coordinates of the original retained source vector. -/ coordinates : Data.Vector
    Gaussian (lifted.vertices.count + attached.words.length)
  /-- Every inverse-coordinate cache entry is exactly the inverse of its original source coordinate. -/ inverse_eq : ∀
    index, coordinates index = (sourceCoordinates index)⁻¹
  /-- Each original embedded boundary vertex has its exact inverse coordinate. -/ vertex_eq : ∀ index, coordinates
    (vertex index) = (lifted.vertices.coordinate index)⁻¹
  /-- Each distinct retained cap apex has inverse coordinate zero. -/ apex_eq : ∀ index, coordinates (CapAttachment.apex
    index) = 0
  /-- All three actual coordinates of every retained cap triangle lie in the reciprocal disk. -/ inside : ∀ triangle ∈
    attached.caps,
    Reciprocal.Bounds.InDisk curve.polynomial (coordinates triangle.first) ∧
      Reciprocal.Bounds.InDisk curve.polynomial (coordinates triangle.second) ∧
      Reciprocal.Bounds.InDisk curve.polynomial (coordinates triangle.third)
  /-- Every retained projected cap triangle has strictly positive coordinate area. -/ positive : ∀ triangle ∈
    attached.caps,
    0 < AffineTriangle.coordinateTriangleArea (coordinates triangle.first) (coordinates triangle.second) (coordinates
      triangle.third)

constructive_injectivity ReciprocalGeometry

namespace ReciprocalGeometry

variable {attached : CapAttachment
  prepared}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
  CapAttachment in
/-- Cache the original source and inverse coordinates once, retaining exact vertex/apex readbacks and every actual
triangle's orientation. -/
@[expose] def build (attached : AllSurfacePreparation.CapAttachment prepared) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
  attached := by
  let sourceCoordinates := Data.Vector.Basic.vectorOfFn (fun index : Fin (lifted.vertices.count + attached.words.length)
    =>
    if inside : index.val < lifted.vertices.count then lifted.vertices.coordinate ⟨index.val, inside⟩ else 0)
  have sourceVertexEq (index : Fin lifted.vertices.count) : sourceCoordinates (vertex index) =
    lifted.vertices.coordinate index := by
    rw [Data.Vector.Basic.vectorOfFn_apply]
    change (if inside : index.val < lifted.vertices.count then lifted.vertices.coordinate ⟨index.val, inside⟩ else 0) =
      _
    rw [dif_pos index.isLt]
  have sourceApexEq (index : Fin attached.words.length) : sourceCoordinates (CapAttachment.apex index) = 0 := by
    rw [Data.Vector.Basic.vectorOfFn_apply]
    change (if inside : lifted.vertices.count + index.val < lifted.vertices.count then
      lifted.vertices.coordinate ⟨lifted.vertices.count + index.val, inside⟩ else 0) = 0
    rw [dif_neg (Nat.not_lt.mpr (Nat.le_add_right _ _))]
  have sourceValid : ∀ triangle ∈ attached.caps,
      ((Cuts.Ambient curve).Contains (sourceCoordinates triangle.second) ∧
        (Cuts.Ambient curve).Contains (sourceCoordinates triangle.third) ∧
        PreparedBoundarySegments.SameSide (Cuts.Ambient curve)
          (sourceCoordinates triangle.second) (sourceCoordinates triangle.third)) ∧
      0 < AffineTriangle.coordinateTriangleArea 0 (sourceCoordinates triangle.third) (sourceCoordinates triangle.second)
        := by
    rw [attached.caps_eq]
    apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.fans_property (fun
      _ second third =>
      ((Cuts.Ambient curve).Contains second ∧ (Cuts.Ambient curve).Contains third ∧
        PreparedBoundarySegments.SameSide (Cuts.Ambient curve) second third) ∧
      0 < AffineTriangle.coordinateTriangleArea 0 third second) sourceCoordinates vertex attached.words
        CapAttachment.apex sourceApexEq
    intro word member edge edgeMember
    rw [sourceVertexEq, sourceVertexEq]
    have source := attached.words_source word member edge edgeMember
    exact ⟨⟨source.1, source.2.1, source.2.2.1⟩, source.2.2.2⟩
  let coordinates := Data.Vector.Basic.vectorOfFn (fun index => (sourceCoordinates index)⁻¹)
  have inverseEq (index : Fin (lifted.vertices.count + attached.words.length)) :
      coordinates index = (sourceCoordinates index)⁻¹ := Data.Vector.Basic.vectorOfFn_apply _ index
  have vertexEq (index : Fin lifted.vertices.count) : coordinates (vertex index) = (lifted.vertices.coordinate index)⁻¹
    := by
    rw [inverseEq, sourceVertexEq]
  have apexEq (index : Fin attached.words.length) : coordinates (CapAttachment.apex index) = 0 := by
    rw [inverseEq, sourceApexEq, Data.Gaussian.Field.inv_eq, Data.Gaussian.Field.inv_zero]
  refine ⟨sourceCoordinates, sourceVertexEq, sourceApexEq, (fun triangle member => (sourceValid triangle member).1),
    (fun triangle member => (sourceValid triangle member).2), coordinates, inverseEq, vertexEq, apexEq, ?_, ?_⟩
  · rw [attached.caps_eq]
    apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.fans_property (fun
      first second third => Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial first ∧
      Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial second ∧
        Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial third)
      coordinates vertex attached.words CapAttachment.apex apexEq
    intro word member edge edgeMember
    rw [vertexEq, vertexEq]
    refine ⟨?_, attached.words_reciprocal_inside word member edge edgeMember⟩
    unfold Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds.InDisk
    rw [Data.Gaussian.Norm.Basic.normSq_zero, mul_zero]
    decide
  · rw [attached.caps_eq]
    apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.fans_property (fun
      first second third => 0 < AffineTriangle.coordinateTriangleArea first second third)
      coordinates vertex attached.words CapAttachment.apex apexEq
    intro word member edge edgeMember
    rw [vertexEq, vertexEq]
    exact attached.words_reciprocal_oriented word member edge edgeMember

/-- Radial contraction of the actual inverse source edge. The outer edge retains the inverse arc, with the cap's
reversed boundary orientation. -/
@[expose] def point (geometry :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
  attached)
    (triangle : Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length))
    (radial transverse : Fraction.Rational) : Gaussian :=
  ReciprocalRadialGeometry.point (geometry.sourceCoordinates triangle.second)
    (geometry.sourceCoordinates triangle.third) ⟨radial, transverse⟩

/-- At radial parameter one, the retained cap point is exactly the inverse of the original affine source edge. -/
theorem point_outer (geometry :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
  attached)
    (triangle : Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)) (transverse :
      Fraction.Rational) :
    geometry.point triangle 1 transverse = (ReciprocalRadialGeometry.source
      (geometry.sourceCoordinates triangle.second) (geometry.sourceCoordinates triangle.third) transverse)⁻¹ :=
  ReciprocalRadialGeometry.outer _ _ _

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry in
/-- Every unit radial and transverse parameter remains in the reciprocal disk of the original retained cap triangle. -/
theorem point_inside (geometry :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
  attached)
    (triangle : Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)) (member : triangle ∈
      attached.caps)
    {radial transverse : Fraction.Rational} (radialUnit : 0 ≤ radial ∧ radial ≤ 1)
    (transverseUnit : 0 ≤ transverse ∧ transverse ≤ 1) :
    Reciprocal.Bounds.InDisk curve.polynomial (geometry.point triangle radial transverse) := by
  have source := geometry.source_boundary triangle member
  exact ReciprocalRadialGeometry.point_inside source.1 source.2.1 source.2.2 ⟨radialUnit.1, radialUnit.2,
    transverseUnit⟩

/-- The existing shared cap sample is bounded on the whole projected fan, using its already retained regular-disk
certificate. -/
theorem factor_bound (geometry :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
  attached)
    (triangle : Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)) (member : triangle ∈
      attached.caps)
    {index : Nat} {box : Rational.Box} (sample : Primitives.Sample cap differential index box)
    {radial transverse : Fraction.Rational} (radialUnit : 0 ≤ radial ∧ radial ≤ 1)
    (transverseUnit : 0 ≤ transverse ∧ transverse ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (sample.factor.eval (geometry.point triangle radial transverse)) ≤
      regular.factorUpper :=
  regular.factor_bound sample (geometry.point_inside triangle member radialUnit transverseUnit)

end ReciprocalGeometry
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
