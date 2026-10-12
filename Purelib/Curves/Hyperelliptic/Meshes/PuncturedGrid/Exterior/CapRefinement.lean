module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

public section

/-!
# Refining the actual reciprocal cap triangles

One existing unit-square partition is shared by every coarse fan triangle.
Its indexed incidence is retained while the coordinates are mapped into the
actual reciprocal disk. Degenerate faces along the collapsed apex edge have
zero coordinate area; every other face keeps the original orientation.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared}
  {depth : Nat}

set_option genInjectivity false in
/-- The original unit-square mesh mapped into one actual reciprocal cap triangle.

The indexed incidence is retained, every vertex remains in the disk and every mapped face has nonnegative coordinate
area. -/
structure Refinement (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
    (coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)) (parameters :
      Path.Dyadic.RadialTriangles.Parameters depth) where
  /-- The cached mapped coordinates on the original indexed mesh. -/ coordinates : Data.Vector
    Gaussian.Basic.Canonical parameters.mesh.mesh.vertices.length
  /-- Each coordinate is the exact original reciprocal geometry map. -/ coordinates_eq : ∀ index, coordinates index =
    geometry.point coarse
    (parameters.mesh.mesh.coordinate index).re (parameters.mesh.mesh.coordinate index).im
  /-- Every mapped face vertex lies in the original reciprocal disk. -/ inside : ∀ face,
    Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial (coordinates (parameters.mesh.mesh.triangulation.faces
      face).first) ∧
      Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial (coordinates (parameters.mesh.mesh.triangulation.faces
        face).second) ∧
      Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial (coordinates (parameters.mesh.mesh.triangulation.faces
        face).third)
  /-- Every mapped face has nonnegative coordinate area, including collapsed apex faces. -/ nonnegative : ∀ face,
    0 ≤ Energy.AffineTriangle.coordinateTriangleArea (coordinates (parameters.mesh.mesh.triangulation.faces face).first)
      (coordinates (parameters.mesh.mesh.triangulation.faces face).second) (coordinates
        (parameters.mesh.mesh.triangulation.faces face).third)

constructive_injectivity Refinement

namespace Refinement

/-- Map the supplied shared radial parameters into the original retained cap triangle and retain its containment and
orientation proofs. -/
@[expose] def build (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
    (coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)) (member : coarse
      ∈ attached.caps)
    (parameters : Path.Dyadic.RadialTriangles.Parameters depth) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters := by
  let coordinates := Data.Vector.Basic.vectorOfFn (fun index => geometry.point coarse
    (parameters.mesh.mesh.coordinate index).re (parameters.mesh.mesh.coordinate index).im)
  have coordinatesEq (index : Fin parameters.mesh.mesh.vertices.length) : coordinates index = geometry.point coarse
      (parameters.mesh.mesh.coordinate index).re (parameters.mesh.mesh.coordinate index).im :=
        Data.Vector.Basic.vectorOfFn_apply _ index
  refine ⟨coordinates, coordinatesEq, ?_, ?_⟩
  · intro face
    have originals := parameters.mesh.mesh.face_coordinates face
    have sourceMember : (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
      parameters.mesh.partition.leaves)[face.val] ∈
        Rectangle.Partition.PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves := List.getElem_mem _
    have contained := Path.Dyadic.RadialTriangles.triangles_inside parameters.mesh.partition.leaves
      parameters.leaves_inside
      _ sourceMember
    have inside (point : Gaussian.Basic.Canonical) (included : Path.Dyadic.RadialTriangles.unitBox.Contains point) :
        Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial (geometry.point coarse point.re point.im) :=
      geometry.point_inside coarse member ⟨included.1, included.2.1⟩ included.2.2
    rw [coordinatesEq, coordinatesEq, coordinatesEq, originals.1, originals.2.1, originals.2.2]
    exact ⟨inside _ contained.1, inside _ contained.2.1, inside _ contained.2.2⟩
  · intro face
    have originals := parameters.mesh.mesh.face_coordinates face
    rw [coordinatesEq, coordinatesEq, coordinatesEq, originals.1, originals.2.1, originals.2.2]
    change 0 ≤ Rectangle.Partition.PreparedBoxTriangulation.coordinateArea
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.triangle
      (geometry.sourceCoordinates coarse.second) (geometry.sourceCoordinates coarse.third)
      (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves)[face.val])
    exact Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.triangles_nonnegative _ _ (geometry.source_positive
      coarse member).le
      parameters.mesh.partition.leaves parameters.leaves_inside _ (List.getElem_mem _)

/-- Both actual face-edge squared distances satisfy the original quarter-radius bound at the retained depth. -/
theorem distances {geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached}
    {coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)}
    {parameters : Path.Dyadic.RadialTriangles.Parameters depth} (refinement :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters)
    (member : coarse ∈ attached.caps) (face : Fin (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
      parameters.mesh.partition.leaves).length) :
    Data.Gaussian.Norm.Basic.normSq (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).second -
      refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) ≤
        Rational.Geometric.Basic.quarterRadius 64 depth ∧
    Data.Gaussian.Norm.Basic.normSq (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).third -
      refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) ≤
        Rational.Geometric.Basic.quarterRadius 64 depth := by
  have source := parameters.mesh.face_geometry face
  rw [parameters.parent_eq] at source
  have contained := geometry.source_boundary coarse member
  have estimate (left right : Fin parameters.mesh.mesh.vertices.length)
      (leftInside : Path.Dyadic.RadialTriangles.unitBox.Contains (parameters.mesh.mesh.coordinate left))
      (rightInside : Path.Dyadic.RadialTriangles.unitBox.Contains (parameters.mesh.mesh.coordinate right)) :
      Data.Gaussian.Norm.Basic.normSq (refinement.coordinates left - refinement.coordinates right) ≤
        32 * Data.Gaussian.Norm.Basic.normSq (parameters.mesh.mesh.coordinate left - parameters.mesh.mesh.coordinate
          right) := by
    rw [refinement.coordinates_eq, refinement.coordinates_eq]
    exact Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.point_distance contained.1 contained.2.1
      contained.2.2 _ _ leftInside rightInside
  have diameter : 32 * parameters.mesh.partition.leafDiagonalSq = Rational.Geometric.Basic.quarterRadius 64 depth := by
    rw [parameters.mesh.partition.leafDiagonalSq_eq, parameters.parent_eq, show
      Path.Dyadic.RadialTriangles.unitBox.diagonalSq = 2 by decide]
    simp only [Rational.Geometric.Basic.quarterRadius, Fraction.Field.div_eq_mul_inv_direct]
    ring1
  have secondBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct source.2.2.2.1
    (Fraction.Cast.Order.natCast_le_direct (by decide : 0 ≤ 32))
  have thirdBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct source.2.2.2.2
    (Fraction.Cast.Order.natCast_le_direct (by decide : 0 ≤ 32))
  refine ⟨?_, ?_⟩
  · exact (estimate _ _ source.2.1 source.1).trans (secondBound.trans_eq diameter)
  · exact (estimate _ _ source.2.2.1 source.1).trans (thirdBound.trans_eq diameter)

end Refinement
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
