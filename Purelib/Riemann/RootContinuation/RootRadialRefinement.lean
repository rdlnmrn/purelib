module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Tactic.Ring

public section

/-! # Indexed radial refinements of actual bounded root edges -/

namespace Purelib.Riemann.RootContinuation.RootRadialRefinement

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Integration.Path.Dyadic.RadialTriangles (Parameters unitBox triangles_inside)
open Purelib.Riemann.RootContinuation.RootRadialGeometry (point domain point_inside point_distance
  triangles_nonnegative)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {first last : Purelib.Data.Gaussian.Basic.Canonical} {depth : Nat}

open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
set_option genInjectivity false in
/-- Cached radial-fan coordinates with box containment and dyadic edge-distance bounds.

The coordinate bank reads the exact retained parameter mesh. Every face stays in the same containing box, and both edges
from its first vertex obey the depth-indexed quarter-radius bound. -/
structure BoundedRefinement (first last : Gaussian.Basic.Canonical) (parameters : Path.Dyadic.RadialTriangles.Parameters
  depth) where
  /-- The materialized Gaussian coordinates of all retained parameter vertices. -/ coordinates : Data.Vector
    Gaussian.Basic.Canonical parameters.mesh.mesh.vertices.length
  /-- Each cached coordinate is the radial map of that exact parameter vertex. -/ coordinates_eq : ∀ vertex, coordinates
    vertex = point first last (parameters.mesh.mesh.coordinate vertex)
  /-- Every face's three cached vertices lie in the retained radial containing box. -/ inside : ∀ face,
    domain.Contains (coordinates (parameters.mesh.mesh.triangulation.faces face).first) ∧
    domain.Contains (coordinates (parameters.mesh.mesh.triangulation.faces face).second) ∧
    domain.Contains (coordinates (parameters.mesh.mesh.triangulation.faces face).third)
  /-- Both face edges from the first vertex have quadrance bounded by quarterRadius 64 at the retained depth. -/
    distances : ∀ face,
    Data.Gaussian.Norm.Basic.normSq (coordinates (parameters.mesh.mesh.triangulation.faces face).second -
      coordinates (parameters.mesh.mesh.triangulation.faces face).first) ≤ Rational.Geometric.Basic.quarterRadius 64
        depth ∧
    Data.Gaussian.Norm.Basic.normSq (coordinates (parameters.mesh.mesh.triangulation.faces face).third -
      coordinates (parameters.mesh.mesh.triangulation.faces face).first) ≤ Rational.Geometric.Basic.quarterRadius 64
        depth

constructive_injectivity BoundedRefinement

namespace BoundedRefinement

open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Geometry in
/-- Materialize the bounded radial fan from its retained dyadic parameter mesh.

Both edge endpoints have quadrance at most two; the radial distance estimate and cached leaf diagonal give the finite
geometric bounds. -/
@[expose] def build (firstBound : Data.Gaussian.Norm.Basic.normSq first ≤ 2) (lastBound :
  Data.Gaussian.Norm.Basic.normSq last ≤ 2)
    (parameters : Path.Dyadic.RadialTriangles.Parameters depth) : BoundedRefinement first last parameters := by
  have firstCanonical := firstBound
  have lastCanonical := lastBound
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstCanonical lastCanonical
  let coordinates := Vector.Basic.vectorOfFn (fun vertex => point first last (parameters.mesh.mesh.coordinate vertex))
  have coordinatesEq (vertex : Fin parameters.mesh.mesh.vertices.length) :
      coordinates vertex = point first last (parameters.mesh.mesh.coordinate vertex) := Vector.Basic.vectorOfFn_apply _
        vertex
  refine ⟨coordinates, coordinatesEq, ?_, ?_⟩
  · intro face
    have originals := parameters.mesh.mesh.face_coordinates face
    have contained := Path.Dyadic.RadialTriangles.triangles_inside parameters.mesh.partition.leaves
      parameters.leaves_inside
      _ (List.getElem_mem (l := Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
        parameters.mesh.partition.leaves) face.isLt)
    rw [coordinatesEq, coordinatesEq, coordinatesEq, originals.1, originals.2.1, originals.2.2]
    exact ⟨point_inside firstCanonical lastCanonical contained.1, point_inside firstCanonical lastCanonical
      contained.2.1,
      point_inside firstCanonical lastCanonical contained.2.2⟩
  · intro face
    have source := parameters.mesh.face_geometry face
    rw [parameters.parent_eq] at source
    have estimate (left right : Fin parameters.mesh.mesh.vertices.length)
        (leftInside : Path.Dyadic.RadialTriangles.unitBox.Contains (parameters.mesh.mesh.coordinate left))
        (rightInside : Path.Dyadic.RadialTriangles.unitBox.Contains (parameters.mesh.mesh.coordinate right)) :
        Data.Gaussian.Norm.Basic.normSq (coordinates left - coordinates right) ≤ 32 *
          Data.Gaussian.Norm.Basic.normSq (parameters.mesh.mesh.coordinate left - parameters.mesh.mesh.coordinate
          right) := by
      rw [coordinatesEq, coordinatesEq]
      have scalar := point_distance firstCanonical lastCanonical _ _ leftInside rightInside
      simp only [← Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
            decide +kernel : (16 : Rat.Fraction.Rational) ≤ 32)
          (Gaussian.Norm.Basic.normSq_nonneg _))
    have diameter : 32 * parameters.mesh.partition.leafDiagonalSq = Rational.Geometric.Basic.quarterRadius 64 depth :=
      by
      rw [parameters.mesh.partition.leafDiagonalSq_eq, parameters.parent_eq,
        show Path.Dyadic.RadialTriangles.unitBox.diagonalSq = 2 by decide]
      simp only [Rational.Geometric.Basic.quarterRadius, Rat.Fraction.Field.div_eq_mul_inv_direct]
      ring1
    have secondBound := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct source.2.2.2.1
      (Rat.Fraction.Cast.Order.natCast_le_direct (by decide : 0 ≤ 32))
    have thirdBound := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct source.2.2.2.2
      (Rat.Fraction.Cast.Order.natCast_le_direct (by decide : 0 ≤ 32))
    exact ⟨(estimate _ _ source.2.1 source.1).trans (secondBound.trans_eq diameter),
      (estimate _ _ source.2.2.1 source.1).trans (thirdBound.trans_eq diameter)⟩

end BoundedRefinement

open Purelib.Integration in
open Purelib.Data in
set_option genInjectivity false in
/-- A bounded radial refinement with nonnegative oriented area at every face.

It retains the same materialized coordinates and geometry, adding the orientation certificate required by the area
claim. -/
structure Refinement (first last : Gaussian.Basic.Canonical) (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    extends BoundedRefinement first last parameters where
  /-- Each actual retained face has nonnegative coordinate triangle area. -/ nonnegative : ∀ face, 0 ≤
    Energy.AffineTriangle.coordinateTriangleArea
    (coordinates (parameters.mesh.mesh.triangulation.faces face).first)
    (coordinates (parameters.mesh.mesh.triangulation.faces face).second)
    (coordinates (parameters.mesh.mesh.triangulation.faces face).third)

constructive_injectivity Refinement

open Purelib.Integration in
open Purelib.Data in
open Purelib.Geometry in
/-- Add face-area positivity to the cached bounded radial fan.

The supplied endpoint cross energy is nonnegative, and the same parameter leaves retain their unit-box containment. -/
@[expose] def Refinement.build (firstBound : Data.Gaussian.Norm.Basic.normSq first ≤ 2) (lastBound :
  Data.Gaussian.Norm.Basic.normSq last ≤ 2)
    (oriented : 0 ≤ Energy.AffineTriangle.crossEnergy first last)
    (parameters : Path.Dyadic.RadialTriangles.Parameters depth) : Refinement first last parameters := by
  let geometry := BoundedRefinement.build firstBound lastBound parameters
  refine ⟨geometry, ?_⟩
  intro face
  have originals := parameters.mesh.mesh.face_coordinates face
  rw [geometry.coordinates_eq, geometry.coordinates_eq, geometry.coordinates_eq, originals.1, originals.2.1,
    originals.2.2]
  exact triangles_nonnegative first last oriented parameters.mesh.partition.leaves parameters.leaves_inside _
    (List.getElem_mem (l := Rectangle.Partition.PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves)
      face.isLt)
end Purelib.Riemann.RootContinuation.RootRadialRefinement
