module
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Geometry.EvaluationLower

import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Riemann.Meshes.RectangularObservationMesh
public import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Normalization.InverseModelDensity
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# Observation energy in actual shared local primitives

The coefficients are read from the retained polynomial primitive bank. Its
inverse-root residual certificate supplies the density lower bound; the
observation mesh supplies containment and exact area. The resulting estimate
uses the existing shared-value affine sample, paying its computed signed
error budget rather than assuming every sampled triangle is positive.
-/

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Box)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Polynomial.Geometry.EvaluationLower (GaussianVector)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_right)
open Purelib.Data.Vector.Basic (vectorOfFn_apply)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box : Box}

open Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

open Purelib.Integration in
/-- The coordinate area of an actual face in the retained observation surface. -/
def faceArea (mesh : ObservationMesh cuts box)
  (face : Fin (mesh.triangles.map ModelTriangle.triangle).length) : Coordinate :=
  let triangle := mesh.surface.mesh.triangulation.faces face
  Energy.AffineTriangle.coordinateTriangleArea (mesh.surface.mesh.coordinate triangle.first)
    (mesh.surface.mesh.coordinate triangle.second) (mesh.surface.mesh.coordinate triangle.third)

open Purelib.Geometry in
/-- The surface face area is exactly the corresponding original retained triangle's coordinate area. -/
theorem faceArea_eq (mesh : ObservationMesh
  cuts box) (face : Fin (mesh.triangles.map ModelTriangle.triangle).length) :
    mesh.faceArea face = Rectangle.Partition.PreparedBoxTriangulation.coordinateArea (mesh.triangles.map
      ModelTriangle.triangle)[face.val] := by
  have coordinates := mesh.surface.mesh.face_coordinates face
  dsimp only [faceArea]
  rw [coordinates.1, coordinates.2.1, coordinates.2.2]
  rfl

/-- Every actual observation face has strictly positive coordinate area. -/
theorem faceArea_positive (mesh :
  ObservationMesh cuts box) (face : Fin (mesh.triangles.map ModelTriangle.triangle).length) :
    0 < mesh.faceArea face := by
  rw [mesh.faceArea_eq]
  exact mesh.positive (List.getElem_mem _)

open Purelib.Algebra in
open Purelib.Geometry in
/-- The actual face areas sum exactly to the observation box content. -/
theorem faceArea_sum (mesh : ObservationMesh
  cuts box) : FiniteSum.Fin.sumFin mesh.faceArea = Rational.Box.Content.boxContent box := by
  calc
    _ = FiniteSum.Fin.sumFin (fun face : Fin (mesh.triangles.map ModelTriangle.triangle).length =>
        Rectangle.Partition.PreparedBoxTriangulation.coordinateArea (mesh.triangles.map
          ModelTriangle.triangle)[face.val]) :=
      FiniteSum.Fin.sumFin_congr mesh.faceArea_eq
    _ = _ := (Rectangle.Partition.PreparedBoxTriangulation.sumTriangleAreas_eq_sumFin _).symm.trans mesh.area_eq

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {models : Bank curve.polynomial
    geometry}
  {primitives : Primitives models (Purelib.Polynomial.Geometry.EvaluationLower.coefficientPolynomial coefficients)}
  {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- The actual face owner's primitive coefficient satisfies one quarter of the retained density lower bound.

The inverse-model residual and both original containment certificates supply the estimate for the cached polynomial
bank. -/
theorem coefficient_lower (cell :
  Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) (mesh : ObservationMesh cuts
  cell.box)
    (readings : SharedPrimitiveValues anchors offsets mesh.surface)
    (face : Fin (mesh.triangles.map ModelTriangle.triangle).length) :
    cell.densityLower / 4 ≤ Data.Gaussian.Norm.Basic.normSq (readings.faceCoefficients face) := by
  rw [SharedPrimitiveValues.faceCoefficients, Vector.Basic.vectorOfFn_apply, primitives.coefficient_eq]
  exact Normalization.InverseModelDensity.SurfaceCell.densityLower_le_inverseModel cell (models.ready
    (mesh.surface.faceSource face).column
    (mesh.surface.faceSource face).row).model (mesh.face_inside face).1 (mesh.surface.face_inside face).1

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Geometry in
/-- The retained affine sample energy dominates box content times one quarter of the density lower bound.

Positive actual face areas and their exact sum combine the original face-owner coefficient bounds. -/
theorem affineEnergy_lower (cell :
  Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) (mesh : ObservationMesh cuts
  cell.box)
    (readings : SharedPrimitiveValues anchors offsets mesh.surface) (radius : Coordinate) (positive : 0 < radius) :
    Rational.Box.Content.boxContent cell.box * (cell.densityLower / 4) ≤ (readings.sample radius positive).affineEnergy
      := by
  calc
    _ = FiniteSum.Fin.sumFin (fun face => mesh.faceArea face * (cell.densityLower / 4)) := by
      rw [FiniteSum.Fin.sumFin_mul_right, mesh.faceArea_sum]
    _ ≤ FiniteSum.Fin.sumFin (fun face => mesh.faceArea face * Data.Gaussian.Norm.Basic.normSq
      (readings.faceCoefficients face)) :=
      FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun face =>
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (mesh.coefficient_lower cell readings face) (mesh.faceArea_positive face).le)
    _ = _ := rfl

open Purelib.Curves in
open Purelib.Data in
open Purelib.Geometry in
/-- The observation-cell contribution minus the computed signed error is bounded by the actual boundary energy.

The same shared primitive bank and positive radius supply the affine sample, retaining its full error budget and
original observation mesh. -/
theorem
  contribution_sub_error_le_boundaryEnergy
  (cell : Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients)
    (mesh : ObservationMesh cuts cell.box) (readings : SharedPrimitiveValues anchors offsets mesh.surface)
    (radius : Coordinate) (positive : 0 < radius) :
    cell.toEnergyCell.contribution / 4 - (readings.sample radius positive).errorBudget ≤
      (readings.sample radius positive).boundaryArea.im / 4 := by
  have affine := mesh.affineEnergy_lower cell readings radius positive
  have shifted := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct affine (-(readings.sample radius
    positive).errorBudget)
  have equal : cell.toEnergyCell.contribution / 4 = Rational.Box.Content.boxContent cell.box * (cell.densityLower / 4)
    := by
    change (Rational.Box.Content.boxContent cell.box * cell.densityLower) / 4 = _
    simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [equal]
  exact shifted.trans (readings.sample radius positive).affineEnergy_sub_errorBudget_le_boundaryEnergy

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh
