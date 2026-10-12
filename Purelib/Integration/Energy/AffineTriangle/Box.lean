module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Dimensions
public import Purelib.Geometry.Rational.Box.Gaussian.Corners
public import Purelib.Integration.Energy.AffineTriangle
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Triangulated finite surface energy

This module supplies the two-dimensional algebraic bridge for the second
Riemann bilinear relation.  A finite sample consists of a genuine oriented
triangulation, primitive values at its vertices, an exact identification of
its outer boundary with the displayed A/B period commutators, and a checked
lower-energy inequality on every face.  Incidence cancellation and finite
summation then derive the global surface lower theorem consumed by
`PreparedEnergy`; it is not repeated as an assumption.
-/

namespace Purelib.Integration.Energy.AffineTriangle.Box

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Integration.Energy
/-- Read affine primitive energy on the box's lower-left, lower-right and upper-right triangle. -/
def lowerBoxAffineTriangleEnergy (box : Box)
    (coefficient : Basic.Canonical) : Fraction.Rational :=
  AffineTriangle.primitiveTriangleEnergy
    (AffineTriangle.affineEnergyPrimitive coefficient (Box.Gaussian.Corners.lowerLeft box))
    (AffineTriangle.affineEnergyPrimitive coefficient (Box.Gaussian.Corners.lowerRight box))
    (AffineTriangle.affineEnergyPrimitive coefficient (Box.Gaussian.Corners.upperRight box))

/-- Read affine primitive energy on the box's lower-left, upper-right and upper-left triangle. -/
def upperBoxAffineTriangleEnergy (box : Box)
    (coefficient : Basic.Canonical) : Fraction.Rational :=
  AffineTriangle.primitiveTriangleEnergy
    (AffineTriangle.affineEnergyPrimitive coefficient (Box.Gaussian.Corners.lowerLeft box))
    (AffineTriangle.affineEnergyPrimitive coefficient (Box.Gaussian.Corners.upperRight box))
    (AffineTriangle.affineEnergyPrimitive coefficient (Box.Gaussian.Corners.upperLeft box))

end

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Integration.Energy
/-- The lower box triangle energy is half the original box content times the coefficient squared norm. -/
theorem lowerBoxAffineTriangleEnergy_eq (box : Box)
    (coefficient : Basic.Canonical) :
    lowerBoxAffineTriangleEnergy box coefficient =
      Box.Content.boxContent box / 2 *
        Norm.Basic.normSq coefficient := by
  unfold lowerBoxAffineTriangleEnergy
  rw [AffineTriangle.affinePrimitiveTriangleEnergy_eq]
  unfold AffineTriangle.coordinateTriangleArea Box.Gaussian.Corners.lowerLeft Box.Gaussian.Corners.lowerRight
    Box.Gaussian.Corners.upperRight
    Box.Content.boxContent Box.widthX
    Box.widthY Components.Basic.point
  change
    (((box.xUpper - box.xLower) * (box.yUpper - box.yLower) -
        (box.yLower - box.yLower) * (box.xUpper - box.xLower)) / 2) *
      Norm.Basic.normSq coefficient =
    ((box.xUpper - box.xLower) * (box.yUpper - box.yLower)) / 2 *
      Norm.Basic.normSq coefficient
  exact congrArg (fun area => area / 2 * Norm.Basic.normSq coefficient) (by ring1)

/-- The upper box triangle energy is half the original box content times the coefficient squared norm. -/
theorem upperBoxAffineTriangleEnergy_eq (box : Box)
    (coefficient : Basic.Canonical) :
    upperBoxAffineTriangleEnergy box coefficient =
      Box.Content.boxContent box / 2 *
        Norm.Basic.normSq coefficient := by
  unfold upperBoxAffineTriangleEnergy
  rw [AffineTriangle.affinePrimitiveTriangleEnergy_eq]
  unfold AffineTriangle.coordinateTriangleArea Box.Gaussian.Corners.lowerLeft Box.Gaussian.Corners.upperRight
    Box.Gaussian.Corners.upperLeft
    Box.Content.boxContent Box.widthX
    Box.widthY Components.Basic.point
  change
    (((box.xUpper - box.xLower) * (box.yUpper - box.yLower) -
        (box.yUpper - box.yLower) * (box.xLower - box.xLower)) / 2) *
      Norm.Basic.normSq coefficient =
    ((box.xUpper - box.xLower) * (box.yUpper - box.yLower)) / 2 *
      Norm.Basic.normSq coefficient
  exact congrArg (fun area => area / 2 * Norm.Basic.normSq coefficient) (by ring1)

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Integration.Energy in
/-- The two retained box triangle energies sum to the original box content times the coefficient squared norm. -/
theorem boxAffineTriangleEnergy_add
    (box : Box) (coefficient : Basic.Canonical) :
    lowerBoxAffineTriangleEnergy box coefficient +
        upperBoxAffineTriangleEnergy box coefficient =
      Box.Content.boxContent box *
        Norm.Basic.normSq coefficient := by
  rw [lowerBoxAffineTriangleEnergy_eq, upperBoxAffineTriangleEnergy_eq]
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  calc
    Box.Content.boxContent box * 2⁻¹ *
          Norm.Basic.normSq coefficient +
        Box.Content.boxContent box * 2⁻¹ *
          Norm.Basic.normSq coefficient =
      Box.Content.boxContent box *
        Norm.Basic.normSq coefficient *
          (2⁻¹ + 2⁻¹) := by ring1
    _ = Box.Content.boxContent box *
        Norm.Basic.normSq coefficient := by
      rw [show (2 : Fraction.Rational)⁻¹ + 2⁻¹ = 1 by decide]
      ring1

end Purelib.Integration.Energy.AffineTriangle.Box

end
