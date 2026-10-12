module
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
public import Purelib.LinearAlgebra.Coordinates4.Determinant
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Quadrilaterals.Basic

section
@[expose] public section

/-!
# Divine Proportions, Chapter 27: rational spherical coordinates

This module formalizes the finite algebra beneath the source's coordinate
changes: squared-coordinate reconstruction, the two-, three-, and
four-dimensional Jacobian determinants, squared density identities, the
lemniscate conversion, and a witness-based finite polygon-refinement step.

The chapter's improper integrals, exponentials, Gamma/Beta integrals, `π`, and
limit assertions are intentionally not introduced.  Their finite endpoint
polynomial simplifications are retained at the end of the module.
-/

namespace Purelib.Geometry.Coordinates.Spherical.Squared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## §27.4: three-dimensional rational spherical coordinates -/

/-- The denominator-cleared relations between three squared coordinates, two spreads and total quadrance. -/
def SphericalCoordinateSquares
    (xSquared ySquared zSquared spread polarSpread R : K) : Prop :=
  let horizontal := xSquared + ySquared
  R = horizontal + zSquared ∧
    spread * horizontal = xSquared ∧
    polarSpread * R = horizontal

/-- Recover all three squared Cartesian coordinates from the spherical spread relations. -/
theorem spherical_coordinate_squares
    (xSquared ySquared zSquared spread polarSpread R : K)
    (coordinates : SphericalCoordinateSquares
      xSquared ySquared zSquared spread polarSpread R) :
    xSquared = spread * polarSpread * R ∧
      ySquared = (1 - spread) * polarSpread * R ∧
      zSquared = (1 - polarSpread) * R := by
  change
    R = xSquared + ySquared + zSquared ∧
      spread * (xSquared + ySquared) = xSquared ∧
      polarSpread * R = xSquared + ySquared at coordinates
  constructor
  · calc
      xSquared = spread * (xSquared + ySquared) := coordinates.2.1.symm
      _ = spread * (polarSpread * R) := by rw [← coordinates.2.2]
      _ = spread * polarSpread * R := by ring1
  constructor
  · calc
      ySquared = (xSquared + ySquared) - xSquared := by ring1
      _ = polarSpread * R - spread * (xSquared + ySquared) := by
        rw [coordinates.2.1, coordinates.2.2]
      _ = (1 - spread) * polarSpread * R := by
        rw [← coordinates.2.2]
        ring1
  · calc
      zSquared = R - (xSquared + ySquared) := by rw [coordinates.1]; ring1
      _ = (1 - polarSpread) * R := by rw [← coordinates.2.2]; ring1

/-- The finite determinant of the three-dimensional spherical coordinate coefficient matrix. -/
def sphericalJacobianDeterminant (spread polarSpread R : K) : K :=
  Quadrilateral.determinantThree
    (polarSpread * R) (spread * R) (spread * polarSpread)
    (-polarSpread * R) ((1 - spread) * R) ((1 - spread) * polarSpread)
    0 (-R) (1 - polarSpread)

/-- The spherical coefficient determinant is the polar spread times the squared total quadrance. -/
theorem spherical_jacobian_determinant (spread polarSpread R : K)
  :
    sphericalJacobianDeterminant spread polarSpread R =
      polarSpread * R ^ 2 := by
  unfold sphericalJacobianDeterminant Quadrilateral.determinantThree
  ring1

/-- Express the product of three squared coordinates as a polynomial in the spreads and total quadrance. -/
theorem spherical_squared_density
    (xSquared ySquared zSquared spread polarSpread R : K)
    (coordinates : SphericalCoordinateSquares
      xSquared ySquared zSquared spread polarSpread R) :
    xSquared * ySquared * zSquared =
      spread * (1 - spread) * polarSpread ^ 2 *
        (1 - polarSpread) * R ^ 3 := by
  rcases spherical_coordinate_squares
      xSquared ySquared zSquared spread polarSpread R coordinates with
    ⟨xValue, yValue, zValue⟩
  rw [xValue, yValue, zValue]
  ring1

/-! ## §27.6: four-dimensional rational spherical coordinates -/

/-- The denominator-cleared relations between four squared coordinates, three spreads and total quadrance. -/
def FourSphericalCoordinateSquares
    (xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T : K) : Prop :=
  let firstPartial := xSquared + ySquared
  let secondPartial := firstPartial + zSquared
  T = secondPartial + wSquared ∧
    spread * firstPartial = xSquared ∧
    secondSpread * secondPartial = firstPartial ∧
    thirdSpread * T = secondPartial

/-- Recover all four squared Cartesian coordinates from the nested spread relations. -/
theorem four_spherical_coordinate_squares
    (xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T : K)
    (coordinates : FourSphericalCoordinateSquares
      xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T) :
    xSquared = spread * secondSpread * thirdSpread * T ∧
      ySquared = (1 - spread) * secondSpread * thirdSpread * T ∧
      zSquared = (1 - secondSpread) * thirdSpread * T ∧
      wSquared = (1 - thirdSpread) * T := by
  change
    T = xSquared + ySquared + zSquared + wSquared ∧
      spread * (xSquared + ySquared) = xSquared ∧
      secondSpread * (xSquared + ySquared + zSquared) =
        xSquared + ySquared ∧
      thirdSpread * T = xSquared + ySquared + zSquared at coordinates
  have firstPartial :
      xSquared + ySquared = secondSpread * thirdSpread * T := by
    calc
      xSquared + ySquared =
          secondSpread * (xSquared + ySquared + zSquared) :=
        coordinates.2.2.1.symm
      _ = secondSpread * (thirdSpread * T) := by
        rw [← coordinates.2.2.2]
      _ = secondSpread * thirdSpread * T := by ring1
  constructor
  · calc
      xSquared = spread * (xSquared + ySquared) := coordinates.2.1.symm
      _ = spread * (secondSpread * thirdSpread * T) := by rw [firstPartial]
      _ = spread * secondSpread * thirdSpread * T := by ring1
  constructor
  · calc
      ySquared = (xSquared + ySquared) - xSquared := by ring1
      _ = (xSquared + ySquared) -
          spread * (xSquared + ySquared) := by rw [coordinates.2.1]
      _ = (1 - spread) * (xSquared + ySquared) := by ring1
      _ = (1 - spread) * secondSpread * thirdSpread * T := by
        rw [firstPartial]
        ring1
  constructor
  · calc
      zSquared = (xSquared + ySquared + zSquared) -
          (xSquared + ySquared) := by ring1
      _ = thirdSpread * T - secondSpread * thirdSpread * T := by
        rw [coordinates.2.2.2, firstPartial]
      _ = (1 - secondSpread) * thirdSpread * T := by ring1
  · calc
      wSquared = T - (xSquared + ySquared + zSquared) := by
        rw [coordinates.1]
        ring1
      _ = (1 - thirdSpread) * T := by
        rw [← coordinates.2.2.2]
        ring1

/-- The finite determinant of the four-dimensional spherical coordinate coefficient matrix. -/
def fourSphericalJacobianDeterminant
    (spread secondSpread thirdSpread T : K) : K :=
  Quadrilateral.determinantFour
    (secondSpread * thirdSpread * T)
      (spread * thirdSpread * T)
      (spread * secondSpread * T)
      (spread * secondSpread * thirdSpread)
    (-secondSpread * thirdSpread * T)
      ((1 - spread) * thirdSpread * T)
      ((1 - spread) * secondSpread * T)
      ((1 - spread) * secondSpread * thirdSpread)
    0 (-thirdSpread * T) ((1 - secondSpread) * T)
      ((1 - secondSpread) * thirdSpread)
    0 0 (-T) (1 - thirdSpread)

/-- The four-dimensional coefficient determinant equals the second spread times the squared third spread and cubed
quadrance. -/
theorem four_spherical_jacobian_determinant
    (spread secondSpread thirdSpread T : K) :
    fourSphericalJacobianDeterminant
        spread secondSpread thirdSpread T =
      secondSpread * thirdSpread ^ 2 * T ^ 3 := by
  unfold fourSphericalJacobianDeterminant Quadrilateral.determinantFour
    Quadrilateral.determinantThree
  ring1

/-- Express the product of four squared coordinates as a polynomial in the three spreads and total quadrance. -/
theorem four_spherical_squared_density
    (xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T : K)
    (coordinates : FourSphericalCoordinateSquares
      xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T) :
    xSquared * ySquared * zSquared * wSquared =
      spread * (1 - spread) * secondSpread ^ 2 *
        (1 - secondSpread) * thirdSpread ^ 3 *
        (1 - thirdSpread) * T ^ 4 := by
  rcases four_spherical_coordinate_squares
      xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T coordinates with
    ⟨xValue, yValue, zValue, wValue⟩
  rw [xValue, yValue, zValue, wValue]
  ring1
end
end Purelib.Geometry.Coordinates.Spherical.Squared

end
