module
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Fin
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Topology.Polygon.Stokes.Commutator.Triangulation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Rational

open Purelib.Data.Rat

open Purelib.Integration.Energy

open Purelib.LinearAlgebra.Gaussian

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.PreparedSurfaceCoercivity

open Purelib.Topology.Polygon.Stokes.Commutator

section
@[expose] public section

/-!
# Small exact regression checks for global surface-error accounting

These are arithmetic tests of the generic comparison layer, not examples of
the Riemann-period theorem.  In particular, the displayed period vectors are
test data, not certified periods of any curve.
-/

namespace Test.Integration.Surface.Coercivity

/-- The exact Gaussian-rational scalar carrier. -/
private abbrev Gaussian := Data.Gaussian.Basic.Canonical

/-- The four unit-square vertices in counterclockwise order. -/
private def squareVertex (vertex : Fin 4) :
  Gaussian :=
  if vertex = 0 then 0
  else if vertex = 1 then 1
  else if vertex = 2 then ⟨1, 1⟩
  else ⟨0, 1⟩

/-- The exact zero local error certificate on each of the original square's two affine faces. -/
private def squareFaceError (face : Fin 2) :
    AffineTriangle.AffineTriangleErrorCertificate 1
      (squareVertex (Triangulation.genusOneCommutatorFaces face).first)
      (squareVertex (Triangulation.genusOneCommutatorFaces face).second)
      (squareVertex (Triangulation.genusOneCommutatorFaces face).third)
      (squareVertex (Triangulation.genusOneCommutatorFaces face).first)
      (squareVertex (Triangulation.genusOneCommutatorFaces face).second)
      (squareVertex (Triangulation.genusOneCommutatorFaces face).third) where
  firstBudget := 0
  secondBudget := 0
  mixedBudget := 0
  firstBudget_nonnegative := Fraction.Order.Basic.le_refl 0
  secondBudget_nonnegative := Fraction.Order.Basic.le_refl 0
  mixedBudget_nonnegative := Fraction.Order.Basic.le_refl 0
  firstProductBound := by
    refine Data.Fin.cases_induction ?_ (fun index => ?_) face
    · decide
    · refine Data.Fin.cases_induction ?_ (fun empty => ?_) index
      · decide
      · exact Fin.elim0 empty
  secondProductBound := by
    refine Data.Fin.cases_induction ?_ (fun index => ?_) face
    · decide
    · refine Data.Fin.cases_induction ?_ (fun empty => ?_) index
      · decide
      · exact Fin.elim0 empty
  mixedProductBound := by
    refine Data.Fin.cases_induction ?_ (fun index => ?_) face
    · decide
    · refine Data.Fin.cases_induction ?_ (fun empty => ?_) index
      · decide
      · exact Fin.elim0 empty

/-- A two-face sample with exact cached sums. -/
private def squareSample : PreparedSurfaceCoercivity.AffineSurfaceSample 4 2
  where
  triangulation := Triangulation.genusOneCommutatorTriangulation
  coordinate := squareVertex
  primitiveValue := squareVertex
  faceCoefficient := fun _ => 1
  faceError := squareFaceError
  affineEnergy := 1
  affineEnergy_eq := by decide
  errorBudget := 0
  errorBudget_eq := by
    change (0 : Fraction.Rational) = 0 + (0 + 0)
    decide
  boundaryArea := ⟨0, 4⟩
  boundaryArea_eq := by decide

/-- The retained local squared radius one thirty-second is strictly positive. -/
private theorem squareRadius_positive : (0 : Fraction.Rational) < 1 / 32 :=
  Fraction.Order.Field.div_pos_direct
    (numerator := 1) (denominator := 32) (by decide)
    (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide))

/-- The same geometry can compute all local error witnesses automatically. -/
private def computedSquareSample :
  PreparedSurfaceCoercivity.AffineSurfaceSample 4 2 :=
  AffineSurfaceSample.ofVertices Triangulation.genusOneCommutatorTriangulation
    squareVertex (fun vertex => 1 * squareVertex
      vertex) (fun _ => 1) (1 / 32)
    squareRadius_positive

/-- The automatically certified square sample retains exact affine energy one. -/
example : computedSquareSample.affineEnergy = 1 := by decide
/-- The automatically generated two-face square certificate has total error budget three sixteenths. -/
example : computedSquareSample.errorBudget = (3 / 16 : Fraction.Rational) := by
  rw [show computedSquareSample.errorBudget =
      FiniteSum.Fin.sumFin (fun _ : Fin 2 => 3 * (1 / 32 : Fraction.Rational)) from
    PreparedSurfaceCoercivity.AffineSurfaceSample.ofVertices_exact_errorBudget
      Triangulation.genusOneCommutatorTriangulation
      squareVertex 1 (1 / 32)
        squareRadius_positive,
    FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ]
  change 3 * (1 / 32 : Fraction.Rational) + (3 * (1 / 32 : Fraction.Rational) + 0) = 3 / 16
  calc
    _ = (6 / 32 : Fraction.Rational) := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = 3 / 16 := Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)).ne'
      (Fraction.Cast.Order.natCast_pos_direct (n := 16) (by decide)).ne'
      (by ring1)
/-- The automatically certified square sample retains its exact original boundary area. -/
example : computedSquareSample.boundaryArea = (⟨0, 4⟩ :
  Gaussian) := by decide

/-- The exact finite Stokes sample recovers the unit-square energy. -/
example : squareSample.affineEnergy -
  squareSample.errorBudget <=
    squareSample.boundaryArea.im / 4 :=
  squareSample.affineEnergy_sub_errorBudget_le_boundaryEnergy

/-- The single-entry Gaussian test vector with value one. -/
private def aPeriods : LinearAlgebra.Gaussian.Energy.GaussianVector 1 :=
  Data.Vector.Basic.vectorOfFn fun _ => 1
/-- The single-entry Gaussian test vector with value imaginary three quarters. -/
private def bPeriods : LinearAlgebra.Gaussian.Energy.GaussianVector 1 :=
  Data.Vector.Basic.vectorOfFn fun _ => ⟨0, 3 / 4⟩

/-- Deliberately unequal boundaries test the approximate matching route. -/
example : squareSample.boundaryArea ≠ Polygon.energyBoundaryArea
  aPeriods bPeriods := by decide

/-- Paying the nonzero boundary loss recovers the exact lower margin. -/
example : (3 / 4 : Fraction.Rational) <=
    Energy.periodPairingEnergy aPeriods bPeriods
      := by
  have bound := squareSample.affineEnergy_sub_budgets_le_periodPairing
    aPeriods bPeriods (1 / 4) (by decide) (by
      decide)
  change (1 : Fraction.Rational) - 0 - 1 / 4 <= _ at bound
  rw [show (1 : Fraction.Rational) - 0 - 1 / 4 = 3 / 4 by decide] at bound
  exact bound

/-- Refinement selection also works when the initial sample is already fine enough; it does not require a positive-depth
or successful-search premise. -/
example : (1 / 2 : Fraction.Rational) <
    Energy.periodPairingEnergy aPeriods bPeriods
      := by
  exact squareSample.half_lower_lt_periodPairing_of_refined
    aPeriods bPeriods (scale := 1 / 4) (lower :=
      1)
    (boundaryBudget := 1 / 4) (by decide) (by decide) (by decide)
    0 0 (by decide) (by decide) (by decide) (by decide)

/-- A large initial error allowance forces actual refinement, and the total selector produces a checked strict bound
rather than a conditional result. -/
example : 0 < PreparedSurfaceCoercivity.energyRefinementIndex 64 1 0 := by
  apply Nat.pos_of_ne_zero
  intro zeroIndex
  have scaleNonnegative : (0 : Fraction.Rational) <= 64 :=
    (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide)).le
  have accurate := PreparedSurfaceCoercivity.error_lt_half_at_energyRefinement
    (scale := 64) (lower := 1) scaleNonnegative (by decide)
    0 (PreparedSurfaceCoercivity.energyRefinementIndex 64 1 0) le_rfl
  rw [zeroIndex] at accurate
  have initialLower : (1 / 2 : Fraction.Rational) <=
      Geometric.Basic.quarterRadius 64 0 := by
    rw [Geometric.Basic.quarterRadius, pow_zero,
      Fraction.Field.div_eq_mul_inv_direct 64 1,
      show (1 : Fraction.Rational)⁻¹ = 1 by decide, mul_one]
    exact (show (1 / 2 : Fraction.Rational) <= 1 by decide).trans
      (Fraction.Cast.Order.natCast_le_direct (m := 1) (n := 64) (by decide))
  exact (not_lt_of_ge initialLower) accurate

/-- The selected finite refinement stage makes the original geometric error strictly less than half the retained lower
margin. -/
example : Geometric.Basic.quarterRadius 64 (PreparedSurfaceCoercivity.energyRefinementIndex 64 1 0) <
    (1 / 2 : Fraction.Rational) :=
  PreparedSurfaceCoercivity.error_lt_half_at_energyRefinement
    (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide)).le
    (by decide) 0 _ le_rfl

end Test.Integration.Surface.Coercivity

end
