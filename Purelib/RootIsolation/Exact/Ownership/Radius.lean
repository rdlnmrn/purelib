module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.RootIsolation.Exact.Basic
public import Purelib.RootIsolation.Exact.Partition.Margin
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Assignment radii for exact root partitions

The retained partition margin and finite polynomial evaluation majorant
determine a positive rational radius. Its original unit cap controls the
radius square, and that same radius bounds the variation on the retained original box by the assigned clearance.
-/

namespace Purelib.RootIsolation.Exact.Ownership.Radius

/-- Compute a positive ownership radius from the retained partition margin and evaluation majorant.

The radius is the minimum of one and the partition margin divided by eight times the majorant. -/
@[expose] public def assignmentRadius
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    {count : Nat} (output : Basic.Output p ambient count) : Fraction.Rational :=
  min 1 (Partition.Margin.partitionMargin output /
    (8 * Bounds.Box.denseLipschitzBound p ambient))

/-- The retained partition margin and positive majorant give a strictly positive ownership radius.

Both entries of the original minimum are positive. The partition's stored
clearance margin and the same finite majorant certify its displayed quotient. -/
public theorem assignmentRadius_pos
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    {count : Nat} (output : Basic.Output p ambient count) :
    0 < assignmentRadius p ambient output := by
  exact Basic.lt_min (by decide)
    (Field.div_pos_direct
      (Partition.Margin.partitionMargin_pos output)
      (Arithmetic.mul_pos_direct (by decide)
        (Bounds.Box.denseLipschitzBound_pos p ambient)))

/-- The ownership radius is at most one, so its square is at most the radius itself.

The original minimum retains its unit cap and positive radius. Multiplying
that cap by the same nonnegative radius bounds the displayed square. -/
public theorem assignmentRadius_sq_le
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    {count : Nat} (output : Basic.Output p ambient count) :
    assignmentRadius p ambient output ^ 2 ≤
      assignmentRadius p ambient output := by
  let radius := assignmentRadius p ambient output
  have radiusPositive := assignmentRadius_pos p ambient output
  have radiusLeOne : radius ≤ 1 := Basic.min_le_left _ _
  rw [pow_two]
  calc
    radius * radius ≤ 1 * radius :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        radiusLeOne radiusPositive.le
    _ = radius := by ring1

/-- A box meeting the retained ownership radius has variation strictly dominated by its assigned clearance.

The original partition margin bounds the clearance below, and the retained majorant controls the diagonal contribution.
-/
public theorem assignment_dominates
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    {count : Nat} (output : Basic.Output p ambient count)
    (box : Box)
    (diagonal : box.diagonalSq ≤
      assignmentRadius p ambient output ^ 2)
    {clearance : Fraction.Rational}
    (marginLe : Partition.Margin.partitionMargin output ≤ clearance) :
    2 * (Bounds.Box.Residual.anchorResidualBound p ambient box +
      Bounds.Box.denseLipschitzBound p ambient * box.diagonalSq) < clearance := by
  let radius := assignmentRadius p ambient output
  let lipschitz := Bounds.Box.denseLipschitzBound p ambient
  let margin := Partition.Margin.partitionMargin output
  have radiusPositive := assignmentRadius_pos p ambient output
  have lipschitzPositive := Bounds.Box.denseLipschitzBound_pos p ambient
  have radiusSquareLe := assignmentRadius_sq_le p ambient output
  have radiusRatio : radius ≤ margin / (8 * lipschitz) :=
    Basic.min_le_right _ _
  have eightLipschitzPositive : 0 < 8 * lipschitz :=
    Arithmetic.mul_pos_direct (by decide) lipschitzPositive
  have scaled : radius * (8 * lipschitz) ≤ margin :=
    (Field.le_div_iff_pos
      eightLipschitzPositive).mp radiusRatio
  have fourLipschitzNonnegative : 0 ≤ 4 * lipschitz :=
    (Arithmetic.mul_pos_direct (by decide)
      lipschitzPositive).le
  have productPositive : 0 < lipschitz * radius :=
    Arithmetic.mul_pos_direct lipschitzPositive radiusPositive
  calc
    2 * (Bounds.Box.Residual.anchorResidualBound p ambient box +
        lipschitz * box.diagonalSq) =
        4 * lipschitz * box.diagonalSq := by
      dsimp only [Bounds.Box.Residual.anchorResidualBound, lipschitz]
      ring1
    _ ≤ 4 * lipschitz * radius ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal
        fourLipschitzNonnegative
    _ ≤ 4 * lipschitz * radius :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquareLe
        fourLipschitzNonnegative
    _ = 4 * (lipschitz * radius) := by ring1
    _ < 8 * (lipschitz * radius) :=
      Arithmetic.mul_lt_mul_of_pos_right_direct
        (show (4 : Fraction.Rational) < 8 by decide) productPositive
    _ = radius * (8 * lipschitz) := by ring1
    _ ≤ margin := scaled
    _ ≤ clearance := marginLe
end Purelib.RootIsolation.Exact.Ownership.Radius
