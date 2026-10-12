module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Boundary.Budget
public import Purelib.Geometry.Rational.Box.Boundary.Strip
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Tactic.Ring

/-!
# Protected boundary radii

The radius retains its boundary-clearance owner and box Lipschitz value. The
side-width caps and residual estimate certify the same protected strip.
-/

namespace Purelib.Polynomial.Clearance.Box.ProtectedRadius

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense

/-- The radius threshold determined by the retained boundary clearance and box Lipschitz value.

The original clearance and box Lipschitz value determine the quotient
threshold. The reciprocal scale cap and one-sixteenth side widths are
retained in the displayed minimum with the same coefficient and box owners. -/
@[expose] public def protectedBoundaryRadius
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p ambient) : Fraction.Rational :=
  min (1 / Box.Boundary.Budget.protectedBoundaryScale)
    (min (clearance.bound / (2 * Gaussian.Bounds.Box.denseLipschitzBound p ambient))
      (min (ambient.widthX / 16) (ambient.widthY / 16)))

/-- A proper ambient box with positive boundary clearance has a positive computed protected-strip radius.

The retained proper-box widths and positive clearance make all four
constituent quotient thresholds positive. Their same rational minima
therefore give a strictly positive protected-strip radius. -/
public theorem protectedBoundaryRadius_pos
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p ambient)
    (proper : ambient.Proper) :
    0 < protectedBoundaryRadius p ambient clearance := by
  have widthXPositive : 0 < ambient.widthX := by
    exact Fraction.Order.Arithmetic.sub_pos_direct proper.1
  have widthYPositive : 0 < ambient.widthY := by
    exact Fraction.Order.Arithmetic.sub_pos_direct proper.2
  have lipschitzPositive := Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  have onePositive : (0 : Fraction.Rational) < 1 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide)
  have twoPositive : (0 : Fraction.Rational) < 2 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 2) (by decide)
  have sixteenPositive : (0 : Fraction.Rational) < 16 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 16) (by decide)
  exact Fraction.Order.Basic.lt_min
    (Fraction.Order.Field.div_pos_direct onePositive
      Box.Boundary.Budget.protectedBoundaryScale_pos)
    (Fraction.Order.Basic.lt_min
      (Fraction.Order.Field.div_pos_direct clearance.positive
        (Fraction.Order.Arithmetic.mul_pos_direct twoPositive
          lipschitzPositive))
      (Fraction.Order.Basic.lt_min
        (Fraction.Order.Field.div_pos_direct widthXPositive
          sixteenPositive)
        (Fraction.Order.Field.div_pos_direct widthYPositive
          sixteenPositive)))

/-- The computed protected radius is nonnegative for every closed ambient box.

Closed-box endpoint ordering gives nonnegative side widths even when
a side is degenerate. The positive scale, clearance and Lipschitz value
certify the same nested radius minimum as nonnegative. -/
public theorem protectedBoundaryRadius_nonneg
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p ambient) :
    0 ≤ protectedBoundaryRadius p ambient clearance := by
  have onePositive : (0 : Fraction.Rational) < 1 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide)
  have twoPositive : (0 : Fraction.Rational) < 2 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 2) (by decide)
  have sixteenPositive : (0 : Fraction.Rational) < 16 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 16) (by decide)
  have widthXQuotientNonnegative :
      0 ≤ ambient.widthX / (16 : Fraction.Rational) := by
    change 0 ≤ ambient.widthX * (16 : Fraction.Rational)⁻¹
    exact Fraction.Order.Arithmetic.mul_nonneg_direct ambient.widthX_nonneg
      (Fraction.Order.Field.inv_pos_direct sixteenPositive).le
  have widthYQuotientNonnegative :
      0 ≤ ambient.widthY / (16 : Fraction.Rational) := by
    change 0 ≤ ambient.widthY * (16 : Fraction.Rational)⁻¹
    exact Fraction.Order.Arithmetic.mul_nonneg_direct ambient.widthY_nonneg
      (Fraction.Order.Field.inv_pos_direct sixteenPositive).le
  exact le_min
    (Fraction.Order.Field.div_pos_direct onePositive
      Box.Boundary.Budget.protectedBoundaryScale_pos).le
    (le_min
      (Fraction.Order.Field.div_pos_direct clearance.positive
        (Fraction.Order.Arithmetic.mul_pos_direct twoPositive
          (Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient))).le
      (le_min widthXQuotientNonnegative widthYQuotientNonnegative))

/-- The computed protected radius is at most one sixteenth of each ambient side width.

The final two entries of the retained nested minimum are the original
side widths divided by sixteen. The minimum projections supply both
quantitative bounds without replacing a radius or box observation. -/
public theorem protectedBoundaryRadius_le_widths
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p ambient) :
    protectedBoundaryRadius p ambient clearance ≤ ambient.widthX / 16 ∧
      protectedBoundaryRadius p ambient clearance ≤ ambient.widthY / 16 := by
  have belowInner : protectedBoundaryRadius p ambient clearance ≤
      min (clearance.bound / (2 * Gaussian.Bounds.Box.denseLipschitzBound p ambient))
        (min (ambient.widthX / 16) (ambient.widthY / 16)) := by
    exact Fraction.Order.Basic.min_le_right
      (1 / Box.Boundary.Budget.protectedBoundaryScale)
      (min (clearance.bound / (2 * Gaussian.Bounds.Box.denseLipschitzBound p ambient))
        (min (ambient.widthX / 16) (ambient.widthY / 16)))
  have widths : protectedBoundaryRadius p ambient clearance ≤
      min (ambient.widthX / 16) (ambient.widthY / 16) := by
    exact belowInner.trans
      (Fraction.Order.Basic.min_le_right
        (clearance.bound / (2 * Gaussian.Bounds.Box.denseLipschitzBound p ambient))
        (min (ambient.widthX / 16) (ambient.widthY / 16)))
  exact ⟨widths.trans (Fraction.Order.Basic.min_le_left _ _),
    widths.trans (Fraction.Order.Basic.min_le_right _ _)⟩

/-- The protected radius leaves enough numerical room for the projected
boundary value to dominate both source oscillations.

The original radius cap and clearance quotient bound control the same
Lipschitz-scaled radius square. Together with the supplied small-box
diagonal bound they dominate the retained anchor residual and boundary
projection displacement strictly below the original clearance. -/
public theorem protectedBoundaryRadius_dominates
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient small : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p ambient)
    (proper : ambient.Proper)
    (diagonal : small.diagonalSq ≤
      protectedBoundaryRadius p ambient clearance ^ 2) :
    2 * (Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
      Gaussian.Bounds.Box.denseLipschitzBound p ambient *
        (Box.Boundary.Strip.protectedBoundaryDistanceScale *
          protectedBoundaryRadius p ambient clearance ^ 2)) <
      clearance.bound := by
  let rho := protectedBoundaryRadius p ambient clearance
  let lipschitz := Gaussian.Bounds.Box.denseLipschitzBound p ambient
  have rhoPositive := protectedBoundaryRadius_pos p clearance proper
  have lipschitzPositive := Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  have rhoCap : rho ≤ 1 / Box.Boundary.Budget.protectedBoundaryScale := Fraction.Order.Basic.min_le_left _ _
  have rhoRatio : rho ≤ clearance.bound / (2 * lipschitz) :=
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  have rhoScaled : rho * Box.Boundary.Budget.protectedBoundaryScale ≤ 1 :=
    (Fraction.Order.Field.le_div_iff_pos
      Box.Boundary.Budget.protectedBoundaryScale_pos).mp rhoCap
  have ratioScaled : rho * (2 * lipschitz) ≤ clearance.bound :=
    (Fraction.Order.Field.le_div_iff_pos
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        lipschitzPositive)).mp rhoRatio
  let base := lipschitz * rho ^ 2
  have basePositive : 0 < base := Fraction.Order.Arithmetic.mul_pos_direct
    lipschitzPositive (Fraction.Order.Arithmetic.pow_pos_direct rhoPositive 2)
  have capScaled : Box.Boundary.Budget.protectedBoundaryScale * base ≤ lipschitz * rho := by
    have multiplierNonnegative : 0 ≤ lipschitz * rho :=
      (Fraction.Order.Arithmetic.mul_pos_direct
        lipschitzPositive rhoPositive).le
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      rhoScaled multiplierNonnegative
    calc
      Box.Boundary.Budget.protectedBoundaryScale * base =
          (rho * Box.Boundary.Budget.protectedBoundaryScale) * (lipschitz * rho) := by
        dsimp only [base]
        ring1
      _ ≤ 1 * (lipschitz * rho) := scaled
      _ = lipschitz * rho := by ring1
  let halfScale : Fraction.Rational := (4 : Fraction.Rational) * 8 * 8
  have oneLeEight : (1 : Fraction.Rational) ≤ 8 :=
    Fraction.Cast.Order.natCast_le_direct
      (m := 1) (n := 8) (by decide)
  have baseLeEight : base ≤ 8 * base := by
    calc
      base = 1 * base := by ring1
      _ ≤ 8 * base :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          oneLeEight basePositive.le
  have baseLeDistanceScale : base ≤
      Box.Boundary.Strip.protectedBoundaryDistanceScale * base := by
    have eightNonnegative : (0 : Fraction.Rational) ≤ 8 :=
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 8) (by decide)).le
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      baseLeEight eightNonnegative
    calc
      base ≤ 8 * base := baseLeEight
      _ ≤ 8 * (8 * base) := scaled
      _ = Box.Boundary.Strip.protectedBoundaryDistanceScale * base := by
        unfold Box.Boundary.Strip.protectedBoundaryDistanceScale
        ring1
  have strictCoefficient : halfScale * base <
      Box.Boundary.Budget.protectedBoundaryScale * base := by
    have halfScalePositive : 0 < halfScale := by
      dsimp only [halfScale]
      have fourPositive : (0 : Fraction.Rational) < 4 :=
        Fraction.Cast.Order.natCast_pos_direct (n := 4) (by decide)
      have eightPositive : (0 : Fraction.Rational) < 8 :=
        Fraction.Cast.Order.natCast_pos_direct (n := 8) (by decide)
      exact Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Order.Arithmetic.mul_pos_direct fourPositive eightPositive)
        eightPositive
    have halfBasePositive := Fraction.Order.Arithmetic.mul_pos_direct
      halfScalePositive basePositive
    calc
      halfScale * base = 0 + halfScale * base := by ring1
      _ < halfScale * base + halfScale * base :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct
          halfBasePositive (halfScale * base)
      _ = Box.Boundary.Budget.protectedBoundaryScale * base := by
        dsimp only [halfScale, Box.Boundary.Budget.protectedBoundaryScale]
        ring1
  have lipschitzRhoPositive :=
    Fraction.Order.Arithmetic.mul_pos_direct lipschitzPositive rhoPositive
  have strictDoubling : lipschitz * rho < 2 * lipschitz * rho := by
    calc
      lipschitz * rho = 0 + lipschitz * rho := by ring1
      _ < lipschitz * rho + lipschitz * rho :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct
          lipschitzRhoPositive (lipschitz * rho)
      _ = 2 * lipschitz * rho := by ring1
  have residualBound : Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small ≤ base := by
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      diagonal lipschitzPositive.le
  calc
    2 * (Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
        lipschitz * (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2)) ≤
        halfScale * base := by
      have residualDistance : Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small ≤
          Box.Boundary.Strip.protectedBoundaryDistanceScale * base :=
        residualBound.trans baseLeDistanceScale
      have twoNonnegative : (0 : Fraction.Rational) ≤ 2 :=
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 2) (by decide)).le
      have variationAsBase :
          lipschitz * (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2) =
            Box.Boundary.Strip.protectedBoundaryDistanceScale * base := by
        dsimp only [base]
        ring1
      calc
        2 * (Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
            lipschitz * (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2)) =
            2 * (Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
              Box.Boundary.Strip.protectedBoundaryDistanceScale * base) := by
          rw [variationAsBase]
        _ ≤ 2 * (Box.Boundary.Strip.protectedBoundaryDistanceScale * base +
            Box.Boundary.Strip.protectedBoundaryDistanceScale * base) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add residualDistance (le_refl _)) twoNonnegative
        _ = halfScale * base := by
          dsimp only [halfScale, Box.Boundary.Strip.protectedBoundaryDistanceScale]
          ring1
    _ < Box.Boundary.Budget.protectedBoundaryScale * base := strictCoefficient
    _ ≤ lipschitz * rho := capScaled
    _ < 2 * lipschitz * rho := strictDoubling
    _ ≤ clearance.bound := by
      have rearranged : 2 * lipschitz * rho =
          rho * (2 * lipschitz) := by ring1
      rw [rearranged]
      exact ratioScaled

end Purelib.Polynomial.Clearance.Box.ProtectedRadius
