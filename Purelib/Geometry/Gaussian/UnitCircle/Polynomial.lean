module

public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Coordinates
public import Purelib.Geometry.Gaussian.UnitCircle.Quarter
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Pair
public import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Dense.Multiplication.Basic
public import Purelib.Data.Gaussian.Scale
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine
import Purelib.Tactic.Ring

/-! # Polynomial quarter arcs on the original stereographic rays

Multiplying the original stereographic numerator by `1-t/2` gives a cubic
whose endpoints are the original unit cardinal points. Its radial factor
relative to the original rational unit point lies between one half and one.
The four original quarter multipliers give literally joined polynomial
edges with positive clearance, including their repeated closing endpoint.
-/

public section

namespace Purelib.Geometry.Gaussian.UnitCircle.Polynomial

open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)
open Purelib.Polynomial.Clearance.Pair.Basic (Certificate)
open Purelib.Geometry.Rational
open Quarter (UnitCircuitQuarter)

/-- The positive radial factor relating the polynomial arc to its original unit-circle point. -/
@[expose] def gain (time : Fraction.Rational) : Fraction.Rational :=
  (1 - time / 2) * (1 + time ^ 2)

/-- Clearing the original nonzero denominator two gives the exact affine complement. -/
private theorem twice_complement (value : Fraction.Rational) : (1 - value / 2) * 2 = 2 - value := by
  calc
    _ = 2 - (value / 2) * 2 := by ring1
    _ = 2 - value := congrArg (fun result : Fraction.Rational => 2 - result)
      (Fraction.Field.div_mul_cancel_of_ne value 2 (by decide +kernel))

/-- The same factor is one minus an explicitly nonnegative endpoint-vanishing term. -/
theorem gain_eq (time : Fraction.Rational) : gain time = 1 - time * (1 - time) ^ 2 / 2 := by
  apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right
    (by decide +kernel : (2 : Fraction.Rational) ≠ 0)
  calc
    gain time * 2 = ((1 - time / 2) * 2) * (1 + time ^ 2) := by unfold gain; ring1
    _ = (2 - time) * (1 + time ^ 2) :=
      congrArg (fun result : Fraction.Rational => result * (1 + time ^ 2)) (twice_complement time)
    _ = 2 - time * (1 - time) ^ 2 := by ring1
    _ = (1 - time * (1 - time) ^ 2 / 2) * 2 := (twice_complement (time * (1 - time) ^ 2)).symm

/-- The polynomial radial factor stays between one half and one throughout the original quarter interval. -/
theorem gain_bounds {time : Fraction.Rational} (inside : 0 ≤ time ∧ time ≤ 1) :
    (1 / 2 : Fraction.Rational) ≤ gain time ∧ gain time ≤ 1 := by
  have half : time / 2 ≤ (1 / 2 : Fraction.Rational) :=
    (Fraction.Order.Field.div_le_iff_pos (by decide +kernel)).mpr
      (inside.2.trans_eq (by decide +kernel))
  have lowerFactor : (1 / 2 : Fraction.Rational) ≤ 1 - time / 2 := by
    have actual := Order.Arithmetic.sub_le_sub_left_direct half 1
    exact Eq.mp (congrArg (fun value : Fraction.Rational => value ≤ 1 - time / 2)
      (by decide +kernel : (1 : Fraction.Rational) - 1 / 2 = 1 / 2)) actual
  have denominator : (1 : Fraction.Rational) ≤ 1 + time ^ 2 := by
    have actual := Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Basic.le_refl (1 : Fraction.Rational))
      (Order.Arithmetic.sq_nonneg_direct time)
    exact Eq.mp (congrArg (fun value : Fraction.Rational => value ≤ 1 + time ^ 2)
      (by decide +kernel : (1 : Fraction.Rational) + 0 = 1)) actual
  constructor
  · have actual := Order.Arithmetic.mul_le_mul_direct lowerFactor denominator
      (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
      ((by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 2).trans lowerFactor)
    exact Eq.mp (congrArg (fun value : Fraction.Rational => value ≤ gain time)
      (by decide +kernel : (1 / 2 : Fraction.Rational) * 1 = 1 / 2)) actual
  · have removed : 0 ≤ time * (1 - time) ^ 2 / 2 :=
      Fraction.Order.Field.div_nonneg_direct
        (Order.Arithmetic.mul_nonneg_direct inside.1
          (Order.Arithmetic.sq_nonneg_direct (1 - time)))
        (by decide +kernel)
    have actual := Order.Arithmetic.sub_le_sub_left_direct removed 1
    rewrite [gain_eq]
    exact actual.trans_eq (by ring1)

/-- The radial factor is exactly one at both original quarter endpoints. -/
theorem gain_endpoints : gain 0 = 1 ∧ gain 1 = 1 := by decide +kernel

/-- The cubic coefficient table for the first original quarter, in descending order. -/
@[expose] def firstPolynomial : CoefficientPolynomial :=
  ⟨[⟨1 / 2, 0⟩, ⟨-1, -1⟩, ⟨-1 / 2, 2⟩, ⟨1, 0⟩]⟩

/-- The first cubic evaluates to the original cleared numerator multiplied by `1-t/2`. -/
theorem firstPolynomial_eval (time : Fraction.Rational) :
    firstPolynomial.eval (Affine.line 0 1 time) =
      ⟨(1 - time / 2) * (1 - time ^ 2), (1 - time / 2) * (2 * time)⟩ := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [firstPolynomial, DensePolynomial.eval, DensePolynomial.evalCoeffs,
      List.foldl_cons, List.foldl_nil, Affine.line, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.zero_re,
      Data.Gaussian.Basic.zero_im, Data.Gaussian.Basic.one_re, Data.Gaussian.Basic.one_im,
      Purelib.Data.Gaussian.Cast.ofCoordinate_re, Purelib.Data.Gaussian.Cast.ofCoordinate_im]
  · apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right
      (by decide +kernel : (2 : Fraction.Rational) ≠ 0)
    calc
      _ = ((1 / 2 : Fraction.Rational) * 2) * time ^ 3 - 2 * time ^ 2 +
          ((-1 / 2 : Fraction.Rational) * 2) * time + 2 := by ring1
      _ = (2 - time) * (1 - time ^ 2) := by
        rewrite [show (1 / 2 : Fraction.Rational) * 2 = 1 by decide +kernel,
          show (-1 / 2 : Fraction.Rational) * 2 = -1 by decide +kernel]
        ring1
      _ = ((1 - time / 2) * 2) * (1 - time ^ 2) :=
        congrArg (fun result : Fraction.Rational => result * (1 - time ^ 2)) (twice_complement time).symm
      _ = ((1 - time / 2) * (1 - time ^ 2)) * 2 := by ring1
  · apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right
      (by decide +kernel : (2 : Fraction.Rational) ≠ 0)
    calc
      _ = (2 - time) * (2 * time) := by ring1
      _ = ((1 - time / 2) * 2) * (2 * time) :=
        congrArg (fun result : Fraction.Rational => result * (2 * time)) (twice_complement time).symm
      _ = ((1 - time / 2) * (2 * time)) * 2 := by ring1

/-- The first actual cubic point lies on the same ray as the original retained stereographic point. -/
theorem firstPolynomial_incidence (time : Fraction.Rational) :
    firstPolynomial.eval (Affine.line 0 1 time) = Scale.scale (gain time) (Stereographic.unitQuarterPoint time) := by
  rewrite [firstPolynomial_eval]
  apply Data.Gaussian.Basic.ext
  · change (1 - time / 2) * (1 - time ^ 2) = gain time * (Stereographic.unitQuarterPoint time).re
    calc
      _ = (1 - time / 2) * ((Stereographic.unitQuarterPoint time).re * (time ^ 2 + 1)) :=
        congrArg (fun value : Fraction.Rational => (1 - time / 2) * value)
          (Stereographic.unitQuarterPoint_re_mul_scalar time).symm
      _ = _ := by unfold gain; ring1
  · change (1 - time / 2) * (2 * time) = gain time * (Stereographic.unitQuarterPoint time).im
    calc
      _ = (1 - time / 2) * ((Stereographic.unitQuarterPoint time).im * (time ^ 2 + 1)) :=
        congrArg (fun value : Fraction.Rational => (1 - time / 2) * value)
          (Stereographic.unitQuarterPoint_im_mul_scalar time).symm
      _ = _ := by unfold gain; ring1

/-- Rotate the same cubic coefficient table by the original selected quarter multiplier. -/
@[expose] def polynomial (quarter : UnitCircuitQuarter) : CoefficientPolynomial :=
  Constants.gaussianConstant (Quarter.unitCircuitMultiplier quarter) * firstPolynomial

/-- Evaluate the original selected polynomial quarter at its retained rational parameter. -/
@[expose] def point (quarter : UnitCircuitQuarter) (time : Fraction.Rational) : Canonical :=
  (polynomial quarter).eval (Affine.line 0 1 time)

/-- The selected polynomial point is the same positive radial scaling of its original rotated unit point. -/
theorem point_incidence (quarter : UnitCircuitQuarter) (time : Fraction.Rational) :
    point quarter time = Scale.scale (gain time)
      (Quarter.unitCircuitMultiplier quarter * Stereographic.unitQuarterPoint time) := by
  unfold point polynomial
  rewrite [DensePolynomial.eval_mul, Constants.gaussianConstant_eval, firstPolynomial_incidence]
  exact (Scale.scale_mul_right _ _ _).symm

/-- The selected polynomial point has squared radius equal to the square of the SAME radial factor. -/
theorem point_normSq (quarter : UnitCircuitQuarter) (time : Fraction.Rational) :
    Norm.Basic.normSq (point quarter time) = gain time ^ 2 := by
  rewrite [point_incidence, Scale.normSq_scale, Norm.Basic.normSq_mul,
    Quarter.unitCircuitMultiplier_unit, Stereographic.unitQuarterPoint_unit]
  ring1

/-- Every polynomial quarter retains both cardinal endpoints of its original rational quarter. -/
theorem point_endpoints (quarter : UnitCircuitQuarter) :
    point quarter 0 = Quarter.unitCircuitMultiplier quarter ∧
      point quarter 1 = Quarter.unitCircuitMultiplier quarter * (⟨0, 1⟩ : Canonical) := by
  constructor
  · rewrite [point_incidence, gain_endpoints.1, Stereographic.unitQuarterPoint_zero]
    apply Data.Gaussian.Basic.ext <;> simp only [Scale.scale_re, Scale.scale_im,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
      Data.Gaussian.Basic.one_re, Data.Gaussian.Basic.one_im] <;> ring1
  · rewrite [point_incidence, gain_endpoints.2, Stereographic.unitQuarterPoint_one]
    apply Data.Gaussian.Basic.ext <;> simp only [Scale.scale_re, Scale.scale_im] <;> ring1

/-- The four actual polynomial quarters join in order and close at the identical original initial point. -/
theorem points_join :
    point .first 1 = point .second 0 ∧ point .second 1 = point .third 0 ∧
      point .third 1 = point .fourth 0 ∧ point .fourth 1 = point .first 0 := by
  constructor
  · exact (point_endpoints .first).2.trans
      ((by decide +kernel : Quarter.unitCircuitMultiplier .first * (⟨0, 1⟩ : Canonical) =
        Quarter.unitCircuitMultiplier .second).trans (point_endpoints .second).1.symm)
  constructor
  · exact (point_endpoints .second).2.trans
      ((by decide +kernel : Quarter.unitCircuitMultiplier .second * (⟨0, 1⟩ : Canonical) =
        Quarter.unitCircuitMultiplier .third).trans (point_endpoints .third).1.symm)
  constructor
  · exact (point_endpoints .third).2.trans
      ((by decide +kernel : Quarter.unitCircuitMultiplier .third * (⟨0, 1⟩ : Canonical) =
        Quarter.unitCircuitMultiplier .fourth).trans (point_endpoints .fourth).1.symm)
  · exact (point_endpoints .fourth).2.trans
      ((by decide +kernel : Quarter.unitCircuitMultiplier .fourth * (⟨0, 1⟩ : Canonical) =
        Quarter.unitCircuitMultiplier .first).trans (point_endpoints .first).1.symm)

/-- One actual polynomial quarter as the original oriented rational-coordinate edge. -/
@[expose] def edge (quarter : UnitCircuitQuarter) : PolynomialEdge :=
  PolynomialEdge.ofLine (polynomial quarter) 0 1 0 1

/-- The actual four original polynomial edges retain their positive orientation and closing occurrence. -/
@[expose] def edges : List PolynomialEdge := [edge .first, edge .second, edge .third, edge .fourth]

/-- The retained edge reads the same real coordinate as its original polynomial point. -/
theorem edge_real (quarter : UnitCircuitQuarter) (time : Fraction.Rational) :
    (edge quarter).realPart.eval time = (point quarter time).re :=
  PolynomialEdge.ofLine_real_eval _ _ _ _ _ _

/-- The retained edge reads the same imaginary coordinate as its original polynomial point. -/
theorem edge_imag (quarter : UnitCircuitQuarter) (time : Fraction.Rational) :
    (edge quarter).imagPart.eval time = (point quarter time).im :=
  PolynomialEdge.ofLine_imag_eval _ _ _ _ _ _

/-- Each actual polynomial point retains the uniform positive squared-radius lower bound one quarter. -/
theorem point_lower (quarter : UnitCircuitQuarter) {time : Fraction.Rational}
    (inside : 0 ≤ time ∧ time ≤ 1) : (1 / 4 : Fraction.Rational) ≤ Norm.Basic.normSq (point quarter time) := by
  have lower := Order.Arithmetic.pow_le_pow_direct (by decide +kernel)
    (gain_bounds inside).1 2
  exact (by decide +kernel : (1 / 4 : Fraction.Rational) = (1 / 2) ^ 2).trans_le
    (lower.trans_eq (point_normSq quarter time).symm)

/-- Each actual polynomial point stays within the original unit radius. -/
theorem point_upper (quarter : UnitCircuitQuarter) {time : Fraction.Rational}
    (inside : 0 ≤ time ∧ time ≤ 1) : Norm.Basic.normSq (point quarter time) ≤ 1 := by
  have nonnegative : 0 ≤ gain time := (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 2).trans
    (gain_bounds inside).1
  exact (point_normSq quarter time).trans_le
    ((Order.Arithmetic.pow_le_pow_direct nonnegative (gain_bounds inside).2 2).trans_eq
      (by decide +kernel : (1 : Fraction.Rational) ^ 2 = 1))

/-- A real polynomial point of any original quarter is nonzero throughout its retained interval. -/
theorem point_ne_zero (quarter : UnitCircuitQuarter) {time : Fraction.Rational}
    (inside : 0 ≤ time ∧ time ≤ 1) : point quarter time ≠ 0 := by
  intro zero
  have lower := point_lower quarter inside
  rewrite [zero, Norm.Basic.normSq_zero] at lower
  exact (by decide +kernel : ¬ (1 / 4 : Fraction.Rational) ≤ 0) lower

/-- Each actual original edge has a certified common-zero clearance of one quarter on the closed unit interval. -/
def clearance (quarter : UnitCircuitQuarter) :
    Certificate (edge quarter).realPart (edge quarter).imagPart ⟨0, 1, by decide +kernel⟩ :=
  { bound := 1 / 4
    positive := by decide +kernel
    lower := fun time inside => by
      rewrite [edge_real, edge_imag]
      exact point_lower quarter inside }

end Purelib.Geometry.Gaussian.UnitCircle.Polynomial

end
