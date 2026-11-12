module

public import Purelib.Polynomial.Clearance.Circle.LinearFactor
public import Purelib.Polynomial.Winding.Circle
import Purelib.Polynomial.Winding.Circle.Comparison
import Purelib.Tactic.Ring

/-!
# Independent circle winding of rational linear factors

A strict rational radial gap makes the original linear factor have positive
conjugate dot product with the coordinate, or with its nonzero constant term.
The actual chart-event readings therefore give one turn inside and zero turns
outside, independently of every root inventory.
-/

namespace Purelib.Polynomial.Winding.Circle

open Purelib.Data
open Purelib.RationalFunctions.Curve
open Canonical.Circle
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Basic (DensePolynomial)
open Dense.Gaussian.LinearFactor (linearFactor)
open Gaussian.Basic (Canonical)
open Rat.Fraction (Rational)
open Rat.Fraction.Order
open Purelib.Polynomial.Clearance.Circle (Certificate)

/-- A larger source quadrance gives positive dot product with the sum. -/
private theorem sum_dot_positive (source addition : Canonical)
    (gap : addition.normSq < source.normSq) :
    0 < source.re * (source + addition).re + source.im * (source + addition).im := by
  have positive := Arithmetic.add_pos_of_pos_of_nonneg_direct
    (Arithmetic.sub_pos_direct gap) (Gaussian.Norm.Basic.normSq_nonneg (source + addition))
  have identity : 2 * (source.re * (source + addition).re + source.im * (source + addition).im) =
      (source.normSq - addition.normSq) + Gaussian.Norm.Basic.normSq (source + addition) := by
    simp only [Gaussian.Norm.Basic.normSq, Canonical.normSq,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im]
    ring1
  apply Arithmetic.lt_of_mul_lt_mul_right_direct (c := (2 : Rational)) _ (by decide)
  calc
    (0 : Rational) * 2 = 0 := Rat.Fraction.Field.zero_mul_direct _
    _ < 2 * (source.re * (source + addition).re + source.im * (source + addition).im) :=
      identity.symm ▸ positive
    _ = (source.re * (source + addition).re + source.im * (source + addition).im) * 2 := by ring1

/-- Every actual retained substitution of the coordinate gives raw winding four. -/
public theorem raw_coordinate (paths : Boundary.Substitutions (linearFactor 0)) : raw paths = 4 := by
  unfold raw
  rw [paths.primary.real_readback, paths.primary.imaginary_readback,
    paths.reciprocal.real_readback, paths.reciprocal.imaginary_readback]
  decide +kernel

/-- Every constant has identical original cleared values on the two circle charts. -/
private theorem constant_cleared (value : Canonical) :
    clearedEval (DensePolynomial.constant value) (circle 1) =
      clearedEval (DensePolynomial.constant value) (reciprocalCircle 1) := by
  change (0 : CoefficientPolynomial) * (circle 1).numerator +
      DensePolynomial.scale value (DensePolynomial.constant 1 * (circle 1).denominator) =
    (0 : CoefficientPolynomial) * (reciprocalCircle 1).numerator +
      DensePolynomial.scale value (DensePolynomial.constant 1 * (reciprocalCircle 1).denominator)
  rfl

/-- Every actual retained substitution of a constant gives raw winding zero. -/
public theorem raw_constant (value : Canonical)
    (paths : Boundary.Substitutions (DensePolynomial.constant value)) : raw paths = 0 := by
  unfold raw
  rw [paths.primary.real_readback, paths.primary.imaginary_readback,
    paths.reciprocal.real_readback, paths.reciprocal.imaginary_readback]
  unfold clearedReal clearedImag
  rw [constant_cleared]
  ring1

/-- A rational linear factor with strictly interior root has independent raw winding four. -/
public theorem raw_linearInside (root : Canonical) (inside : root.normSq < 1)
    (paths : Boundary.Substitutions (linearFactor root)) : raw paths = 4 := by
  let coordinate := Boundary.Substitutions.prepare (linearFactor 0)
  have comparison := Comparison.raw_eq_of_positiveDot
    (Certificate.linearInside 0 (by decide)) (Certificate.linearInside root inside) coordinate paths
    (fun point unit => by
      rw [Dense.Gaussian.LinearFactor.linearFactor_eval, Dense.Gaussian.LinearFactor.linearFactor_eval,
        Gaussian.Basic.sub_zero, Gaussian.Basic.sub_eq_add_neg]
      apply sum_dot_positive
      rewrite [Canonical.normSq_neg, unit]
      exact inside)
  exact comparison.trans (raw_coordinate coordinate)

/-- A rational linear factor with strictly exterior root has independent raw winding zero. -/
public theorem raw_linearOutside (root : Canonical) (outside : 1 < root.normSq)
    (paths : Boundary.Substitutions (linearFactor root)) : raw paths = 0 := by
  have nonzero : -root ≠ 0 := by
    intro equal
    have normEqual := congrArg Canonical.normSq equal
    rewrite [Canonical.normSq_neg, Canonical.normSq_zero] at normEqual
    exact (not_lt_of_ge (by decide : (0 : Rational) ≤ 1)) (normEqual ▸ outside)
  let constant := Boundary.Substitutions.prepare (DensePolynomial.constant (-root))
  have comparison := Comparison.raw_eq_of_positiveDot
    (Certificate.constant (-root) nonzero) (Certificate.linearOutside root outside) constant paths
    (fun point unit => by
      rw [DensePolynomial.eval_constant, Dense.Gaussian.LinearFactor.linearFactor_eval,
        Gaussian.Basic.sub_eq_add_neg, Gaussian.Basic.add_comm point (-root)]
      apply sum_dot_positive
      rewrite [Canonical.normSq_neg, unit]
      exact outside)
  exact comparison.trans (raw_constant (-root) constant)

end Purelib.Polynomial.Winding.Circle
