module

public import Purelib.Polynomial.Clearance.Circle
public import Purelib.Polynomial.Winding.Circle
import Purelib.RationalFunctions.Winding.Circle
import Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Tactic.Ring

/-!
# Whole-circle winding under an explicit polynomial perturbation

The same retained quotient-direction coordinate products stay in the positive
real half-plane. Their original endpoint formulas cancel at both exact joins,
so the independently executable original polynomial readings agree.
-/

namespace Purelib.Polynomial.Winding.Circle.Comparison

open Purelib.Data
open Purelib.Data.Rat
open Purelib.RationalFunctions.Curve
open Purelib.RationalFunctions.Winding.Circle (Paths)
open Canonical.Circle
open Purelib.Data.Gaussian.Basic (Canonical)
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Dense.Rational.CauchyIndex
open Rat.Fraction (Rational)
open Rat.Fraction.Order

/-- A perturbation below one sixteenth of a positive source quadrance has positive conjugate dot product. -/
private theorem dot_positive (source target : Canonical) {margin : Rational}
    (marginPositive : 0 < margin) (sourceLower : margin ≤ Gaussian.Norm.Basic.normSq source)
    (close : Gaussian.Norm.Basic.normSq (target - source) ≤ margin / 16) :
    0 < source.re * target.re + source.im * target.im := by
  have fractionLess : margin / 16 < margin := by
    apply (Field.div_lt_iff_pos (by decide : (0 : Rational) < 16)).mpr
    have scaled := Arithmetic.mul_lt_mul_of_pos_right_direct (by decide : (1 : Rational) < 16) marginPositive
    calc
      margin = 1 * margin := (Rat.Fraction.Field.one_mul _).symm
      _ < 16 * margin := scaled
      _ = margin * 16 := Rat.Fraction.Field.mul_comm _ _
  have residualLess : Gaussian.Norm.Basic.normSq (target - source) < Gaussian.Norm.Basic.normSq source :=
    close.trans_lt (fractionLess.trans_le sourceLower)
  have positive := Arithmetic.add_pos_of_pos_of_nonneg_direct
    (Arithmetic.sub_pos_direct residualLess) (Gaussian.Norm.Basic.normSq_nonneg target)
  have identity : 2 * (source.re * target.re + source.im * target.im) =
      (Gaussian.Norm.Basic.normSq source - Gaussian.Norm.Basic.normSq (target - source)) +
        Gaussian.Norm.Basic.normSq target := by
    simp only [Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
    ring1
  apply Arithmetic.lt_of_mul_lt_mul_right_direct (c := (2 : Rational)) _ (by decide)
  calc
    (0 : Rational) * 2 = 0 := Rat.Fraction.Field.zero_mul_direct _
    _ < 2 * (source.re * target.re + source.im * target.im) := identity.symm ▸ positive
    _ = (source.re * target.re + source.im * target.im) * 2 := by ring1

/-- Positive real-denominator clearing preserves the same original positive conjugate dot product. -/
private theorem cleared_product_positive (source target : CoefficientPolynomial) (curve : RationalCurve)
    (parameter divisor : Rational) (divisorPositive : 0 < divisor)
    (denominator : curve.denominatorAt parameter = ⟨divisor, 0⟩)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0)
    (positive : 0 < (source.eval (curve.point parameter)).re * (target.eval (curve.point parameter)).re +
      (source.eval (curve.point parameter)).im * (target.eval (curve.point parameter)).im) :
    0 < ((clearedEval target curve).eval (Gaussian.Cast.Path.ofCoordinate parameter) *
      Gaussian.Basic.conj ((clearedEval source curve).eval (Gaussian.Cast.Path.ofCoordinate parameter))).re := by
  rw [eval_clearedEval target curve parameter denominatorNonzero,
    eval_clearedEval source curve parameter denominatorNonzero,
    eval_denominatorPower, eval_denominatorPower, denominator,
    Gaussian.Power.realAxis_pow, Gaussian.Power.realAxis_pow]
  have identity (left right : Canonical) (first second : Rational) :
      (((⟨first, 0⟩ : Canonical) * right) *
        Gaussian.Basic.conj ((⟨second, 0⟩ : Canonical) * left)).re =
      (first * second) * (left.re * right.re + left.im * right.im) := by
    simp only [Gaussian.Basic.conj, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im]
    ring1
  rw [identity]
  exact Arithmetic.mul_pos_direct
    (Arithmetic.mul_pos_direct (Arithmetic.pow_pos_direct divisorPositive _)
      (Arithmetic.pow_pos_direct divisorPositive _))
    positive

/-- A positive conjugate dot product preserves the two original independent raw winding readings.

Both retained chart substitutions remain the original inputs. The proof uses
their same original quotient-direction products, half-plane formulas and
exact join identities; no root inventory defines either winding.
-/
public theorem raw_eq_of_positiveDot {source target : CoefficientPolynomial}
    (sourceMargin : Certificate source) (targetMargin : Certificate target)
    (sourcePaths : Boundary.Substitutions source) (targetPaths : Boundary.Substitutions target)
    (positive : ∀ point : Canonical, point.normSq = 1 →
      0 < (source.eval point).re * (target.eval point).re +
        (source.eval point).im * (target.eval point).im) :
    Circle.raw targetPaths = Circle.raw sourcePaths := by
  let sourceClearance := sourceMargin.onBoundary sourcePaths
  let targetClearance := targetMargin.onBoundary targetPaths
  let paths := Paths.prepare targetPaths sourcePaths
  have primaryPositive : ∀ parameter : Rational, Boundary.parameters.Contains parameter →
      0 < paths.primaryReal.eval parameter := by
    intro parameter _
    have value := congrArg Canonical.re (paths.primary_value parameter)
    change paths.primaryReal.eval parameter = _ at value
    rw [value, targetPaths.primary.state_value, sourcePaths.primary.state_value]
    exact cleared_product_positive source target (circle 1) parameter (parameter ^ 2 + 1)
      (Arithmetic.add_pos_of_nonneg_of_pos_direct (Arithmetic.sq_nonneg_direct _) (by decide))
      (circle_denominatorAt 1 parameter) (circle_denominator_ne 1 parameter)
      (positive _ (normSq_circle_point 1 parameter))
  have reciprocalPositive : ∀ parameter : Rational, Boundary.parameters.Contains parameter →
      0 < paths.reciprocalReal.eval parameter := by
    intro parameter _
    have value := congrArg Canonical.re (paths.reciprocal_value parameter)
    change paths.reciprocalReal.eval parameter = _ at value
    rw [value, targetPaths.reciprocal.state_value, sourcePaths.reciprocal.state_value]
    exact cleared_product_positive source target (reciprocalCircle 1) parameter (parameter ^ 2 + 1)
      (Arithmetic.add_pos_of_nonneg_of_pos_direct (Arithmetic.sq_nonneg_direct _) (by decide))
      (reciprocalCircle_denominatorAt 1 parameter) (reciprocalCircle_denominator_ne 1 parameter)
      (positive _ (normSq_reciprocalCircle_point 1 parameter))
  have primary := HalfPlane.formula_of_positive_real
    (paths.primaryClearance targetClearance sourceClearance) (by decide) primaryPositive
  have reciprocal := HalfPlane.formula_of_positive_real
    (paths.reciprocalClearance targetClearance sourceClearance) (by decide) reciprocalPositive
  have endpoint (parameter : Rational) (isEndpoint : parameter = -1 ∨ parameter = 1) :
      (Rat.Sign.Jump.signJump 1 (paths.primaryReal.eval parameter * paths.primaryImaginary.eval parameter) : Int) =
        Rat.Sign.Jump.signJump 1 (paths.reciprocalReal.eval parameter * paths.reciprocalImaginary.eval parameter) := by
    rw [paths.endpoint_real_eq parameter isEndpoint, paths.endpoint_imaginary_eq parameter isEndpoint]
  have zero : Purelib.RationalFunctions.Winding.Circle.raw paths = 0 := by
    unfold Purelib.RationalFunctions.Winding.Circle.raw
    unfold HalfPlane.Formula at primary reciprocal
    dsimp only [Boundary.parameters] at primary reciprocal
    rw [primary, reciprocal, endpoint (-1) (Or.inl rfl), endpoint 1 (Or.inr rfl)]
    ring1
  have difference := Purelib.RationalFunctions.Winding.Circle.raw_eq_sub paths targetClearance sourceClearance
  calc
    Circle.raw targetPaths = (Circle.raw targetPaths - Circle.raw sourcePaths) + Circle.raw sourcePaths := by ring1
    _ = 0 + Circle.raw sourcePaths := by rw [← difference, zero]
    _ = Circle.raw sourcePaths := by ring1

/-- Exact evaluation agreement on the rational circle preserves the original independent raw winding.

The target margin retains the same source payment by direct scalar transport.
The comparison uses the original positive source quadrance and the two actual
retained chart substitutions.
-/
public theorem raw_eq_of_eval_eq {source target : CoefficientPolynomial} (clearance : Certificate source)
    (sourcePaths : Boundary.Substitutions source) (targetPaths : Boundary.Substitutions target)
    (same : ∀ point : Canonical, point.normSq = 1 → target.eval point = source.eval point) :
    Circle.raw targetPaths = Circle.raw sourcePaths := by
  apply raw_eq_of_positiveDot clearance (clearance.transport same) sourcePaths targetPaths
  intro point unit
  rw [same point unit]
  have positive := Gaussian.Norm.Basic.normSq_pos (clearance.eval_ne unit)
  rewrite [Gaussian.Norm.Basic.normSq_eq_canonical] at positive
  exact positive

/-- A whole-circle small perturbation preserves the original independent raw winding readings.

The same original source margin constructs the target margin and pays the
positive conjugate dot product. Both chart substitutions remain retained
inputs; neither winding is defined by a root inventory.
-/
public theorem raw_eq_of_close {source target : CoefficientPolynomial} (clearance : Certificate source)
    (sourcePaths : Boundary.Substitutions source) (targetPaths : Boundary.Substitutions target)
    (close : clearance.Close target) : Circle.raw targetPaths = Circle.raw sourcePaths :=
  raw_eq_of_positiveDot clearance (clearance.perturbation close) sourcePaths targetPaths
    (fun point unit => dot_positive _ _ clearance.positive
      (clearance.lower point unit)
      (close point unit))

end Purelib.Polynomial.Winding.Circle.Comparison
