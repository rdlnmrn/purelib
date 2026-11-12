module

public import Purelib.Polynomial.Clearance.Circle
public import Purelib.Polynomial.Dense.Gaussian.LinearFactor
public import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Tactic.Ring

/-!
# Whole-circle margins for rational linear factors

A strict squared radial gap pays an explicit positive original-polynomial
margin. The exact root and its original linear factor remain the inputs;
no bounded boundary search or root approximation is used.
-/

namespace Purelib.Polynomial.Clearance.Circle

open Purelib.Data
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Basic (DensePolynomial)
open Dense.Gaussian.LinearFactor (linearFactor)
open Gaussian.Basic (Canonical)
open Rat.Fraction (Rational)
open Rat.Fraction.Order

/-- A nonzero constant has its exact constant quadrance as whole-circle margin. -/
@[expose] public def Certificate.constant (value : Canonical) (nonzero : value ≠ 0) :
    Certificate (DensePolynomial.constant value) :=
  { bound := Gaussian.Norm.Basic.normSq value
    positive := Gaussian.Norm.Basic.normSq_pos nonzero
    lower := fun _ _ => by
      rewrite [DensePolynomial.eval_constant]
      exact le_refl _ }

/-- The rational unit is preserved by every finite natural power. -/
private theorem unit_power : (exponent : Nat) → (1 : Rational) ^ exponent = 1
  | 0 => rfl
  | exponent + 1 => by rw [pow_succ, unit_power exponent, Rat.Fraction.Field.one_mul]

/-- Every original natural coordinate power has exact unit quadrance on the whole rational circle. -/
@[expose] public def Certificate.coordinatePower (exponent : Nat) :
    Certificate (Dense.Gaussian.Power.polynomialPower (linearFactor 0) exponent) :=
  { bound := 1
    positive := by decide
    lower := by
      intro point unit
      rewrite [Dense.Gaussian.Power.eval_polynomialPower, Dense.Gaussian.LinearFactor.linearFactor_eval,
        Gaussian.Basic.sub_zero, Gaussian.Power.normSq_pow, Gaussian.Norm.Basic.normSq_eq_canonical,
        unit, unit_power exponent]
      exact le_refl _ }

/-- A strictly interior rational root gives an explicit margin for its original monic linear factor. -/
@[expose] public def Certificate.linearInside (root : Canonical) (inside : root.normSq < 1) :
    Certificate (linearFactor root) :=
  { bound := (1 - root.normSq) ^ 2 / 4
    positive := Field.div_pos_direct (Arithmetic.pow_pos_direct (Arithmetic.sub_pos_direct inside) 2) (by decide)
    lower := by
      intro point unit
      rw [Dense.Gaussian.LinearFactor.linearFactor_eval, Gaussian.Basic.sub_eq_add_neg]
      have gap : 1 - root.normSq ≤ Gaussian.Norm.Basic.normSq point - Gaussian.Norm.Basic.normSq (-root) := by
        rewrite [Gaussian.Norm.Basic.normSq_eq_canonical, unit,
          Gaussian.Norm.Basic.normSq_neg, Gaussian.Norm.Basic.normSq_eq_canonical]
        exact le_refl _
      have lower := Gaussian.Norm.Bounds.normSq_add_lower_of_gap
        (Arithmetic.sub_pos_direct inside) gap
      rewrite [Gaussian.Norm.Basic.normSq_eq_canonical point, unit] at lower
      exact lower }

/-- A strictly exterior rational root gives an explicit margin for its original monic linear factor. -/
@[expose] public def Certificate.linearOutside (root : Canonical) (outside : 1 < root.normSq) :
    Certificate (linearFactor root) :=
  { bound := (root.normSq - 1) ^ 2 / (4 * root.normSq)
    positive := Field.div_pos_direct (Arithmetic.pow_pos_direct (Arithmetic.sub_pos_direct outside) 2)
      (Arithmetic.mul_pos_direct (by decide) ((by decide : (0 : Rational) < 1).trans outside))
    lower := by
      intro point unit
      rw [Dense.Gaussian.LinearFactor.linearFactor_eval, Gaussian.Basic.sub_eq_add_neg,
        Gaussian.Basic.add_comm point (-root)]
      have gap : root.normSq - 1 ≤ Gaussian.Norm.Basic.normSq (-root) - Gaussian.Norm.Basic.normSq point := by
        rewrite [Gaussian.Norm.Basic.normSq_neg, Gaussian.Norm.Basic.normSq_eq_canonical,
          Gaussian.Norm.Basic.normSq_eq_canonical, unit]
        exact le_refl _
      have lower := Gaussian.Norm.Bounds.normSq_add_lower_of_gap
        (Arithmetic.sub_pos_direct outside) gap
      rewrite [Gaussian.Norm.Basic.normSq_neg, Gaussian.Norm.Basic.normSq_eq_canonical] at lower
      exact lower }

end Purelib.Polynomial.Clearance.Circle
