module

public import Purelib.Polynomial.Winding.Box.Rouche.Connection
public import Purelib.Polynomial.Clearance.Box.Dominance.Scale
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Algebra.Ring.Normalization
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data.Gaussian
open Purelib.Algebra

public section

namespace Purelib.Polynomial.Winding.Box.Rouche.Connection

namespace OrientedRouche

/-- Read the rational coefficient interpolation while preserving both literal endpoint polynomials.

Interior readings use the original base and scaled retained perturbation.
Endpoint branches retain the original coefficient tables even when the base
representation contains leading zeros.
-/
@[expose] def polynomialAt {base target : CoefficientPolynomial} {box : Box}
    (certificate : OrientedRouche base target box) (time : Rational) : CoefficientPolynomial :=
  if time = 0 then base else if time = 1 then target
  else base + DensePolynomial.scale (⟨time, 0⟩ : Canonical) certificate.perturbation

/-- The zero-parameter reading is the exact original base coefficient polynomial. -/
theorem at_zero {base target : CoefficientPolynomial} {box : Box}
    (certificate : OrientedRouche base target box) : certificate.polynomialAt 0 = base := by
  rw [polynomialAt, if_pos rfl]

/-- The unit-parameter reading is the exact original target coefficient polynomial. -/
theorem at_one {base target : CoefficientPolynomial} {box : Box}
    (certificate : OrientedRouche base target box) : certificate.polynomialAt 1 = target := by
  rw [polynomialAt, if_neg (by decide), if_pos rfl]

/-- Every interpolated reading has exactly the affine polynomial evaluation of the retained perturbation. -/
theorem eval_at {base target : CoefficientPolynomial} {box : Box}
    (certificate : OrientedRouche base target box) (time : Rational) (value : Canonical) :
    (certificate.polynomialAt time).eval value =
      base.eval value + (⟨time, 0⟩ : Canonical) * certificate.perturbation.eval value := by
  by_cases zero : time = 0
  · subst time
    rw [certificate.at_zero]
    change base.eval value = base.eval value + 0 * certificate.perturbation.eval value
    rw [zero_mul, add_zero]
  by_cases one : time = 1
  · subst time
    have targetEval := congrArg (fun polynomial : CoefficientPolynomial => polynomial.eval value)
      certificate.target_eq_add
    rw [DensePolynomial.eval_add] at targetEval
    rw [certificate.at_one, targetEval]
    change base.eval value + certificate.perturbation.eval value =
      base.eval value + 1 * certificate.perturbation.eval value
    rw [one_mul]
  · rw [polynomialAt, if_neg zero, if_neg one, DensePolynomial.eval_add, DensePolynomial.eval_scale]

/-- The scaled perturbation gives an oriented Rouché certificate to its actual coefficient sum. -/
@[expose] def scaled {base target : CoefficientPolynomial} {box : Box}
    (certificate : OrientedRouche base target box) (time : Rational)
    (inside : 0 ≤ time ∧ time ≤ 1) :
    OrientedRouche base (base + DensePolynomial.scale (⟨time, 0⟩ : Canonical) certificate.perturbation) box where
  perturbation := DensePolynomial.scale (⟨time, 0⟩ : Canonical) certificate.perturbation
  target_eq_add := rfl
  dominance := certificate.dominance.scale time inside

/-- The interior oriented certificate retains exactly the original positive dominance margin. -/
theorem scaled_margin {base target : CoefficientPolynomial} {box : Box}
    (certificate : OrientedRouche base target box) (time : Rational)
    (inside : 0 ≤ time ∧ time ≤ 1) :
    (certificate.scaled time inside).dominance.margin = certificate.dominance.margin := rfl

end OrientedRouche

namespace RoucheConnection

/-- Read the original connection's rational coefficient interpolation in its retained direction. -/
@[expose] def polynomialAt {left right : CoefficientPolynomial} {box : Box} :
    RoucheConnection left right box → Rational → CoefficientPolynomial
  | .equal _, _ => left
  | .forward certificate, time => certificate.polynomialAt time
  | .backward certificate, time => certificate.polynomialAt (1 - time)

/-- The interpolation starts at the exact original left coefficient polynomial. -/
theorem at_zero {left right : CoefficientPolynomial} {box : Box}
    (connection : RoucheConnection left right box) : connection.polynomialAt 0 = left := by
  cases connection with
  | equal same => rfl
  | forward certificate => exact certificate.at_zero
  | backward certificate =>
      change certificate.polynomialAt (1 - 0) = left
      rewrite [Ring.Normalization.sub_zero]
      exact certificate.at_one

/-- The interpolation finishes at the exact original right coefficient polynomial. -/
theorem at_one {left right : CoefficientPolynomial} {box : Box}
    (connection : RoucheConnection left right box) : connection.polynomialAt 1 = right := by
  cases connection with
  | equal same => exact same
  | forward certificate => exact certificate.at_one
  | backward certificate =>
      change certificate.polynomialAt (1 - 1) = right
      rw [sub_self]
      exact certificate.at_zero

/-- Reversing a connection reverses exactly its rational coefficient parameter. -/
theorem reverse_at {left right : CoefficientPolynomial} {box : Box}
    (connection : RoucheConnection left right box) (time : Rational) :
    connection.reverse.polynomialAt time = connection.polynomialAt (1 - time) := by
  cases connection with
  | equal same => exact same.symm
  | forward certificate => rfl
  | backward certificate =>
      change certificate.polynomialAt time = certificate.polynomialAt (1 - (1 - time))
      have complement : 1 - (1 - time) = time := by ring1
      rw [complement]

/-- Every connection reading evaluates as the affine interpolation of its two original endpoint values.

The backward orientation uses the complemented parameter and the original
retained perturbation. The equation holds for literal endpoint representations
as well as interior normalized coefficient readings.
-/
theorem eval_at {left right : CoefficientPolynomial} {box : Box}
    (connection : RoucheConnection left right box) (time : Rational) (value : Canonical) :
    (connection.polynomialAt time).eval value =
      left.eval value + (⟨time, 0⟩ : Canonical) * (right.eval value - left.eval value) := by
  cases connection with
  | equal same =>
      cases same
      change left.eval value = left.eval value + (⟨time, 0⟩ : Canonical) * (left.eval value - left.eval value)
      rw [sub_self, mul_zero, add_zero]
  | forward certificate =>
      have targetEval := congrArg (fun polynomial : CoefficientPolynomial => polynomial.eval value)
        certificate.target_eq_add
      rw [DensePolynomial.eval_add] at targetEval
      change (certificate.polynomialAt time).eval value = _
      rw [certificate.eval_at, targetEval]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im,
          Basic.mul_re, Basic.mul_im] <;> ring1
  | backward certificate =>
      have targetEval := congrArg (fun polynomial : CoefficientPolynomial => polynomial.eval value)
        certificate.target_eq_add
      rw [DensePolynomial.eval_add] at targetEval
      change (certificate.polynomialAt (1 - time)).eval value = _
      rw [certificate.eval_at, targetEval]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im,
          Basic.mul_re, Basic.mul_im] <;> ring1

/-- Complementing a retained unit-interval parameter keeps it in the same closed interval. -/
theorem complement_inside (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    0 ≤ 1 - time ∧ 1 - time ≤ 1 := by
  constructor
  · exact Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_nonneg_direct inside.2
  · have order := Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_le_sub_left_direct inside.1 1
    rewrite [Ring.Normalization.sub_zero] at order
    exact order

end RoucheConnection

end Purelib.Polynomial.Winding.Box.Rouche.Connection

end
