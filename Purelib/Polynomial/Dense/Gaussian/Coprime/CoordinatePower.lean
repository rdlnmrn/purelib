module

import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Polynomial.Dense.Multiplication
public import Mathlib.Tactic.Ring.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Polynomial

section
/-!
# Executable squarefreeness under finite coefficient reversal

Clear the reciprocal denominators in the original finite Bézout identity.
This gives a power of the coordinate in the ideal of the reversed polynomial
and its derivative. The reversed constant coefficient is the original
nonzero leading coefficient; a finite recursive Bézout calculation removes
that coordinate power. No root enumeration or nonzero affine constant term
is assumed.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.CoordinatePower

set_option genInjectivity false in
/-- Explicit coefficient witnesses for coprimality with a coordinate power.
The recursion retains its coefficients instead of rerunning extended Euclid
at every exponent. -/
structure PowerBezout (polynomial :
  CoefficientPolynomial) (degree : Nat) where
  /-- The polynomial coefficient multiplying the retained polynomial. -/ left :
    CoefficientPolynomial
  /-- The polynomial coefficient multiplying the requested coordinate power. -/ right :
    CoefficientPolynomial
  /-- The two stored coefficients express one at every Gaussian-rational point. -/ identity : ∀ point, 1 = left.eval
    point * polynomial.eval point + right.eval point * point ^ degree

constructive_injectivity PowerBezout

/-- Lift a Bézout identity against the coordinate to any natural coordinate power.

The recursion retains the preceding coefficient witnesses and builds the next pair by polynomial multiplication and
shifting. -/
@[expose] def powerBezout (polynomial left right :
  CoefficientPolynomial)
    (identity : ∀ point, 1 = left.eval point * polynomial.eval point + right.eval point * point) :
    (degree : Nat) → PowerBezout polynomial degree
  | 0 => ⟨0, DensePolynomial.constant 1, by intro point; simp only [DensePolynomial.eval_zero,
    DensePolynomial.eval_constant, zero_mul, pow_zero]; ring1⟩
  | degree + 1 =>
      let previous := powerBezout polynomial left right
        identity degree
      { left := previous.left + previous.right * DensePolynomial.shift degree left
        right := previous.right * right
        identity := by
          intro point
          rw [DensePolynomial.eval_add, DensePolynomial.eval_mul,
            DensePolynomial.eval_shift, DensePolynomial.eval_mul, pow_succ]
          calc
            1 = previous.left.eval point * polynomial.eval point +
                previous.right.eval point * point ^ degree := previous.identity point
            _ = previous.left.eval point * polynomial.eval point +
                previous.right.eval point * point ^ degree *
                  (left.eval point * polynomial.eval point + right.eval point * point) := by rw [← identity]; ring1
            _ = _ := by ring1 }

/-- The nonzero constant term gives a direct finite Bézout witness against
every requested coordinate power. -/
@[expose] def ofOrigin (polynomial :
  CoefficientPolynomial) (originNonzero : polynomial.eval 0 ≠ 0) (degree :
    Nat) :
    PowerBezout polynomial degree :=
  let inverse := (polynomial.eval 0)⁻¹
  let left := DensePolynomial.constant inverse
  let right := DensePolynomial.scale (-inverse) (Dense.Gaussian.Reciprocal.originTail polynomial)
  powerBezout polynomial left right (by
    intro point
    dsimp only [left, right]
    rw [DensePolynomial.eval_constant, DensePolynomial.eval_scale]
    calc
      1 = inverse * polynomial.eval 0 :=
        (Gaussian.Basic.Canonical.inv_mul_cancel _ originNonzero).symm
      _ = _ := by rw [Dense.Gaussian.Reciprocal.origin_decomposition polynomial point]; ring1) degree

/-- Clear an explicit power identity using the same stored coefficient
witnesses. The only Euclidean certificate conversion happens at the end. -/
@[expose] def ofPowerIdentity (polynomial derivative :
  CoefficientPolynomial)
    (nonzero : polynomial.isZero = false) (originNonzero : polynomial.eval 0 ≠ 0)
    (degree : Nat) (left right : CoefficientPolynomial)
    (identity : ∀ point, point ^ degree = left.eval point * polynomial.eval point + right.eval point * derivative.eval
      point) :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate polynomial derivative := by
  let power := ofOrigin polynomial originNonzero degree
  apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity polynomial derivative (Or.inl nonzero)
    (power.left + power.right * left) (power.right * right)
  intro point
  rw [DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_mul]
  calc
    1 = power.left.eval point * polynomial.eval point + power.right.eval point * point ^ degree := power.identity point
    _ = _ := by rw [identity]; ring1
end Purelib.Polynomial.Dense.Gaussian.Coprime.CoordinatePower

end
