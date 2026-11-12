module

import Purelib.Polynomial.Dense.Derivative.Map
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field

/-!
# Original derivative interpretation in a ring with zero divisors

The original Gaussian square has a derivative whose value at a nilpotent
perturbation is nonzero and square-zero. Its actual derivative producer and
the same original finite-shift first jet agree at every target-ring point.
-/

namespace TestPurelib.Polynomial.Dense.Derivative.Map

open Purelib.Algebra.Quadratic
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Recurrence.Mode

/-- The original Gaussian coefficient field. -/
private abbrev Gaussian := Purelib.Data.Gaussian.Basic.Canonical

/-- The original quadratic ring with a square-zero coordinate. -/
private abbrev Dual := Pair Gaussian 0

/-- The original nonzero nilpotent coordinate. -/
private def epsilon : Dual := Pair.generator

/-- The same original scalar embedding retains the Gaussian source coefficient exactly. -/
private theorem injective : Function.Injective (Pair.scalar (radialSquare := (0 : Gaussian))) :=
  fun _ _ same => congrArg Pair.re same

/-- The original Gaussian repeated linear factor is stored in its original coefficient table. -/
private def square : DensePolynomial Gaussian := ⟨[1, -2, 1]⟩

/-- The original derivative scan agrees with the original mode first jet at every target-ring point. -/
private theorem every_point (root : Dual) :
    (Dense.Map.map Pair.scalar (Dense.Derivative.derivative square)).eval root =
      coefficientRow (Dense.Map.map Pair.scalar square).coeffs root 1 0 :=
  Dense.Derivative.Map.firstJet Pair.scalar Pair.scalar_zero injective Pair.scalar_add square root

/-- The original mapped derivative has its independent nonzero nilpotent reading. -/
private theorem derivative_value :
    (Dense.Map.map Pair.scalar (Dense.Derivative.derivative square)).eval (1 + epsilon) = 2 * epsilon := by
  decide +kernel

/-- The same first jet retains that original nilpotent derivative reading. -/
private theorem first_jet_value :
    coefficientRow (Dense.Map.map Pair.scalar square).coeffs (1 + epsilon) 1 0 = 2 * epsilon :=
  (every_point (1 + epsilon)).symm.trans derivative_value

/-- The retained derivative reading is nonzero even though its square vanishes. -/
private theorem derivative_nilpotent : (2 * epsilon : Dual) ≠ 0 ∧ (2 * epsilon : Dual) ^ 2 = 0 := by
  decide +kernel

/-- The original target-ring quadratic has a nilpotent coefficient. -/
private def first : DensePolynomial Dual := ⟨[1, epsilon, 1]⟩

/-- The original target-ring linear factor vanishes at the perturbed unit root. -/
private def second : DensePolynomial Dual := ⟨[1, -(1 + epsilon)]⟩

/-- The actual normalized original product obeys the general first-jet multiplication law. -/
private theorem product_readback : coefficientRow (first * second).coeffs (1 + epsilon) 1 0 =
    coefficientRow first.coeffs (1 + epsilon) 1 0 * second.eval (1 + epsilon) +
      first.eval (1 + epsilon) * coefficientRow second.coeffs (1 + epsilon) 1 0 :=
  coefficientRow_mul_first first second (1 + epsilon)

/-- Its same original first jet has the independent literal nilpotent value. -/
private theorem product_value : coefficientRow (first * second).coeffs (1 + epsilon) 1 0 =
    2 + 3 * epsilon := by
  rw [product_readback]
  decide +kernel

end TestPurelib.Polynomial.Dense.Derivative.Map
