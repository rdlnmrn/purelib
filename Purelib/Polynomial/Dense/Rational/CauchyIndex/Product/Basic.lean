module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Sign.Jump
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic

/-- The sign jump from one to the product of the three denominator-coordinate values. -/
def auxiliaryEndpointCorrection2
    (B D H : CoordinatePolynomial) (x : Fraction.Rational) : Nat :=
  Data.Rat.Sign.Jump.signJump 1 (H.eval x * (B.eval x * D.eval x))

/-- The doubled Cauchy-index product identity with endpoint corrections.

It relates the displayed product pair to the two factor pairs, retaining the correction at each oriented endpoint. -/
def AuxiliaryProductFormula
    (A B C D E H : CoordinatePolynomial) (a b : Fraction.Rational) : Prop :=
  Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 E H a b =
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 A B a b + Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 C
      D a b -
      (auxiliaryEndpointCorrection2 B D H a : Int) +
      auxiliaryEndpointCorrection2 B D H b

/-- Auxiliary product formulas compose under exact interval subdivision. -/
theorem AuxiliaryProductFormula.add
    {A B C D E H : CoordinatePolynomial} {a b c : Fraction.Rational}
    (left : AuxiliaryProductFormula A B C D E H a b)
    (right : AuxiliaryProductFormula A B C D E H b c) :
    AuxiliaryProductFormula A B C D E H a c := by
  unfold AuxiliaryProductFormula at left right ⊢
  rw [Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add E H a b c,
    Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add A B a b c,
    Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add C D a b c]
  rw [left, right]
  ring1

/-- Reversing an interval reverses its auxiliary product formula. -/
theorem AuxiliaryProductFormula.reverse
    {A B C D E H : CoordinatePolynomial} {a b : Fraction.Rational}
    (formula : AuxiliaryProductFormula A B C D E H a b) :
    AuxiliaryProductFormula A B C D E H b a := by
  unfold AuxiliaryProductFormula at formula ⊢
  rw [Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse E H a b,
    Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse A B a b,
    Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse C D a b]
  rw [formula]
  ring1

/-- The auxiliary identity is symmetric in its two displayed complex
factors. -/
theorem AuxiliaryProductFormula.swap
    {A B C D E H : CoordinatePolynomial} {a b : Fraction.Rational}
    (formula : AuxiliaryProductFormula A B C D E H a b) :
    AuxiliaryProductFormula C D A B E H a b := by
  have correction : ∀ x : Fraction.Rational,
      auxiliaryEndpointCorrection2 D B H x =
        auxiliaryEndpointCorrection2 B D H x := by
    intro x
    unfold auxiliaryEndpointCorrection2
    rw [mul_comm (D.eval x) (B.eval x)]
  unfold AuxiliaryProductFormula at formula ⊢
  rw [correction a, correction b]
  rw [formula]
  ring1

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic

end
