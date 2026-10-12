module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
import Purelib.Polynomial.Ascending.Rational.Convolution
public import Purelib.Polynomial.Ascending.Rational.Monomial

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Polynomial.Ascending.Rational.Truncation

/-! ## Bounded coefficient identities used by the local inverse law -/

/-- Equality of polynomial coefficients at every degree strictly below a finite bound. -/
def EqualBelow (count : Nat) (left right :
  CoefficientPolynomial) : Prop :=
  ∀ degree, degree < count →
    Ascending.Rational.Basic.coefficient left degree = Ascending.Rational.Basic.coefficient right degree

/-- Vanishing of every polynomial coefficient strictly below a finite bound. -/
def VanishesBelow (count : Nat) (polynomial :
  CoefficientPolynomial) : Prop :=
  ∀ degree, degree < count → Ascending.Rational.Basic.coefficient polynomial degree = 0

/-- Restrict coefficientwise equality to any finite initial range of degrees. -/
theorem CoefficientwiseEqual.equalBelow {left right :
  CoefficientPolynomial}
    (equal : Ascending.Rational.Coefficientwise.CoefficientwiseEqual left right) (count : Nat) :
    EqualBelow count left right := fun degree _ => equal degree

/-- A polynomial agrees with itself below every degree bound. -/
theorem equalBelow_refl (count : Nat) (polynomial :
  CoefficientPolynomial) :
    EqualBelow count polynomial polynomial := fun _ _ => rfl

/-- Reverse equality below a fixed degree bound. -/
theorem equalBelow_symm {count : Nat} {left right :
  CoefficientPolynomial}
    (equal : EqualBelow count left right) : EqualBelow count
      right left :=
  fun degree below => (equal degree below).symm

/-- Compose coefficient equalities below the same degree bound. -/
theorem equalBelow_trans {count : Nat} {first second third :
  CoefficientPolynomial}
    (firstSecond : EqualBelow count first second)
    (secondThird : EqualBelow count second third) :
    EqualBelow count first third :=
  fun degree below => (firstSecond degree below).trans
    (secondThird degree below)

/-- Addition preserves equality below a shared degree bound in both arguments. -/
theorem equalBelow_add {count : Nat}
    {left left' right right' : CoefficientPolynomial}
    (leftEqual : EqualBelow count left left')
    (rightEqual : EqualBelow count right right') :
    EqualBelow count (Ascending.Rational.Basic.add left right)
      (Ascending.Rational.Basic.add left' right') := by
  intro degree below
  rw [Ascending.Rational.Basic.coefficient_add, Ascending.Rational.Basic.coefficient_add,
    leftEqual degree below, rightEqual degree below]

/-- Rational scaling preserves equality below a degree bound. -/
theorem equalBelow_scale (factor : Fraction.Rational) {count :
  Nat}
    {left right : CoefficientPolynomial} (equal : EqualBelow
      count left right) :
    EqualBelow count (Ascending.Rational.Basic.scale factor left)
      (Ascending.Rational.Basic.scale factor right) := by
  intro degree below
  rw [Ascending.Rational.Basic.coefficient_scale, Ascending.Rational.Basic.coefficient_scale, equal degree below]

/-- Multiplication preserves equality below a shared degree bound.

For a coefficient below the bound, both complementary indices in its finite convolution also lie below the bound. -/
theorem equalBelow_mul {count : Nat}
    {left left' right right' : CoefficientPolynomial}
    (leftEqual : EqualBelow count left left')
    (rightEqual : EqualBelow count right right') :
    EqualBelow count (Ascending.Rational.Basic.mul left right)
      (Ascending.Rational.Basic.mul left' right') := open Purelib.Algebra in by
  intro degree below
  rw [Ascending.Rational.Convolution.coefficient_mul, Ascending.Rational.Convolution.coefficient_mul]
  apply FiniteSum.Prefix.coordinateSum_congr_lt
  intro index inSum
  rw [leftEqual index ((Nat.le_of_lt_succ inSum).trans_lt below),
    rightEqual (degree - index) ((Nat.sub_le degree index).trans_lt below)]

/-- Scaling preserves vanishing below a degree bound. -/
theorem vanishesBelow_scale (factor : Fraction.Rational) {count
  : Nat}
    {polynomial : CoefficientPolynomial} (vanishes :
      VanishesBelow count polynomial) :
    VanishesBelow count (Ascending.Rational.Basic.scale factor polynomial) := by
  intro degree below
  rw [Ascending.Rational.Basic.coefficient_scale, vanishes degree below,
    Fraction.Field.mul_zero_direct]

/-- A monomial vanishes below every bound at most its degree. -/
theorem vanishesBelow_monomial (count degree : Nat) (order :
  count ≤ degree)
    (value : Fraction.Rational) : VanishesBelow count
      (Ascending.Rational.Monomial.monomial degree value) := by
  intro outputDegree below
  rw [Ascending.Rational.Monomial.coefficient_monomial,
    if_neg (Nat.ne_of_lt (below.trans_le order))]

/-- A product vanishes below any bound below which its left factor vanishes. -/
theorem vanishesBelow_mul_left {count : Nat} {left :
  CoefficientPolynomial}
    (vanishes : VanishesBelow count left) (right :
      CoefficientPolynomial) :
    VanishesBelow count (Ascending.Rational.Basic.mul left right) := open Purelib.Algebra
      in by
  intro degree below
  rw [Ascending.Rational.Convolution.coefficient_mul]
  rw [FiniteSum.Prefix.coordinateSum_congr_lt (degree + 1) (by
    intro index inSum
    rw [vanishes index
        ((Nat.le_of_lt_succ inSum).trans_lt below),
      Fraction.Field.zero_mul_direct])]
  exact FiniteSum.Prefix.coordinateSum_all_zero (fun _ => (0 : Fraction.Rational))
    (fun _ => rfl) (degree + 1)

/-- Adding a polynomial that vanishes below the bound preserves the other coefficients there. -/
theorem vanishesBelow_add_right {count : Nat} {left right :
  CoefficientPolynomial}
    (vanishes : VanishesBelow count right) :
    EqualBelow count (Ascending.Rational.Basic.add left right) left := by
  intro degree below
  rw [Ascending.Rational.Basic.coefficient_add, vanishes degree below]
  ring1

/-- A polynomial with zero constant term has its `n`th power vanishing below degree `n`.

Each low convolution coefficient either uses an already vanishing coefficient of the preceding power or the zero
constant of the final factor. -/
theorem vanishesBelow_pow_of_zero_constant {polynomial :
  CoefficientPolynomial}
    (zeroConstant : Ascending.Rational.Basic.coefficient polynomial 0 = 0) : ∀ exponent,
    VanishesBelow exponent (Ascending.Rational.Basic.pow polynomial exponent)
  | 0 => fun degree below => (Nat.not_lt_zero degree below).elim
  | exponent + 1 => by
      intro degree below
      rw [Ascending.Rational.Basic.pow, Purelib.Polynomial.Ascending.Rational.Convolution.coefficient_mul]
      rw [Purelib.Algebra.FiniteSum.Prefix.coordinateSum_congr_lt (degree + 1) (by
        intro index inSum
        by_cases before : index < exponent
        · rw [vanishesBelow_pow_of_zero_constant zeroConstant exponent
              index before,
            Purelib.Data.Rat.Fraction.Field.zero_mul_direct]
        · have degreeLe : degree ≤ exponent := Nat.le_of_lt_succ below
          have indexLe : index ≤ degree := Nat.le_of_lt_succ inSum
          have exponentLe : exponent ≤ index := Nat.le_of_not_gt before
          have indexEqual : index = exponent :=
            Nat.le_antisymm (indexLe.trans degreeLe) exponentLe
          subst index
          have degreeEqual : degree = exponent :=
            Nat.le_antisymm degreeLe indexLe
          subst degree
          rw [Nat.sub_self, zeroConstant,
            Purelib.Data.Rat.Fraction.Field.mul_zero_direct])]
      exact Purelib.Algebra.FiniteSum.Prefix.coordinateSum_all_zero (fun _ => (0 : Fraction.Rational))
        (fun _ => rfl) (degree + 1)

/-- Dropping an initial coefficient block translates all subsequent coefficient indices. -/
theorem coefficientCoefficients_drop : ∀ count coefficients
  degree,
    Ascending.Rational.Basic.coefficientCoefficients (coefficients.drop count) degree =
      Ascending.Rational.Basic.coefficientCoefficients coefficients (count + degree)
  | 0, coefficients, degree => by rw [List.drop_zero, Nat.zero_add]
  | count + 1, [], degree => by
      rw [List.drop_nil, Ascending.Rational.Basic.coefficientCoefficients_nil,
        Ascending.Rational.Basic.coefficientCoefficients_nil]
  | count + 1, coefficient :: remaining, degree => by
      rw [List.drop_succ_cons,
        coefficientCoefficients_drop count remaining degree]
      rw [show count + 1 + degree = (count + degree) + 1 by ring1,
        Ascending.Rational.Basic.coefficientCoefficients_cons_succ]
end Purelib.Polynomial.Ascending.Rational.Truncation

end
