module

-- The public degree comparison retains the original raw constant owner and scalar parents.
public import Purelib.Polynomial.Dense.Rational.Constants.RawLinear
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Translated rational coordinates

The original two-slot coefficient table `[1, -center]` represents the
coordinate minus its supplied center. Its nonzero leading coefficient fixes
the normalized count and degree without changing that representation.
-/

namespace Purelib.Polynomial.Dense.Rational.Linear.Translated

open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Constants

/-- Retain the descending translated-coordinate table `[1, -center]`.

Construction records the original monic leading coefficient and negated
center directly, with no normalization or replacement of either slot. -/
@[expose] public def affineVariable (center : Fraction.Rational) : DensePolynomial Fraction.Rational :=
  ⟨[1, -center]⟩

/-- Evaluating the translated coordinate subtracts its retained center.

The original descending Horner scan reads the leading one and negated
center at the supplied point. -/
@[simp] public theorem affineVariable_eval (center t : Fraction.Rational) :
    (affineVariable center).eval t = t - center := by
  change (0 * t + 1) * t + -center = t - center
  rewrite [MulZeroClass.zero_mul, _root_.zero_add, _root_.one_mul]
  exact (_root_.sub_eq_add_neg t center).symm

/-- The translated coordinate always fails the zero test.

Its leading coefficient is the nonzero rational one, so normalization retains
both original coefficient slots for every supplied center. -/
public theorem affineVariable_isZero_false (center : Fraction.Rational) :
    (affineVariable center).isZero = false := by
  change (⟨[1, -center]⟩ : DensePolynomial Fraction.Rational).normalize.coeffs.isEmpty = false
  rewrite [DensePolynomial.normalize_linear_of_leading_ne_zero
    (Ne.symm Fraction.Field.zero_ne_one)]
  exact Eq.refl _

/-- The translated coordinate has exactly two normalized coefficients.

The nonzero monic leading coefficient retains the original two-slot list,
including when the constant coefficient vanishes. -/
public theorem affineVariable_degreeCount (center : Fraction.Rational) :
    (affineVariable center).degreeCount = 2 := by
  change (⟨[1, -center]⟩ : DensePolynomial Fraction.Rational).normalize.coeffs.length = 2
  rewrite [DensePolynomial.normalize_linear_of_leading_ne_zero
    (Ne.symm Fraction.Field.zero_ne_one)]
  exact Eq.refl _

/-- The translated coordinate has natural degree one.

The original natural degree convention subtracts one from its two retained
normalized coefficient slots. -/
public theorem affineVariable_natDegree (center : Fraction.Rational) :
    (affineVariable center).natDegree = 1 := by
  change (affineVariable center).degreeCount - 1 = 1
  rewrite [affineVariable_degreeCount center]
  exact Eq.refl _

/-- A nonzero raw constant has smaller degree than a translated coordinate.

The raw constant normalizes to one slot, while the translated coordinate
retains two; their natural degrees are therefore zero and one respectively. -/
public theorem rawConstant_natDegree_lt_affineVariable
    {center value : Fraction.Rational} (nonzero : value ≠ 0) :
    (RawLinear.rawConstant value).natDegree < (affineVariable center).natDegree := by
  rewrite [RawLinear.rawConstant_natDegree nonzero, affineVariable_natDegree center]
  exact Nat.zero_lt_succ 0

end Purelib.Polynomial.Dense.Rational.Linear.Translated
