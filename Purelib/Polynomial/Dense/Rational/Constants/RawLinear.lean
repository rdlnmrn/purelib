module

-- The original public rational aliases and scalar parents remain available to clients.
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.List.DropWhile.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Raw two-slot rational constants

The coefficient table `[0, value]` retains its leading zero until normalization.
The finite leading-zero scan removes that slot and, for a nonzero value, retains
the constant coefficient. Evaluation consumes the original untrimmed table.
-/

namespace Purelib.Polynomial.Dense.Rational.Constants.RawLinear

open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

/-- Retain the descending coefficient table `[0, value]` of a rational constant.

The first slot is an explicit representation zero. Construction keeps both
slots, including when the supplied constant is itself zero. -/
@[expose] public def rawConstant (value : Fraction.Rational) : DensePolynomial Fraction.Rational :=
  ⟨[0, value]⟩

/-- The raw two-slot table evaluates to its retained constant coefficient.

The initial zero contributes nothing to the original descending Horner scan,
so this equality holds for every supplied evaluation point and constant. -/
@[simp] public theorem rawConstant_eval (value t : Fraction.Rational) :
    (rawConstant value).eval t = value := by
  change DensePolynomial.evalCoeffs t (0 :: [value]) = value
  exact (DensePolynomial.evalCoeffs_cons_zero t [value]).trans
    (DensePolynomial.eval_constant value t)

/-- Normalization of a nonzero raw constant retains exactly its constant slot.

The leading zero is discarded by the finite scan. The nonzero hypothesis
then selects the branch that retains the supplied constant coefficient. -/
public theorem rawConstant_normalize {value : Fraction.Rational}
    (nonzero : value ≠ 0) :
    (rawConstant value).normalize = DensePolynomial.constant value := by
  apply DensePolynomial.ext
  change ([0, value].dropWhile (fun coefficient => decide (coefficient = 0))) = [value]
  rewrite [DropWhile.cons_of_true (fun coefficient : Fraction.Rational => decide (coefficient = 0))
    0 [value] (decide_eq_true (Eq.refl (0 : Fraction.Rational)))]
  exact DropWhile.cons_of_false (fun coefficient => decide (coefficient = 0))
    value [] (decide_eq_false nonzero)

/-- A raw constant table with a nonzero coefficient fails the zero test.

Normalization retains the single supplied coefficient, whose singleton list
is nonempty independently of its original leading representation zero. -/
public theorem rawConstant_isZero_false {value : Fraction.Rational}
    (nonzero : value ≠ 0) : (rawConstant value).isZero = false := by
  change (rawConstant value).normalize.coeffs.isEmpty = false
  rewrite [rawConstant_normalize nonzero]
  exact Eq.refl _

/-- A nonzero raw constant has exactly one normalized coefficient slot.

The count reads the singleton list retained by the original leading-zero
normalization, rather than the two slots of the raw representation. -/
public theorem rawConstant_degreeCount {value : Fraction.Rational}
    (nonzero : value ≠ 0) : (rawConstant value).degreeCount = 1 := by
  change (rawConstant value).normalize.coeffs.length = 1
  rewrite [rawConstant_normalize nonzero]
  exact Eq.refl _

/-- A nonzero raw constant has natural degree zero.

Natural degree subtracts one from the normalized coefficient count. The
single retained constant slot therefore has the original degree convention. -/
public theorem rawConstant_natDegree {value : Fraction.Rational}
    (nonzero : value ≠ 0) : (rawConstant value).natDegree = 0 := by
  change (rawConstant value).degreeCount - 1 = 0
  rewrite [rawConstant_degreeCount nonzero]
  exact Eq.refl _

/-- Negating the normalized nonzero raw constant still fails the zero test.

Negation and repeated normalization preserve the original Boolean zero
reading, so the same nonzero coefficient certifies this signed representation. -/
public theorem negNormalizedRawConstant_isZero_false {value : Fraction.Rational}
    (nonzero : value ≠ 0) : (-((rawConstant value).normalize)).isZero = false := by
  exact (DensePolynomial.isZero_neg _).trans
    ((DensePolynomial.isZero_normalize _).trans (rawConstant_isZero_false nonzero))

/-- The negated normalized nonzero raw constant has one degree slot.

The original negation and normalization laws preserve the count of normalized
coefficients, including the retained singleton constant representation. -/
public theorem negNormalizedRawConstant_degreeCount {value : Fraction.Rational}
    (nonzero : value ≠ 0) : (-((rawConstant value).normalize)).degreeCount = 1 := by
  exact (DensePolynomial.degreeCount_neg _).trans
    ((DensePolynomial.degreeCount_normalize _).trans (rawConstant_degreeCount nonzero))

end Purelib.Polynomial.Dense.Rational.Constants.RawLinear
