module
import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
-- Multiplication publicly retains Evaluation and its ascending coefficient owner.
import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Extensionality

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Ascending integer tables as normalized rational dense polynomials

Reversal and the original integer cast retain the exact coefficients before
normalization. Direct finite fold certificates identify ascending evaluation
with the retained descending Horner scan. Scalar operation laws transport the
same coefficient-table arithmetic and repeated shifts to dense polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic

open Purelib.Polynomial
open Purelib.Data.Rat

/-- Embed each integer in a retained coefficient list into constructive rationals, preserving order.

The original finite map preserves every coefficient position and integer
value, using the retained rational integer cast at each entry. -/
@[expose] public def castCoefficients (coefficients : List Int) : List Fraction.Rational :=
  List.map (fun coefficient : Int => (coefficient : Fraction.Rational)) coefficients

/-- Reverse an ascending integer coefficient table, embed its entries and normalize the descending rational polynomial.

The original ascending coefficient table is reversed, cast entrywise, then
normalized. This retains the same descending coefficient construction and its
exact zero-trimming operation. -/
@[expose] public def ofAscending (coefficients : List Int) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Basic.DensePolynomial.normalize ⟨castCoefficients coefficients.reverse⟩

/-- Conversion from ascending integer coefficients returns an already normalized rational polynomial. -/
@[simp] public theorem ofAscending_normalized (coefficients : List Int) :
    (ofAscending coefficients).normalize = ofAscending coefficients :=
  Dense.Basic.DensePolynomial.normalize_normalize _

/-- Conversion from ascending integer coefficients preserves rational evaluation.

The original reversal accumulator and scalar cast transports identify both
Horner folds on the same input table. Normalization preserves that retained
evaluation. -/
@[simp] public theorem eval_ofAscending (coefficients : List Int)
    (point : Fraction.Rational) :
    (ofAscending coefficients).eval point = Ascending.Integer.Basic.eval coefficients point := by
  rw [ofAscending, Dense.Basic.DensePolynomial.eval_normalize]
  exact Dense.Basic.DensePolynomial.evalCoeffs_reverse_intCast coefficients point

/-- The empty ascending coefficient table converts to the zero dense polynomial. -/
public theorem ofAscending_zero : ofAscending [] = 0 := rfl

/-- The ascending singleton one converts to the dense constant-one polynomial. -/
public theorem ofAscending_one : ofAscending [1] = Dense.Basic.DensePolynomial.constant (1 : Fraction.Rational) := by
  change (Dense.Basic.DensePolynomial.constant ((1 : Int) : Fraction.Rational)).normalize =
    Dense.Basic.DensePolynomial.constant (1 : Fraction.Rational)
  rewrite [Int.cast_one]
  exact Dense.Basic.DensePolynomial.normalize_constant_of_ne Fraction.Field.zero_ne_one.symm

/-- Conversion from ascending integer coefficients preserves polynomial addition.

The original padded integer addition and dense zero-padded addition have
the same scalar evaluations. Their retained normalization certificates
identify the complete coefficient representations. -/
public theorem ofAscending_add (left right : List Int) :
    ofAscending (Ascending.Integer.Basic.Certificate.add left right) =
      ofAscending left + ofAscending right := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (Dense.Basic.DensePolynomial.normalize_add _ _)
  intro point
  rw [eval_ofAscending, Ascending.Integer.Basic.eval_add,
    Dense.Basic.DensePolynomial.eval_add,
    eval_ofAscending, eval_ofAscending]

open Purelib.Algebra.Group in
/-- Conversion from ascending integer coefficients preserves polynomial negation.

The original coefficient negative-unit scaling and dense scalar negation
have the same rational evaluations. Their original normalized coefficients
therefore coincide. -/
public theorem ofAscending_neg (coefficients : List Int) :
    ofAscending (Ascending.Integer.Basic.neg coefficients) = -ofAscending coefficients := by
  letI : SubNegZeroMonoid Fraction.Rational := Negation.subNegZeroMonoid
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (Dense.Basic.DensePolynomial.normalize_neg _)
  intro point
  rw [eval_ofAscending, Ascending.Integer.Basic.eval_neg,
    Dense.Basic.DensePolynomial.eval_neg, eval_ofAscending]

/-- Conversion from ascending integer coefficients preserves polynomial subtraction.

The original padded coefficient difference retains both input tables.
Scalar evaluation identifies its normalized dense image with subtraction
of those same retained dense inputs. -/
public theorem ofAscending_sub (left right : List Int) :
    ofAscending (Ascending.Integer.Basic.sub left right) =
      ofAscending left - ofAscending right := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (Dense.Basic.DensePolynomial.normalize_sub _ _)
  intro point
  rw [eval_ofAscending, Ascending.Integer.Basic.eval_sub,
    Dense.Basic.DensePolynomial.eval_sub,
    eval_ofAscending, eval_ofAscending]

/-- Conversion from ascending integer coefficients preserves polynomial multiplication.

The original integer convolution retains its scaled right lists and shifted
tail products. Their evaluations identify the normalized dense product of
the same two retained input polynomials. -/
public theorem ofAscending_mul (left right : List Int) :
    ofAscending (Ascending.Integer.Basic.Certificate.mul left right) =
      ofAscending left * ofAscending right := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (Dense.Basic.DensePolynomial.normalize_mul _ _)
  intro point
  rw [eval_ofAscending, Ascending.Integer.Basic.eval_mul,
    Dense.Basic.DensePolynomial.eval_mul,
    eval_ofAscending, eval_ofAscending]

/-- Scaling an ascending integer table converts to scaling its dense polynomial by the embedded integer.

The original integer coefficient scaling casts the same retained factor
into rational scalar multiplication. Evaluation and normalization identify
both complete dense coefficient representations. -/
public theorem ofAscending_scale (factor : Int) (coefficients : List Int) :
    ofAscending (Ascending.Integer.Basic.Certificate.scale factor coefficients) =
      Dense.Basic.DensePolynomial.scale
        (factor : Fraction.Rational) (ofAscending coefficients) := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (Dense.Basic.DensePolynomial.normalize_scale _ _)
  intro point
  rw [eval_ofAscending, Ascending.Integer.Basic.eval_scale,
    Dense.Basic.DensePolynomial.eval_scale,
    eval_ofAscending]

/-- Repeat the ascending-list multiplication-by-`X` operation.

Each successor request applies the original single-degree shift to the
completed smaller shift. The same coefficient table and exponent are retained. -/
@[expose] public def shiftN : Nat → List Int → List Int
  | 0, coefficients => coefficients
  | exponent + 1, coefficients => Ascending.Integer.Basic.shift
    (Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic.shiftN exponent coefficients)

/-- Repeated ascending coefficient shifts multiply evaluation by the corresponding point power.

Each retained shift multiplies by the same supplied rational point.
Structural induction preserves the original table evaluation and exponent. -/
@[simp] public theorem eval_shiftN : ∀ exponent : Nat,
    ∀ coefficients : List Int, ∀ point : Fraction.Rational,
    Ascending.Integer.Basic.eval (shiftN exponent coefficients) point =
      Ascending.Integer.Basic.eval coefficients point * point ^ exponent
  | 0, coefficients, point => by rw [shiftN, pow_zero, mul_one]
  | exponent + 1, coefficients, point => by
      rw [shiftN, Ascending.Integer.Basic.eval_shift,
        eval_shiftN exponent coefficients point,
        pow_succ]
      ring0

/-- Repeated ascending shifts convert to the matching dense polynomial shift.

The repeated original coefficient shift and dense degree shift have the
same retained rational evaluations and normalization certificates. -/
public theorem ofAscending_shiftN (exponent : Nat) (coefficients : List Int) :
    ofAscending (shiftN exponent coefficients) =
      Dense.Basic.DensePolynomial.shift exponent
        (ofAscending coefficients) := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (Dense.Basic.DensePolynomial.normalize_shift _ _)
  intro point
  rw [eval_ofAscending, eval_shiftN,
    Dense.Basic.DensePolynomial.eval_shift,
    eval_ofAscending]
end Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
