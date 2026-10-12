module

import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring.Basic
import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Algebra.Group.Basic
import Purelib.Tactic.Ring
public import Purelib.Algebra.Group.Negation

section
public section

/-!
# An explicit field-law interface

Mathlib's `Field` has several compatible inheritance paths to its multiplicative
operations.  Asking typeclass synthesis to choose between those paths can make an
otherwise finite proof depend on `Classical.choice`.  `ExplicitField` records the
small set of field laws needed by the executable polynomial algorithms through one
unambiguous operation path.

This is not a finiteness or cardinality assumption on the carrier.  It is only a
bundled interface for explicitly supplied operations and proofs.
-/

namespace Purelib.Algebra.Field

/-- A commutative ring with explicit inversion, division and nonzero-product laws.

The supplied operations satisfy division as multiplication by the inverse, cancellation for nonzero inputs, preservation
of nonzeroness and inverse negation. Nontriviality and a value for the inverse of zero are not required. -/
class ExplicitField (K : Type*) extends CommRing K, Inv K, Div K where
  /-- Division is multiplication by the supplied inverse. -/ div_eq_mul_inv : ∀ a b : K, a / b = a * b⁻¹
  /-- A scalar times its inverse is one when the scalar is nonzero. -/ mul_inv_cancel : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1
  /-- A product of supplied nonzero factors is nonzero. -/ mul_ne_zero : ∀ {a b : K}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
  /-- The inverse of a supplied nonzero scalar is nonzero. -/ inv_ne_zero : ∀ {a : K}, a ≠ 0 → a⁻¹ ≠ 0
  /-- Inversion commutes with negation for every scalar. -/ inv_neg : ∀ a : K, (-a)⁻¹ = -(a⁻¹)

namespace ExplicitField

variable {K : Type*} [ExplicitField K]

/-- A quotient with supplied nonzero numerator and denominator is nonzero. -/
theorem div_ne_zero {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    a / b ≠ 0 := by
  rw [ExplicitField.div_eq_mul_inv]
  exact ExplicitField.mul_ne_zero ha (ExplicitField.inv_ne_zero hb)

/-- Multiplying a quotient by its supplied nonzero denominator recovers the numerator. -/
theorem div_mul_cancel (a : K) {b : K} (hb : b ≠ 0) : a / b * b = a := by
  rw [ExplicitField.div_eq_mul_inv, mul_assoc,
    show b⁻¹ * b = b * b⁻¹ from mul_comm _ _,
    ExplicitField.mul_inv_cancel b hb, mul_one]

/-- Zero divided by any scalar is zero, including a zero denominator. -/
@[simp] theorem zero_div (b : K) : 0 / b = 0 := by
  rw [ExplicitField.div_eq_mul_inv, zero_mul]

attribute [local instance high] SubNegMonoid.toNeg in
/-- Negating the denominator negates the quotient.

The explicit inverse-negation law makes this identity valid without a nonzero-denominator hypothesis. -/
theorem div_neg (a b : K) : a / -b = -(a / b) := by
  letI : SubNegZeroMonoid K := Group.Negation.subNegZeroMonoid
  rw [ExplicitField.div_eq_mul_inv, ExplicitField.inv_neg,
    ExplicitField.div_eq_mul_inv]
  ring1

end ExplicitField

end Purelib.Algebra.Field

end

section
@[expose] public section

/-!
# Executable dense polynomials and finite Euclidean division

Mathlib's sparse `Polynomial` arithmetic is intended for specifications at the
representation level.  The FTA algorithms therefore use this separate dense
coefficient program.  Coefficients are stored highest-degree first; leading
zeros are removed by a finite `dropWhile` pass.
-/

namespace Purelib.Polynomial.Dense.Basic
namespace DensePolynomial

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K]

omit [DecidableEq K] in
open Purelib.Algebra.Field in
/-- A product of two supplied nonzero factors is nonzero. -/
theorem mul_ne_zero_direct {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := ExplicitField.mul_ne_zero ha hb

omit [DecidableEq K] in
open Purelib.Algebra.Field in
/-- A quotient with supplied nonzero numerator and denominator is nonzero. -/
theorem div_ne_zero_direct {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    a / b ≠ 0 := ExplicitField.div_ne_zero ha hb

end DensePolynomial

end Purelib.Polynomial.Dense.Basic

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11: median quadrance

The denominator-cleared identity already proved for right midpoints gives the
median formula directly.  The source's extra `Q₁ ≠ 0` hypothesis is not needed;
only characteristic two is excluded so that the displayed midpoint and `/4`
normalization have their intended meaning.
-/

namespace Purelib.Algebra

variable {K : Type*} [Field.ExplicitField K]

open Purelib.Algebra.Field in
/-- Cancel a supplied nonzero right factor from an equality of products.

The explicit field laws justify the cancellation without assuming the carrier is globally nontrivial. -/
public theorem Field.ExplicitField.eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

end Purelib.Algebra

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11: Menelaus and Ceva

The cyclic arguments are stated first as product identities retaining the
common spread factor.  The geometric nonparallel hypotheses supply explicit
nonzero certificates exactly where the printed conclusions cancel that factor.
-/

end

section
public section

/-!
# Divine Proportions, §2.6: pairs of quadratic equations

This file begins the numbered theorem sequence in *Divine Proportions*.  The
source's theorem has a genuine degenerate-case omission: when the two centres
are equal, its displayed polynomial condition merely says that the two
equations are identical; it does not prove that the common equation has a
solution in the field.  The exact arbitrary-field result is therefore split
into the distinct-centre theorem proved by the source's calculation and a
separate same-centre characterization.

Everything is parameterized by the project's explicit, choice-free field-law
interface.  The only characteristic assumption used below is the displayed
witness that `2` is nonzero.
-/

namespace Purelib.Algebra

variable {K : Type*} [Field.ExplicitField K]

/-- Distinct scalars have nonzero difference. -/
public theorem Field.ExplicitField.sub_ne_zero_of_ne {a b : K} (different : a ≠ b) : a - b ≠ 0
  := by
  intro differenceZero
  apply different
  calc
    a = (a - b) + b := by ring1
    _ = 0 + b := by rw [differenceZero]
    _ = b := zero_add b

end Purelib.Algebra

end

section
@[expose] public section

/-!
# Divine Proportions, Exercises 2.8–2.9

Both printed exercises omit genuine degenerate cases.  The determinant formula
in Exercise 2.8 is sufficient only when its displayed root denominator is
nonzero.  Exercise 2.9 uses `±2q` where the valid root-free condition is
`(p₁-p₂)²=4q`, and coincident equations still require `q` to be a square.
The corrected constructive statements and explicit rational counterexamples
are given below.
-/

namespace Purelib.Algebra

variable {K : Type*} [Field.ExplicitField K]

open Purelib.Algebra.Field in
/-- The square of a supplied nonzero scalar is nonzero. -/
public theorem Field.ExplicitField.square_nonzero_of_nonzero {value : K} (nonzero : value ≠ 0) :
    value ^ 2 ≠ 0 := by
  simpa only [pow_two] using ExplicitField.mul_ne_zero nonzero nonzero

end Purelib.Algebra

end

end

section
public section

/-!
# Bounded power sums in prime characteristic

All sums in this module range over the explicit natural residue labels
`0, ..., p-1`.  The proofs use finite differences, the project-owned finite
binomial expansion, and explicit field cancellation.  No carrier, primitive
root, or global enumeration is introduced.
-/

namespace Purelib.Algebra.Field.ExplicitField

variable {R : Type*} [Purelib.Algebra.Field.ExplicitField R]

open Purelib.Algebra.Field in
/-- A zero product with a supplied nonzero left factor has zero right factor. -/
public theorem eq_zero_of_mul_eq_zero_left
    {factor value : R} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have factorCancel : factor * factor⁻¹ = (1 : R) :=
    ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by rw [one_mul]
    _ = (factor * factor⁻¹) * value := by rw [factorCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

end Purelib.Algebra.Field.ExplicitField

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 23: physics applications

The calculus passages in the source are retained through their finite
polynomial stationarity equations.  Extremum conclusions are separated from
those equations, so no completed real line, limit, or general derivative
operator enters the formalization.
-/

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 26: Platonic solids

All five face-spread computations are recorded by one denominator-cleared
isosceles-triangle certificate.  Exercise 26.1 is proved directly from three
displayed edge vectors.  Exercise 26.4 uses a uniformly scaled standard
icosahedron, so its coordinates are polynomial in a supplied witness
`root²=5` and contain no selected irrational or completed field.
-/

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 25: resection and Hansen's problem

The large rational calculations are represented by common-denominator
integer certificates.  The general resection theorem is proved from the
denominator-free Four-point polynomial, so neither a root search nor a
completed coordinate field is used.
-/

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 24: surveying

Every construction is expressed by its finite quadrance/spread equations.
Decimal readings are retained as exact integer coefficient pairs, with
integer interval certificates for the source's numerical approximations.
-/

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

end

section
@[expose] public section

/-!
# Divine Proportions, Exercises 14.3 and 14.4

The source writes the two nonzero order-five spread values using a square
root `r²=5`.  Here `alpha` and `beta` are finite field expressions built from
an explicitly supplied root; no completed real or selected algebraic closure
is introduced.  Their root classification and logistic identities are proved
constructively.

`Figure` is the exact finite three-vertex window from Theorem 98, labelled as
`B,A,E` around the center `P`, together with the one radial spread used by
Exercise 14.4.  Its midpoint definitions are the points `M` and `F` in Figure
14.4.  The four quadrance displays follow from Polygon triangle and the
midpoint identities.  The printed decimals are retained as exact rational
millionth brackets with opposite quadratic signs.
-/

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7 field-fragment examples

The book's two complex examples need only one explicitly supplied element
`i` satisfying `i²=-1`.  Keeping that finite field fragment abstract makes the
same proofs usable in admissible finite fields and in the constructive
Gaussian rationals; no completed complex carrier is introduced.
-/

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11 exercises

This module begins the reader problems following the Two-struts theorem.  All
normalizations are retained as finite polynomial equalities.  In particular,
Example 11.1 is checked by scaling the two quad triples by the displayed
factor `256`; no quadratic formula or selected root is used.
-/

end

section
@[expose] public section
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Algebra.Field.ExplicitField

open Purelib.Algebra.Field in
/-- Dividing a product by its supplied nonzero right factor recovers the left factor. -/
theorem mul_div_cancel_right (value divisor : K)
    (divisorNonzero : divisor ≠ 0) :
    (value * divisor) / divisor = value := by
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    value * divisor * divisor⁻¹ =
        value * (divisor * divisor⁻¹) := by ring1
    _ = value := by
      rw [ExplicitField.mul_inv_cancel divisor divisorNonzero, _root_.mul_one]

end Purelib.Algebra.Field.ExplicitField

end

section
@[expose] public section

namespace Purelib.Algebra.Field.ExplicitField

open Purelib.Algebra.Field in
/-- Cancel a supplied nonzero left factor from an equality of products.

The explicit field laws justify the cancellation without assuming the carrier is globally nontrivial. -/
theorem eq_of_mul_eq_mul_left
    {K : Type*} [ExplicitField K]
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  apply ExplicitField.eq_of_mul_eq_mul_right factorNonzero
  rw [_root_.mul_comm left factor, _root_.mul_comm right factor]
  exact productsEqual

end Purelib.Algebra.Field.ExplicitField

end

section
open Purelib
open Purelib.Algebra.Field
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid
public section
namespace Purelib.Algebra.Field.ExplicitField

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Negating a nonzero scalar preserves nonzeroness. -/
public theorem neg_ne_zero_of_ne_zero {value :
  K} (nonzero : value ≠ 0) :
    -value ≠ 0 := by
  intro negativeZero
  apply nonzero
  calc
    value = -(-value) := by ring1
    _ = 0 := by rw [negativeZero]; ring1

/-- Division by one leaves every scalar unchanged.

The nontriviality assumption certifies that one is nonzero, enabling the explicit inverse law. -/
public theorem div_one [Nontrivial K] (value
  : K) :
    value / 1 = value := by
  have oneInverse : (1 : K)⁻¹ = 1 := by
    simpa only [one_mul] using
      ExplicitField.mul_inv_cancel (1 : K)
        (one_ne_zero : (1 : K) ≠ 0)
  rw [ExplicitField.div_eq_mul_inv, oneInverse, mul_one]

/-- A zero product with a supplied nonzero right factor has zero left factor. -/
public theorem
  eq_zero_of_mul_eq_zero_right
    {left right : K} (rightNonzero : right ≠ 0)
    (productZero : left * right = 0) : left = 0 := by
  apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left rightNonzero
  calc
    right * left = left * right := by ring1
    _ = 0 := productZero

/-- A product of three supplied nonzero factors is nonzero. -/
public theorem mul_three_ne_zero {a b c : K}
    (aNonzero : a ≠ 0) (bNonzero : b ≠ 0) (cNonzero : c ≠ 0) :
    a * b * c ≠ 0 :=
  ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero aNonzero bNonzero) cNonzero

/-- A product of four supplied nonzero factors is nonzero. -/
public theorem mul_four_ne_zero {a b c d : K}
    (aNonzero : a ≠ 0) (bNonzero : b ≠ 0) (cNonzero : c ≠ 0)
    (dNonzero : d ≠ 0) : a * b * c * d ≠ 0 :=
  ExplicitField.mul_ne_zero
    (Algebra.Field.ExplicitField.mul_three_ne_zero aNonzero bNonzero cNonzero) dNonzero

end Purelib.Algebra.Field.ExplicitField
end

end

public section

namespace Purelib.Algebra.Field.ExplicitField

/-- Total inversion sends zero to zero when two is nonzero.

The original inverse-negation law makes the inverse of zero its own negative.
Multiplying that equality by the nonzero scalar two forces it to vanish.
-/
theorem inverse_zero_of_two_ne_zero {K : Type*} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) :
    (0 : K)⁻¹ = 0 := by
  have negative := ExplicitField.inv_neg (0 : K)
  rw [show -(0 : K) = 0 by ring1] at negative
  have doubledZero : (2 : K) * (0 : K)⁻¹ = 0 := by
    calc
      (2 : K) * (0 : K)⁻¹ = (0 : K)⁻¹ + (0 : K)⁻¹ := by ring1
      _ = -((0 : K)⁻¹) + (0 : K)⁻¹ := congrArg (fun value => value + (0 : K)⁻¹) negative
      _ = 0 := by ring1
  exact ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero doubledZero

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A scalar different from one has nonzero complement. -/
public theorem one_sub_ne_zero_of_ne_one {value : K}
  (notOne : value ≠ 1) :
    1 - value ≠ 0 := by
  intro differenceZero
  apply notOne
  calc
    value = 1 - (1 - value) := by ring1
    _ = 1 := by rw [differenceZero]; ring1

end Purelib.Algebra.Field.ExplicitField
end
