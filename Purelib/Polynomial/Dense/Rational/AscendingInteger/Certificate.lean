module
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.List.Append
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Reverse
import Purelib.Data.Nat.Subtraction
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Integer
import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
public import Purelib.Polynomial.Dense.Rational.IntegerCoefficients.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Mathlib.Data.List.Basic

/-!
# Certificates for retained ascending integer coefficient tables

Normalized rational conversion preserves the original integer witnesses and
canonical coefficient readback. Equality transports those same coefficients to
any supplied explicit field. The actual nonzero final integer entry retains its
original degree count through reversal, integer casts and leading-zero trimming.
-/

namespace Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate

open Purelib.Polynomial
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Data.Nat
open Purelib.Algebra.Field
open Purelib.Algebra.Ring
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

/-- Every rational in an embedded integer coefficient list has an explicit integer witness.

The original mapped occurrence supplies its retained integer source.
Structural membership cases either identify that head or preserve the unchanged tail. -/
private theorem integral_of_mem_castCoefficients
    (value : Fraction.Rational) : ∀ coefficients : List Int,
    value ∈ Dense.Rational.AscendingInteger.Basic.castCoefficients coefficients →
      Fraction.Integer.IsIntegralRational value
  | [], member => by cases member
  | coefficient :: remaining, member => by
      change value ∈ (coefficient : Fraction.Rational) ::
        Dense.Rational.AscendingInteger.Basic.castCoefficients remaining at member
      cases member with
      | head => exact ⟨coefficient, rfl⟩
      | tail _ remainingMember =>
          exact integral_of_mem_castCoefficients
            value remaining remainingMember

/-- Every coefficient retained by conversion from an ascending integer list is an integer-valued rational.

The original normalized coefficient occurrence belonged to the retained cast
list, whose source entry supplies the same explicit integer witness. -/
public theorem ofAscending_coefficient_integral (coefficients : List Int)
    {value : Fraction.Rational}
    (member : value ∈ (Dense.Rational.AscendingInteger.Basic.ofAscending coefficients).coeffs) :
    Fraction.Integer.IsIntegralRational value := by
  unfold Dense.Rational.AscendingInteger.Basic.ofAscending at member
  rw [Dense.Basic.DensePolynomial.normalize_coeffs] at member
  have rawMember : value ∈
      Dense.Rational.AscendingInteger.Basic.castCoefficients coefficients.reverse :=
    DropWhile.mem_of_mem _ member
  exact integral_of_mem_castCoefficients value coefficients.reverse rawMember

/-- An integer polynomial certificate supplies integrality of every normalized retained coefficient.

The retained integer-polynomial certificate identifies the normalized table
with its original ascending integer conversion, preserving its coefficient witness. -/
public theorem integral_coefficient {polynomial : Basic.Integer.CoefficientPolynomial}
    (integral : Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial polynomial) {value : Fraction.Rational}
    (member : value ∈ polynomial.normalize.coeffs) :
    Fraction.Integer.IsIntegralRational value := by
  rcases integral with ⟨coefficients, certificate⟩
  rw [certificate] at member
  exact ofAscending_coefficient_integral coefficients member

/-- Canonical executable integer coefficients extracted from a normalized
finite dense rational polynomial.

The original normalized rational table is reversed before its retained canonical
numerators are extracted in ascending order. -/
@[expose] public def integerCoefficients (polynomial : Basic.Integer.CoefficientPolynomial) : List Int :=
  polynomial.normalize.coeffs.reverse.map fun coefficient =>
    (Fraction.Basic.representative coefficient).num

/-- Re-embedding canonical numerators reconstructs a finite list of integer-valued rational coefficients.

Each integral rational is the cast of its canonical representative numerator.
Structural recursion preserves the original head and every retained tail occurrence. -/
private theorem cast_representative_coefficients : ∀ values : List Fraction.Rational,
    (∀ value ∈ values, Fraction.Integer.IsIntegralRational value) →
    Dense.Rational.AscendingInteger.Basic.castCoefficients
        (values.map fun value =>
          (Fraction.Basic.representative value).num) = values
  | [], allIntegral => rfl
  | value :: remaining, allIntegral => by
      unfold Dense.Rational.AscendingInteger.Basic.castCoefficients
      simp only [List.map_cons]
      apply congrArg₂ List.cons
      · exact (Fraction.Integer.integral_eq_cast_representative_num
          (allIntegral value List.mem_cons_self)).symm
      · change Dense.Rational.AscendingInteger.Basic.castCoefficients
            (remaining.map fun entry =>
              (Fraction.Basic.representative entry).num) = remaining
        exact cast_representative_coefficients remaining
          (fun entry member => allIntegral entry
            (List.mem_cons_of_mem value member))

/-- The extracted canonical ascending integer table reconstructs the normalized polynomial.

An integer polynomial certificate ensures each retained rational equals the embedding of its canonical numerator. -/
public theorem ofAscending_integerCoefficients_eq_normalize
    (polynomial : Basic.Integer.CoefficientPolynomial) (integral :
      Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial polynomial) :
    Dense.Rational.AscendingInteger.Basic.ofAscending (integerCoefficients polynomial) =
      polynomial.normalize := by
  have reversed : (integerCoefficients polynomial).reverse =
      polynomial.normalize.coeffs.map fun coefficient =>
        (Fraction.Basic.representative coefficient).num := by
    unfold integerCoefficients
    rw [← Reverse.map_reverse, Reverse.reverse_reverse]
  unfold Dense.Rational.AscendingInteger.Basic.ofAscending
  rw [reversed]
  rw [cast_representative_coefficients polynomial.normalize.coeffs
    (fun value member => integral_coefficient integral member)]
  exact Dense.Basic.DensePolynomial.normalize_normalize polynomial

/-- Embedding integer coefficients commutes with removal of leading zeros.

The original integer-zero test selects the same retained branch as its rational
cast. Injectivity preserves every nonzero head and its unchanged tail. -/
public theorem castCoefficients_dropWhile_zero : ∀ values : List Int,
    Dense.Rational.AscendingInteger.Basic.castCoefficients (values.dropWhile (fun value => value = 0)) =
      (Dense.Rational.AscendingInteger.Basic.castCoefficients values).dropWhile
        (fun value => value = 0)
  | [] => rfl
  | value :: remaining => by
      by_cases valueZero : value = 0
      · subst value
        rw [DropWhile.cons_of_true (fun value : Int => decide (value = 0))
          0 remaining (decide_eq_true (Eq.refl (0 : Int)))]
        unfold Dense.Rational.AscendingInteger.Basic.castCoefficients
        rw [List.map_cons, IntCast.cast_zero,
          DropWhile.cons_of_true (fun value : Fraction.Rational => decide (value = 0))
            0 _ (decide_eq_true (Eq.refl (0 : Fraction.Rational)))]
        exact castCoefficients_dropWhile_zero remaining
      · have castNonzero : (value : Fraction.Rational) ≠ 0 := by
          intro castZero
          exact valueZero (Fraction.Cast.Compatibility.intCast_injective_direct castZero)
        rewrite [DropWhile.cons_of_false (fun value : Int => decide (value = 0))
          value remaining (decide_eq_false valueZero)]
        unfold Dense.Rational.AscendingInteger.Basic.castCoefficients
        rewrite [List.map_cons,
          DropWhile.cons_of_false (fun value : Fraction.Rational => decide (value = 0))
            (value : Fraction.Rational) _ (decide_eq_false castNonzero)]
        exact Eq.refl _

/-- Embedding finite integer coefficient lists into constructive rationals is injective. -/
private theorem castCoefficients_injective : ∀ {left right : List Int},
    Dense.Rational.AscendingInteger.Basic.castCoefficients left =
      Dense.Rational.AscendingInteger.Basic.castCoefficients right → left = right
  | [], [], equal => rfl
  | [], _ :: _, equal => by
      unfold Dense.Rational.AscendingInteger.Basic.castCoefficients at equal
      simp only [List.map_nil, List.map_cons] at equal
      exact (List.cons_ne_nil _ _ equal.symm).elim
  | _ :: _, [], equal => by
      unfold Dense.Rational.AscendingInteger.Basic.castCoefficients at equal
      simp only [List.map_nil, List.map_cons] at equal
      exact (List.cons_ne_nil _ _ equal).elim
  | left :: lefts, right :: rights, equal => by
      unfold Dense.Rational.AscendingInteger.Basic.castCoefficients at equal
      simp only [List.map_cons] at equal
      have heads : left = right :=
        Fraction.Cast.Compatibility.intCast_injective_direct
          (List.cons.inj equal).1
      have tails : lefts = rights := castCoefficients_injective
        (List.cons.inj equal).2
      rw [heads, tails]

/-- Dropping leading integer zeros before casting preserves descending evaluation in an explicit field.

Each retained integer zero casts to the original field zero. Scalar zero-prefix
evaluation removes those same displayed heads before the unchanged tail is scanned. -/
private theorem evalCoeffs_map_dropWhile_int_zero
    {K : Type*} [ExplicitField K] (point : K) : ∀ values : List Int,
    Dense.Basic.DensePolynomial.evalCoeffs point
        ((values.dropWhile fun value => value = 0).map
          fun value : Int => (value : K)) =
      Dense.Basic.DensePolynomial.evalCoeffs point
        (values.map fun value : Int => (value : K))
  | [] => rfl
  | value :: remaining => by
      by_cases valueZero : value = 0
      · subst value
        rw [DropWhile.cons_of_true (fun value : Int => decide (value = 0))
          0 remaining (decide_eq_true (Eq.refl (0 : Int))), List.map_cons,
          IntCast.cast_zero]
        rw [Dense.Basic.DensePolynomial.evalCoeffs_cons_zero]
        exact evalCoeffs_map_dropWhile_int_zero point remaining
      · rw [DropWhile.cons_of_false (fun value : Int => decide (value = 0))
          value remaining (decide_eq_false valueZero)]

/-- Equality of canonical rational embeddings of two integer polynomials is
a coefficient identity, hence their evaluations agree in every explicitly
supplied field, including finite characteristic.

Coefficient readback identifies the original normalized rational tables.
Injective integer casts recover their retained zero-trimmed integer entries. -/
public theorem normalized_reverse_eq_of_ofAscending_eq
    {left right : List Int}
    (equal : Dense.Rational.AscendingInteger.Basic.ofAscending left =
      Dense.Rational.AscendingInteger.Basic.ofAscending right) :
    left.reverse.dropWhile (fun value => value = 0) =
      right.reverse.dropWhile (fun value => value = 0) := by
  have coefficientEquality := congrArg
    Dense.Basic.DensePolynomial.coeffs equal
  unfold Dense.Rational.AscendingInteger.Basic.ofAscending at coefficientEquality
  simp only [Dense.Basic.DensePolynomial.normalize_coeffs] at coefficientEquality
  rw [← castCoefficients_dropWhile_zero,
    ← castCoefficients_dropWhile_zero] at coefficientEquality
  exact castCoefficients_injective coefficientEquality

/-- Equal rational dense conversions of integer tables have equal evaluations in every explicit field.

The rational equality identifies normalized integer coefficients, so the conclusion also holds in finite characteristic.
-/
public theorem eval_eq_of_ofAscending_eq
    {left right : List Int}
    (equal : Dense.Rational.AscendingInteger.Basic.ofAscending left =
      Dense.Rational.AscendingInteger.Basic.ofAscending right)
    {K : Type*} [ExplicitField K] (point : K) :
    Ascending.Integer.Basic.eval left point =
      Ascending.Integer.Basic.eval right point := by
  have integerEquality :
      left.reverse.dropWhile (fun value => value = 0) =
        right.reverse.dropWhile (fun value => value = 0) :=
    normalized_reverse_eq_of_ofAscending_eq equal
  calc
    Ascending.Integer.Basic.eval left point =
        Dense.Basic.DensePolynomial.evalCoeffs point
          (left.reverse.map fun value : Int => (value : K)) :=
      (Dense.Basic.DensePolynomial.evalCoeffs_reverse_intCast left point).symm
    _ = Dense.Basic.DensePolynomial.evalCoeffs point
          ((left.reverse.dropWhile fun value => value = 0).map
            fun value : Int => (value : K)) :=
      (evalCoeffs_map_dropWhile_int_zero point left.reverse).symm
    _ = Dense.Basic.DensePolynomial.evalCoeffs point
          ((right.reverse.dropWhile fun value => value = 0).map
            fun value : Int => (value : K)) := by rw [integerEquality]
    _ = Dense.Basic.DensePolynomial.evalCoeffs point
          (right.reverse.map fun value : Int => (value : K)) :=
      evalCoeffs_map_dropWhile_int_zero point right.reverse
    _ = Ascending.Integer.Basic.eval right point :=
      Dense.Basic.DensePolynomial.evalCoeffs_reverse_intCast right point

/-- A displayed nonzero final ascending coefficient prevents normalization
from removing any slot.

The original last-entry observation identifies the first reversed coefficient.
Its nonzero cast prevents zero-prefix trimming from removing any original slot. -/
public theorem ofAscending_degreeCount_of_getLast
    {coefficients : List Int} {leading : Int}
    (last : coefficients.getLast? = some leading)
    (leadingNonzero : leading ≠ 0) :
    (Dense.Rational.AscendingInteger.Basic.ofAscending coefficients).degreeCount =
      coefficients.length := by
  have reversed : coefficients.reverse = leading :: coefficients.dropLast.reverse :=
    Reverse.reverse_eq_getLast_cons_dropLast coefficients last
  have castNonzero : (leading : Fraction.Rational) ≠ 0 := by
    intro castZero
    exact leadingNonzero
      (Fraction.Cast.Compatibility.intCast_injective_direct castZero)
  unfold Dense.Rational.AscendingInteger.Basic.ofAscending Dense.Basic.DensePolynomial.degreeCount
  rw [Dense.Basic.DensePolynomial.normalize_normalize]
  change
    ((Dense.Rational.AscendingInteger.Basic.castCoefficients coefficients.reverse).dropWhile
        (fun value => value = 0)).length = coefficients.length
  rewrite [reversed]
  unfold Dense.Rational.AscendingInteger.Basic.castCoefficients
  rewrite [List.map_cons,
    DropWhile.cons_of_false (fun value : Fraction.Rational => decide (value = 0))
      (leading : Fraction.Rational) _ (decide_eq_false castNonzero),
    List.length_cons, Map.length_map, Reverse.length_reverse]
  exact Reverse.length_dropLast_of_getLast coefficients last

/-- Exact natural degree from an ascending slot count and a nonzero final
coefficient.

The retained slot count is one successor of the displayed degree. The original
nonzero last coefficient makes normalization retain exactly those same slots. -/
public theorem ofAscending_natDegree_of_getLast
    {coefficients : List Int} {degree : Nat} {leading : Int}
    (length : coefficients.length = degree + 1)
    (last : coefficients.getLast? = some leading)
    (leadingNonzero : leading ≠ 0) :
    (Dense.Rational.AscendingInteger.Basic.ofAscending coefficients).natDegree = degree := by
  unfold Dense.Basic.DensePolynomial.natDegree
  rw [ofAscending_degreeCount_of_getLast last leadingNonzero, length]
  exact Subtraction.add_sub_cancel_right degree 1

/-- The same finite shape certificate proves that the represented polynomial
is nonzero.

The original nonzero final entry supplies a nonempty coefficient table. Its
retained slot count excludes an empty normalized rational representation. -/
public theorem ofAscending_isZero_false_of_getLast
    {coefficients : List Int} {leading : Int}
    (last : coefficients.getLast? = some leading)
    (leadingNonzero : leading ≠ 0) :
    (Dense.Rational.AscendingInteger.Basic.ofAscending coefficients).isZero = false := by
  cases zeroTest : (Dense.Rational.AscendingInteger.Basic.ofAscending coefficients).isZero with
  | false => rfl
  | true =>
      have countZero := Dense.Basic.DensePolynomial.degreeCount_eq_zero_of_isZero zeroTest
      rw [ofAscending_degreeCount_of_getLast last leadingNonzero] at countZero
      cases coefficients with
      | nil => cases last
      | cons coefficient remaining => cases countZero

/-- The leading coefficient of a converted ascending integer table is an integer-valued rational.

The normalized head either is the original rational zero or has a retained
source occurrence in the cast integer table, supplying its exact integer witness. -/
public theorem ofAscending_leadingCoeff_integral (coefficients : List Int) :
    Fraction.Integer.IsIntegralRational
      (Dense.Rational.AscendingInteger.Basic.ofAscending coefficients).leadingCoeff := by
  unfold Dense.Basic.DensePolynomial.leadingCoeff Dense.Rational.AscendingInteger.Basic.ofAscending
  rw [Dense.Basic.DensePolynomial.normalize_normalize]
  change Fraction.Integer.IsIntegralRational
    (((Dense.Rational.AscendingInteger.Basic.castCoefficients coefficients.reverse).dropWhile
      (fun value => value = 0)).headD 0)
  cases trimmedEquation :
      (Dense.Rational.AscendingInteger.Basic.castCoefficients coefficients.reverse).dropWhile
        (fun value => value = 0) with
  | nil => exact ⟨0, rfl⟩
  | cons leading remaining =>
      have leadingMember : leading ∈
          (Dense.Rational.AscendingInteger.Basic.castCoefficients coefficients.reverse).dropWhile
            (fun value => value = 0) := by
        rw [trimmedEquation]
        exact List.mem_cons_self
      have rawMember : leading ∈
          Dense.Rational.AscendingInteger.Basic.castCoefficients coefficients.reverse :=
        DropWhile.mem_of_mem _ leadingMember
      exact integral_of_mem_castCoefficients
        leading coefficients.reverse rawMember
end Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate

section

namespace Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate
/-- The endpoint polynomial with ascending coefficients `[0, 1]` has natural degree one. -/
public theorem
  endpointPolynomial_natDegree
  :
    (Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic.ofAscending
      [0, 1]).natDegree = 1 :=
  Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.ofAscending_natDegree_of_getLast
    (coefficients := [0, 1]) (degree := 1) (leading := 1)
    (by decide) (by decide) (by decide)

/-- The endpoint polynomial with ascending coefficients `[0, 1]` is nonzero. -/
public theorem
  endpointPolynomial_nonzero
  :
    (Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic.ofAscending
      [0, 1]).isZero = false :=
  Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.ofAscending_isZero_false_of_getLast
    (coefficients := [0, 1]) (leading := 1) (by decide) (by decide)

/-- The constant-one polynomial has natural degree zero. -/
public theorem
  constantOnePolynomial_natDegree
  :
    (Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic.ofAscending
      [1]).natDegree = 0 :=
  Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.ofAscending_natDegree_of_getLast
    (coefficients := [1]) (degree := 0) (leading := 1)
    (by decide) (by decide) (by decide)

/-- The constant-one polynomial is nonzero. -/
public theorem
  constantOnePolynomial_nonzero
  :
    (Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic.ofAscending
      [1]).isZero = false :=
  Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate.ofAscending_isZero_false_of_getLast
    (coefficients := [1]) (leading := 1) (by decide) (by decide)
end Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate
end
