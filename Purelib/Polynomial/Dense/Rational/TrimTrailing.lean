module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Rational.Coefficients
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.List.Reverse
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Membership

/-!
# Retaining the nonzero endpoints of descending rational tables

The original reverse/take/drop scans remove only the displayed trailing zeros.
Their finite retained suffix, endpoint witnesses and evaluation factorization
refer to that same original coefficient table.
-/

namespace Purelib.Polynomial.Dense.Rational.TrimTrailing

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Algebra
open Purelib.Data.List

/-- A finite high-to-low coefficient list with all of its displayed trailing
zeros removed.

The original reversal moves the displayed trailing suffix to the prefix scan.
Reversing the exact retained scan result restores the original coefficient order. -/
@[expose] public def trimTrailing (coefficients : List Fraction.Rational) : List Fraction.Rational :=
  (coefficients.reverse.dropWhile (· = 0)).reverse

/-- The finite suffix removed by `trimTrailing`, retained explicitly for the
evaluation proof.

The original takeWhile scan retains the exact displayed zero suffix in reverse.
Reversal restores its original order and length for the evaluation factorization. -/
@[expose] public def trailingPart (coefficients : List Fraction.Rational) : List Fraction.Rational :=
  (coefficients.reverse.takeWhile (· = 0)).reverse

/-- The retained prefix and removed zero suffix concatenate to the original coefficient list.

The original two scans partition the same reversed coefficient table. Their
retained orders reconstruct exactly the original source after reversing. -/
public theorem trimTrailing_append_trailingPart (coefficients : List Fraction.Rational) :
    trimTrailing coefficients ++ trailingPart coefficients = coefficients := by
  unfold trimTrailing trailingPart
  rewrite [← Reverse.reverse_append,
    DropWhile.takeWhile_append_dropWhile,
    Reverse.reverse_reverse]
  exact Eq.refl _

/-- Every coefficient in a leading zero-prefix scan equals zero.

The original Boolean scan retains only selected head occurrences. Constructor
cases transport each actual retained occurrence to its exact zero equality. -/
private theorem mem_takeWhile_zero
    {value : Fraction.Rational} {coefficients : List Fraction.Rational}
    (member : value ∈ coefficients.takeWhile (· = 0)) : value = 0 := by
  induction coefficients with
  | nil => cases member
  | cons coefficient remaining inductionHypothesis =>
      cases selected : decide (coefficient = 0) with
      | false =>
          rewrite [List.takeWhile, selected] at member
          cases member
      | true =>
          rewrite [List.takeWhile, selected] at member
          cases member with
          | head => exact of_decide_eq_true selected
          | tail _ inTail => exact inductionHypothesis inTail

/-- A finite coefficient list whose entries all vanish is the zero list of its retained length.

The retained source length supplies the zero-block count. Each original head
equality transports one constructor while leaving the unchanged tail explicit. -/
private theorem eq_replicate_zero_of_all
    (coefficients : List Fraction.Rational)
    (allZero : ∀ value ∈ coefficients, value = 0) :
    coefficients = List.replicate coefficients.length 0 := by
  induction coefficients with
  | nil => rfl
  | cons value remaining inductionHypothesis =>
      have valueZero := allZero value List.mem_cons_self
      have remainingZero : ∀ member ∈ remaining, member = 0 := by
        intro member memberIn
        exact allZero member (List.mem_cons_of_mem value memberIn)
      rw [valueZero]
      change 0 :: remaining = 0 :: List.replicate remaining.length 0
      exact congrArg (List.cons (0 : Fraction.Rational))
        (inductionHypothesis remainingZero)

/-- The removed trailing suffix is exactly a zero block of its retained length.

The original reverse scan retains only zero occurrences. Their actual membership
witnesses account for every position in the retained removed suffix. -/
private theorem trailingPart_eq_replicate (coefficients : List Fraction.Rational) :
    trailingPart coefficients =
      List.replicate (trailingPart coefficients).length 0 := by
  have allZero : ∀ value ∈ trailingPart coefficients, value = 0 := by
    intro value member
    unfold trailingPart at member
    exact mem_takeWhile_zero
      ((Reverse.mem_reverse _).mp member)
  exact eq_replicate_zero_of_all (trailingPart coefficients) allZero

/-- Removing trailing zeros factors out the corresponding power of the evaluation point.

The exponent is the retained removed-suffix length, so the identity also covers all-zero and empty lists. -/
public theorem eval_trimTrailing_mul_power
    (point : Fraction.Rational) (coefficients : List Fraction.Rational) :
    Dense.Basic.DensePolynomial.evalCoeffs point coefficients =
      Dense.Basic.DensePolynomial.evalCoeffs point (trimTrailing coefficients) *
        point ^ (trailingPart coefficients).length := by
  let kept := trimTrailing coefficients
  let removed := trailingPart coefficients
  have decomposition : kept ++ removed = coefficients :=
    trimTrailing_append_trailingPart coefficients
  have removedZeros : removed = List.replicate removed.length 0 :=
    trailingPart_eq_replicate coefficients
  calc
    Dense.Basic.DensePolynomial.evalCoeffs point coefficients = Dense.Basic.DensePolynomial.evalCoeffs point (kept ++
      removed) := by
      rw [decomposition]
    _ = Dense.Basic.DensePolynomial.evalCoeffs point (kept ++ List.replicate removed.length 0) := by
      exact congrArg (Dense.Basic.DensePolynomial.evalCoeffs point)
        (congrArg (fun suffix => kept ++ suffix) removedZeros)
    _ = Dense.Basic.DensePolynomial.evalCoeffs point kept * point ^ removed.length :=
      Dense.Basic.DensePolynomial.evalCoeffs_append_replicate_zero point kept removed.length
    _ = _ := rfl

/-- A nonzero root remains a root after trailing zeros are removed.

The removed suffix supplies the same finite exponent as the factorization law.
Its nonzero point power cancels directly through the original field inverse. -/
public theorem eval_trimTrailing_eq_zero_of_nonzero_root
    (point : Fraction.Rational) (coefficients : List Fraction.Rational)
    (pointNonzero : point ≠ 0) (root : Dense.Basic.DensePolynomial.evalCoeffs point coefficients = 0) :
    Dense.Basic.DensePolynomial.evalCoeffs point (trimTrailing coefficients) = 0 := by
  rewrite [eval_trimTrailing_mul_power] at root
  let power := point ^ (trailingPart coefficients).length
  have powerNonzero : power ≠ 0 :=
    Fraction.Field.pow_ne_zero_direct point pointNonzero _
  calc
    Dense.Basic.DensePolynomial.evalCoeffs point
        (trimTrailing coefficients) =
        Dense.Basic.DensePolynomial.evalCoeffs point
          (trimTrailing coefficients) * (power * power⁻¹) := by
      rewrite [Field.ExplicitField.mul_inv_cancel power powerNonzero, mul_one]
      exact Eq.refl _
    _ = (Dense.Basic.DensePolynomial.evalCoeffs point
          (trimTrailing coefficients) * power) * power⁻¹ :=
      (mul_assoc _ _ _).symm
    _ = 0 := by
      rewrite [root, zero_mul]
      exact Eq.refl _

/-- A nonzero displayed leading coefficient is retained by trailing
trimming.

The original zero suffix cannot contain the nonzero leading coefficient.
The retained append equation identifies the unchanged leading constructor. -/
public theorem trimTrailing_cons_of_leading_nonzero
    (leading : Fraction.Rational) (remaining : List Fraction.Rational)
    (leadingNonzero : leading ≠ 0) :
    ∃ trimmedRemaining,
      trimTrailing (leading :: remaining) = leading :: trimmedRemaining := by
  have decomposition :=
    trimTrailing_append_trailingPart (leading :: remaining)
  have nonempty : trimTrailing (leading :: remaining) ≠ [] := by
    intro empty
    rw [empty, List.nil_append] at decomposition
    have leadingMember : leading ∈ trailingPart (leading :: remaining) := by
      rw [decomposition]
      exact List.mem_cons_self
    have trailingZeros := trailingPart_eq_replicate (leading :: remaining)
    rewrite [trailingZeros] at leadingMember
    exact leadingNonzero (Membership.eq_of_mem_replicate leadingMember)
  cases shape : trimTrailing (leading :: remaining) with
  | nil => exact (nonempty shape).elim
  | cons trimmedLeading trimmedRemaining =>
      rw [shape] at decomposition
      have leadingEqual : trimmedLeading = leading := by
        injection decomposition
      exact ⟨trimmedRemaining,
        congrArg (fun value => value :: trimmedRemaining) leadingEqual⟩

/-- Reverse induction derived directly from ordinary finite-list induction.

Ordinary structural induction on the original reversed source constructs
the retained final-entry step. A second reversal recovers the original source. -/
private theorem reverseRec {α : Type*} {motive : List α → Prop}
    (nilCase : motive [])
    (snocCase : ∀ list value, motive list → motive (list ++ [value]))
    (list : List α) : motive list := by
  have reversed : ∀ source : List α, motive source.reverse := by
    intro source
    induction source with
    | nil => exact nilCase
    | cons value remaining inductionHypothesis =>
        rewrite [Reverse.reverse_cons]
        exact snocCase remaining.reverse value inductionHypothesis
  have retained := reversed list.reverse
  rewrite [Reverse.reverse_reverse] at retained
  exact retained

/-- Every nonempty trailing-trim result ends in a nonzero coefficient.  The
proof is a direct reverse induction on the finite source list, avoiding the
choice-bearing generic `getLast` convenience route. -/
public theorem trimTrailing_constant_nonzero
    (coefficients : List Fraction.Rational) (leading : Fraction.Rational)
    (remaining : List Fraction.Rational)
    (shape : trimTrailing coefficients = leading :: remaining) :
    Dense.Rational.Coefficients.rationalConstantCoefficient (leading :: remaining) ≠ 0 := by
  apply reverseRec
    (motive := fun source => ∀ leading remaining,
      trimTrailing source = leading :: remaining →
        Dense.Rational.Coefficients.rationalConstantCoefficient (leading :: remaining) ≠ 0)
    (by
      intro leading remaining impossible
      change [] = leading :: remaining at impossible
      cases impossible)
    (by
      intro coefficients coefficient inductionHypothesis leading remaining shape
      have reversal : (coefficients ++ [coefficient]).reverse =
          coefficient :: coefficients.reverse :=
        Reverse.reverse_append coefficients [coefficient]
      cases selected : decide (coefficient = 0) with
      | true =>
          have retained : trimTrailing coefficients = leading :: remaining := by
            change (((coefficients ++ [coefficient]).reverse).dropWhile
              (fun value => decide (value = 0))).reverse = leading :: remaining at shape
            rewrite [reversal, DropWhile.cons_of_true
              (fun value => decide (value = 0)) coefficient coefficients.reverse selected] at shape
            exact shape
          exact inductionHypothesis leading remaining retained
      | false =>
          have unchanged : trimTrailing (coefficients ++ [coefficient]) =
              coefficients ++ [coefficient] := by
            unfold trimTrailing
            rewrite [reversal, DropWhile.cons_of_false
              (fun value => decide (value = 0)) coefficient coefficients.reverse selected,
              Reverse.reverse_cons, Reverse.reverse_reverse]
            exact Eq.refl _
          have coefficientNonzero : coefficient ≠ 0 := of_decide_eq_false selected
          intro constantZero
          have endpoint : coefficient =
              Dense.Rational.Coefficients.rationalConstantCoefficient (leading :: remaining) :=
            (Dense.Rational.Coefficients.rationalConstantCoefficient_append_singleton
              coefficients coefficient).symm.trans
                (congrArg Dense.Rational.Coefficients.rationalConstantCoefficient
                  (unchanged.symm.trans shape))
          exact coefficientNonzero (endpoint.trans constantZero))
    coefficients leading remaining shape

end Purelib.Polynomial.Dense.Rational.TrimTrailing
