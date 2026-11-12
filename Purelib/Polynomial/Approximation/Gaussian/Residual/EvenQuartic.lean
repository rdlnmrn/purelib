module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Dense.Gaussian.EvenQuartic
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Original-channel comparisons from computed even-quartic box gaps -/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Residual.EvenQuartic

open Purelib.Polynomial.Dense
open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Geometry.Rational (Box)

set_option genInjectivity false in
/-- Two actual original residuals with their retained local tails and computed divided-difference interval.

Both supplied input records remain stored with their identities. Their
original sample programs stay in the two displayed boxes after the same
finite floor; the gap is computed from those exact box endpoints.
-/
structure Attempt {a b : Rational} {firstChannel secondChannel : CoherentNamed}
    (originalFirst : Residual (Gaussian.EvenQuartic.polynomial a b) firstChannel)
    (originalSecond : Residual (Gaussian.EvenQuartic.polynomial a b) secondChannel) where
  /-- The actual retained first original residual program. -/
  first : Residual (Gaussian.EvenQuartic.polynomial a b) firstChannel
  /-- The retained first program is the original supplied record. -/
  first_eq : first = originalFirst
  /-- The actual retained second original residual program. -/
  second : Residual (Gaussian.EvenQuartic.polynomial a b) secondChannel
  /-- The retained second program is the original supplied record. -/
  second_eq : second = originalSecond
  /-- The original first tail's displayed local box. -/
  firstBox : Box
  /-- The original second tail's displayed local box. -/
  secondBox : Box
  /-- The finite stage after which both actual original tails obey these boxes. -/
  floor : Nat
  /-- Every later actual first sample remains in its same retained box. -/
  firstInside : ∀ index, floor ≤ index → firstBox.Contains (first.source.sample index)
  /-- Every later actual second sample remains in its same retained box. -/
  secondInside : ∀ index, floor ≤ index → secondBox.Contains (second.source.sample index)
  /-- The interval computed from those same original boxes is cached once. -/
  factorBounds : Purelib.Data.Rat.Interval.Bounds
  /-- The cached interval retains the same endpoint computation. -/
  factorBounds_eq : factorBounds = Gaussian.EvenQuartic.factorBounds a firstBox secondBox

constructive_injectivity Attempt

set_option genInjectivity false in
/-- The same finite original-tail attempt whose computed divided-difference gap is positive. -/
structure Certificate {a b : Rational} {firstChannel secondChannel : CoherentNamed}
    (first : Residual (Gaussian.EvenQuartic.polynomial a b) firstChannel)
    (second : Residual (Gaussian.EvenQuartic.polynomial a b) secondChannel)
    extends Attempt first second where
  /-- The computed lower endpoint positively separates the same divided-difference factor. -/
  positive : 0 < factorBounds.lower

constructive_injectivity Certificate

namespace Certificate

variable {a b : Rational} {firstChannel secondChannel : CoherentNamed}
variable {first : Residual (Gaussian.EvenQuartic.polynomial a b) firstChannel}
variable {second : Residual (Gaussian.EvenQuartic.polynomial a b) secondChannel}

/-- The same actual residual scales and retained box gap compute the comparison allowance. -/
@[expose] def scale (certificate : Certificate first second) : Rational :=
  (1 / certificate.factorBounds.lower ^ 2) * (2 * (certificate.first.scale + certificate.second.scale))

/-- The computed allowance is nonnegative on the same original residuals. -/
theorem scale_nonnegative (certificate : Certificate first second) : 0 ≤ certificate.scale :=
  Arithmetic.mul_nonneg_direct
    (Field.div_nonneg_direct (by decide) (Arithmetic.sq_nonneg_direct _))
    (Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.add_le_add_direct certificate.first.scale_nonnegative certificate.second.scale_nonnegative))

/-- Every same-index pair in the retained tails meets the allowance computed from its actual polynomial residuals. -/
theorem bound (certificate : Certificate first second) (index : Nat) (order : certificate.floor ≤ index) :
    normSq (certificate.first.source.sample index - certificate.second.source.sample index) ≤
      Basic.quarterRadius certificate.scale index := by
  have positive : 0 < (Gaussian.EvenQuartic.factorBounds a certificate.firstBox certificate.secondBox).lower := by
    rewrite [← certificate.factorBounds_eq]
    exact certificate.positive
  have separated := Gaussian.EvenQuartic.normSq_difference_le a b positive
    (certificate.firstInside index order) (certificate.secondInside index order)
  rewrite [← certificate.factorBounds_eq] at separated
  have residuals := Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_le_two
    ((Gaussian.EvenQuartic.polynomial a b).eval (certificate.first.source.sample index))
    ((Gaussian.EvenQuartic.polynomial a b).eval (certificate.second.source.sample index))
  have sourceBounds := Arithmetic.add_le_add_direct
    (certificate.first.bound index) (certificate.second.bound index)
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct sourceBounds (by decide : (0 : Rational) ≤ 2)
  have total := Arithmetic.mul_le_mul_of_nonneg_left_direct (residuals.trans paid)
    (Field.div_nonneg_direct (by decide : (0 : Rational) ≤ 1)
      (Arithmetic.sq_nonneg_direct certificate.factorBounds.lower))
  apply separated.trans (total.trans_eq _)
  unfold scale
  rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
  ring1

/-- Compare both original channels with independent starts and an allowance computed from their retained tails.

The first program's movement certificate pays the different-index movement.
The actual same-index polynomial bound pays the remaining original-program
difference, and geometric search computes a finite stage for each request.
-/
def equivalent (certificate : Certificate first second) : NamedEquivalent firstChannel.name secondChannel.name := by
  have direct : Equivalent certificate.first.source.toApproximation certificate.second.source.toApproximation := by
    refine ⟨?_⟩
    intro firstStart secondStart target positive
    let quarter := target / 4
    have quarterPositive := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    let movement := (Equivalent.refl certificate.first.source.toApproximation).compare
      firstStart secondStart quarter quarterPositive
    let start := Nat.max movement.rightIndex certificate.floor
    let index := Search.firstQuarterBelow certificate.scale start quarter
    have indexGe := Search.firstQuarterBelow_ge certificate.scale start quarter
    refine ⟨movement.leftIndex, index, movement.left_ge,
      movement.right_ge.trans ((Purelib.Data.Nat.Order.le_max_left _ _).trans indexGe), ?_⟩
    intro firstLater secondLater firstOrder secondOrder
    have originalSecondOrder := (Purelib.Data.Nat.Order.le_max_left _ _).trans (indexGe.trans secondOrder)
    have floorOrder := (Purelib.Data.Nat.Order.le_max_right _ _).trans (indexGe.trans secondOrder)
    have moved := movement.close firstOrder originalSecondOrder
    have differentPrograms := (certificate.bound secondLater floorOrder).trans_lt
      ((Basic.quarterRadius_antitone certificate.scale_nonnegative secondOrder).trans_lt
        (Search.firstQuarterBelow_accurate certificate.scale certificate.scale_nonnegative
          start quarter quarterPositive))
    have via := Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_le_via
      (certificate.first.source.sample firstLater) (certificate.first.source.sample secondLater)
      (certificate.second.source.sample secondLater)
    have sum := Arithmetic.add_lt_add_direct moved differentPrograms
    have paid := Arithmetic.mul_lt_mul_of_pos_left_direct (a := (2 : Rational)) (by decide) sum
    have total : 2 * (quarter + quarter) = target := by
      calc
        2 * (quarter + quarter) = quarter * 4 := by ring1
        _ = target := Purelib.Data.Rat.Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)
    rewrite [total] at paid
    exact via.trans_lt paid
  exact certificate.first.equivalent.trans (direct.toNamed.trans certificate.second.equivalent.symm)

end Certificate

set_option genInjectivity false in
/-- A computed local gap comparison or the unresolved sufficient test on its same actual original inputs. -/
inductive Outcome {a b : Rational} {firstChannel secondChannel : CoherentNamed}
    (first : Residual (Gaussian.EvenQuartic.polynomial a b) firstChannel)
    (second : Residual (Gaussian.EvenQuartic.polynomial a b) secondChannel) (firstBox secondBox : Box) where
  /-- The computed local interval positively separates the factor on both actual retained tails. -/
  | ready (certificate : Certificate first second)
      (firstBox_eq : certificate.firstBox = firstBox) (secondBox_eq : certificate.secondBox = secondBox)
  /-- The computed local interval's lower endpoint is nonpositive; no equality or collision is asserted. -/
  | unresolved (attempt : Attempt first second)
      (firstBox_eq : attempt.firstBox = firstBox) (secondBox_eq : attempt.secondBox = secondBox)
      (failed : ¬ 0 < attempt.factorBounds.lower)

constructive_injectivity Outcome

/-- Inspect the sufficient local comparison once on the two original residuals and their actual retained tails. -/
@[expose] def inspect {a b : Rational} {firstChannel secondChannel : CoherentNamed}
    (first : Residual (Gaussian.EvenQuartic.polynomial a b) firstChannel)
    (second : Residual (Gaussian.EvenQuartic.polynomial a b) secondChannel)
    (firstBox secondBox : Box) (floor : Nat)
    (firstInside : ∀ index, floor ≤ index → firstBox.Contains (first.source.sample index))
    (secondInside : ∀ index, floor ≤ index → secondBox.Contains (second.source.sample index)) :
    Outcome first second firstBox secondBox :=
  let factorBounds := Gaussian.EvenQuartic.factorBounds a firstBox secondBox
  let attempt : Attempt first second :=
    ⟨first, rfl, second, rfl, firstBox, secondBox, floor, firstInside, secondInside, factorBounds, rfl⟩
  if positive : 0 < attempt.factorBounds.lower then
    .ready ⟨attempt, positive⟩ rfl rfl
  else .unresolved attempt rfl rfl positive

end Purelib.Polynomial.Approximation.Gaussian.Residual.EvenQuartic

end
