module
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Stability
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

public section

/-!
# Finite rational Jensen certificates

A supporting line supplied at the exact rational mean proves Jensen's
inequality by finite linearity.  Convex functions on a completed carrier are
not introduced: the caller gives the finitely checkable support inequalities
needed on the displayed atoms.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- A supporting affine line at the exact mean bounds the transform of that mean by the transformed expectation.

The supporting inequality is required on each original retained occurrence, with the same supplied slope and observable;
linearity cancels the centered affine term. -/
theorem jensen_of_supportingLine {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational)
    (transform : Fraction.Rational → Fraction.Rational) (slope : Fraction.Rational)
    (supports : ∀ atom, atom ∈ distribution.atoms →
      transform (distribution.expectation value) +
          slope * (value atom.item - distribution.expectation value) ≤
        transform (value atom.item)) :
    transform (distribution.expectation value) ≤
      distribution.expectation (fun item => transform (value item)) := by
  calc
    transform (distribution.expectation value) =
        distribution.expectation (fun item =>
          transform (distribution.expectation value) +
            slope * (value item - distribution.expectation value)) := by
      rw [distribution.expectation_add, distribution.expectation_scale,
        distribution.expectation_sub, distribution.expectation_constant,
        distribution.expectation_constant]
      ring1
    _ ≤ distribution.expectation (fun item => transform (value item)) := by
      apply distribution.expectation_mono
      intro atom member
      exact supports atom member

/-- The square of the exact expectation is bounded by the expectation of the squared observable. -/
theorem jensen_square {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) :
    distribution.expectation value ^ 2 ≤
      distribution.expectation (fun item => value item ^ 2) := by
  apply distribution.jensen_of_supportingLine value (fun item => item ^ 2)
    (2 * distribution.expectation value)
  intro atom member
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (value atom.item - distribution.expectation value) ^ 2 :=
      Fraction.Order.Arithmetic.sq_nonneg_direct _
    _ = value atom.item ^ 2 -
        (distribution.expectation value ^ 2 +
          2 * distribution.expectation value *
            (value atom.item - distribution.expectation value)) := by
      ring1

/-- The magnitude of the exact expectation is bounded by the expectation of the observable's magnitude. -/
theorem jensen_rationalSeparation_zero {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    Distance.rationalSeparation (distribution.expectation value) 0 ≤
      distribution.expectation (fun item =>
        Distance.rationalSeparation (value item) 0) := by
  by_cases meanNonnegative : 0 ≤ distribution.expectation value
  · apply distribution.jensen_of_supportingLine value
      (fun item => Distance.rationalSeparation item 0) 1
    intro atom member
    rw [Distance.rationalSeparation_zero_of_nonneg meanNonnegative]
    calc
      distribution.expectation value +
            1 * (value atom.item - distribution.expectation value) =
          value atom.item := by
        ring1
      _ ≤ Distance.rationalSeparation (value atom.item) 0 :=
        by
          unfold Distance.rationalSeparation
          have leftRestore : value atom.item - 0 = value atom.item := by ring1
          have rightRestore : 0 - value atom.item = -value atom.item := by ring1
          rw [leftRestore, rightRestore]
          exact Fraction.Order.Basic.le_max_left _ _
  · have meanNonpositive : distribution.expectation value ≤ 0 :=
      (Fraction.Order.Arithmetic.lt_of_not_ge_direct meanNonnegative).le
    apply distribution.jensen_of_supportingLine value
      (fun item => Distance.rationalSeparation item 0) (-1)
    intro atom member
    rw [Distance.rationalSeparation_zero_of_nonpos meanNonpositive]
    calc
      -distribution.expectation value +
            -1 * (value atom.item - distribution.expectation value) =
          -value atom.item := by
        ring1
      _ ≤ Distance.rationalSeparation (value atom.item) 0 :=
        by
          unfold Distance.rationalSeparation
          have leftRestore : value atom.item - 0 = value atom.item := by ring1
          have rightRestore : 0 - value atom.item = -value atom.item := by ring1
          rw [leftRestore, rightRestore]
          exact Fraction.Order.Basic.le_max_right _ _

end Distribution

end Purelib.Measure
