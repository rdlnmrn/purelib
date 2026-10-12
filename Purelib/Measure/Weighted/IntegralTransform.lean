module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Operations
public import Purelib.Measure.Weighted.Transform
import Purelib.Data.Rat.Fraction.Arithmetic

section
public section

/-!
# Exact integration against finite contents

A finite-content integral is an exact rational weighted sum.  The usual
linearity, monotonicity, indicator, restriction, and pushforward identities
are all finite list calculations.
-/

namespace Purelib.Measure

open Purelib.Data.Rat
/-- Integration after mapping payloads equals the original integral of the pulled-back observable.

The mapped head retains the original weight and reads the supplied
function at that payload. Scalar tail transport identifies the same
ordered integral without rewriting the observable beneath a binder. -/
theorem expectationWeight_mapAtoms {α β : Type}
    (function : α → β) (value : β → Fraction.Rational) :
    ∀ atoms : List (Weighted α),
      Distribution.expectationWeight (mapAtoms function atoms) value =
        Distribution.expectationWeight atoms
          (fun item => value (function item))
  | [] => rfl
  | atom :: remaining => congrArg
      (fun tail => atom.weight * value (function atom.item) + tail)
        (expectationWeight_mapAtoms function value remaining)

/-- Integration after restriction equals the original integral of the event indicator times the observable.

The original Boolean head test either retains the exact head or skips it.
Its scalar indicator contribution and the certificate on the unchanged
restricted tail identify both integrals directly. -/
theorem expectationWeight_restrictAtoms {α : Type}
    (condition : α → Bool) (value : α → Fraction.Rational) :
    ∀ atoms : List (Weighted α),
      Distribution.expectationWeight (restrictAtoms atoms condition) value =
        Distribution.expectationWeight atoms
          (fun item => Distribution.indicator condition item * value item)
  | [] => rfl
  | atom :: remaining => by
      change Distribution.expectationWeight
          (if condition atom.item then atom :: restrictAtoms remaining condition
            else restrictAtoms remaining condition) value =
        atom.weight * ((match condition atom.item with | true => 1 | false => 0) *
          value atom.item) + Distribution.expectationWeight remaining
            (fun item => Distribution.indicator condition item * value item)
      cases condition atom.item with
      | false =>
          have head : atom.weight * ((0 : Fraction.Rational) * value atom.item) = 0 :=
            (congrArg (fun scalar => atom.weight * scalar)
              (Fraction.Field.zero_mul_direct (value atom.item))).trans
                (Fraction.Field.mul_zero_direct atom.weight)
          exact (expectationWeight_restrictAtoms condition value remaining).trans
            ((Fraction.Field.zero_add _).symm.trans
              (congrArg (fun scalar => scalar +
                Distribution.expectationWeight remaining
                  (fun item => Distribution.indicator condition item * value item))
                    head.symm))
      | true =>
          change atom.weight * value atom.item +
              Distribution.expectationWeight (restrictAtoms remaining condition) value =
            atom.weight * (1 * value atom.item) +
              Distribution.expectationWeight remaining
                (fun item => Distribution.indicator condition item * value item)
          exact (congrArg (fun tail => atom.weight * value atom.item + tail)
            (expectationWeight_restrictAtoms condition value remaining)).trans
              (congrArg (fun scalar => atom.weight * scalar +
                Distribution.expectationWeight remaining
                  (fun item => Distribution.indicator condition item * value item))
                    (Fraction.Field.one_mul (value atom.item)).symm)

/-- A product of separate observables integrates over the exact occurrence product as the product of the two integrals.

Each original left occurrence contributes its exact scaled right row.
Append, map, and scale certificates retain those rows, while scalar
linearity and distributivity identify the two original marginal integrals. -/
theorem expectationWeight_productAtoms_mul {α β : Type}
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    ∀ (left : List (Weighted α)) (right : List (Weighted β)),
      Distribution.expectationWeight (productAtoms left right)
          (fun pair => leftValue pair.1 * rightValue pair.2) =
        Distribution.expectationWeight left leftValue *
          Distribution.expectationWeight right rightValue
  | [], right => (Fraction.Field.zero_mul_direct _).symm
  | atom :: remaining, right => by
      rw [productAtoms, expectationWeight_append,
        expectationWeight_scaleAtoms, expectationWeight_mapAtoms,
        expectationWeight_productAtoms_mul leftValue rightValue remaining right]
      change atom.weight *
            Distribution.expectationWeight right
              (fun item => leftValue atom.item * rightValue item) +
          Distribution.expectationWeight remaining leftValue *
            Distribution.expectationWeight right rightValue =
        (atom.weight * leftValue atom.item +
            Distribution.expectationWeight remaining leftValue) *
          Distribution.expectationWeight right rightValue
      calc
        _ = atom.weight * (leftValue atom.item *
              Distribution.expectationWeight right rightValue) +
            Distribution.expectationWeight remaining leftValue *
              Distribution.expectationWeight right rightValue :=
          congrArg (fun scalar => atom.weight * scalar +
            Distribution.expectationWeight remaining leftValue *
              Distribution.expectationWeight right rightValue)
                (Distribution.expectationWeight_scale right (leftValue atom.item) rightValue)
        _ = _ := by ring1

/-- Integration over the exact occurrence product equals its left-then-right nested finite weighted integral.

The original product list concatenates one scaled mapped right row for
each retained left occurrence. The corresponding append, scale, and map
certificates and scalar tail transport recover those exact nested sums. -/
theorem expectationWeight_productAtoms {α β : Type}
    (value : α × β → Fraction.Rational) :
    ∀ (left : List (Weighted α)) (right : List (Weighted β)),
      Distribution.expectationWeight (productAtoms left right) value =
        Distribution.expectationWeight left (fun leftItem =>
          Distribution.expectationWeight right (fun rightItem =>
            value (leftItem, rightItem)))
  | [], right => rfl
  | atom :: remaining, right => by
      change Distribution.expectationWeight
          (scaleAtoms atom.weight atom.nonnegative
              (mapAtoms (fun rightItem => (atom.item, rightItem)) right) ++
            productAtoms remaining right) value =
        atom.weight * Distribution.expectationWeight right
            (fun rightItem => value (atom.item, rightItem)) +
          Distribution.expectationWeight remaining (fun leftItem =>
            Distribution.expectationWeight right (fun rightItem =>
              value (leftItem, rightItem)))
      have row := (expectationWeight_scaleAtoms atom.weight atom.nonnegative
        (mapAtoms (fun rightItem => (atom.item, rightItem)) right) value).trans
          (congrArg (fun scalar => atom.weight * scalar)
            (expectationWeight_mapAtoms (fun rightItem => (atom.item, rightItem)) value right))
      exact (expectationWeight_append _ _ value).trans
        ((congrArg (fun scalar => scalar +
          Distribution.expectationWeight (productAtoms remaining right) value) row).trans
            (congrArg (fun tail => atom.weight *
              Distribution.expectationWeight right
                (fun rightItem => value (atom.item, rightItem)) + tail)
                  (expectationWeight_productAtoms value remaining right)))

end Purelib.Measure

end
