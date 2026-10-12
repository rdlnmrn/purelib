module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction

section
public section

/-!
# Exchange of exact finite weighted integrals

Two retained occurrence lists supply nested rational weighted sums.
Finite additivity and scalar linearity exchange their order while retaining
the original occurrences, weights, and observations.
-/

namespace Purelib.Measure

open Distribution

open Purelib.Data.Rat in
/-- Exchange the two exact finite weighted summations of a rational observable on paired payloads.

Both ordered occurrence lists and their original weights remain fixed.
Finite additivity, scalar linearity, and transport of the original left
tail give equal nested integrals without rewriting beneath a binder. -/
theorem expectationWeight_exchange {α β : Type}
    (value : α → β → Fraction.Rational) :
    ∀ (left : List (Weighted α)) (right : List (Weighted β)),
      expectationWeight left (fun leftItem =>
        expectationWeight right (fun rightItem =>
          value leftItem rightItem)) =
      expectationWeight right (fun rightItem =>
        expectationWeight left (fun leftItem =>
          value leftItem rightItem))
  | [], right => by
      change 0 = expectationWeight right (fun _ => 0)
      exact ((weighted_constant right 0).trans
        (Fraction.Field.mul_zero_direct (totalWeight right))).symm
  | atom :: remaining, right => by
      change atom.weight * expectationWeight right (value atom.item) +
          expectationWeight remaining (fun leftItem =>
            expectationWeight right (value leftItem)) =
        expectationWeight right (fun rightItem =>
          atom.weight * value atom.item rightItem +
            expectationWeight remaining (fun leftItem => value leftItem rightItem))
      calc
        _ = atom.weight * expectationWeight right (value atom.item) +
            expectationWeight right (fun rightItem =>
              expectationWeight remaining (fun leftItem => value leftItem rightItem)) :=
          congrArg (fun tail => atom.weight *
            expectationWeight right (value atom.item) + tail)
              (expectationWeight_exchange value remaining right)
        _ = expectationWeight right (fun rightItem => atom.weight *
              value atom.item rightItem) +
            expectationWeight right (fun rightItem =>
              expectationWeight remaining (fun leftItem => value leftItem rightItem)) :=
          congrArg (fun scalar => scalar +
            expectationWeight right (fun rightItem =>
              expectationWeight remaining (fun leftItem => value leftItem rightItem)))
                (expectationWeight_scale right atom.weight (value atom.item)).symm
        _ = _ := (expectationWeight_add right
          (fun rightItem => atom.weight * value atom.item rightItem)
          (fun rightItem =>
            expectationWeight remaining (fun leftItem => value leftItem rightItem))).symm

end Purelib.Measure

end
