module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Order.Multiplication
import Purelib.Measure.Weighted.EssentialMaximum
import Purelib.Measure.Content.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Transform
import Purelib.Data.List.Event
public import Purelib.Measure.Content.EssentialMaximum.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Content.Operations

section
/-!
# Essential maxima on explicit finite products

The computed essential maximum of a separable product factors exactly over
the Cartesian product of two displayed finite contents.  The proof follows
the executable atom-list construction, treating zero weights directly; no
supremum, maximizing choice, or product sigma algebra is used.
-/

@[expose] public section

namespace Purelib.Measure

open Purelib in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The essential maximum of one fixed left value times a mapped right row equals that left magnitude times the original
right essential maximum.

The row retains the original right weights and occurrences, mapping only
payloads to pairs. Pullback and scalar magnitude scaling concern that same row. -/
private theorem essentialMaximumMagnitudeOn_productRow {α β : Type}
    (leftItem : α) (leftValue : α → Fraction.Rational)
    (rightValue : β → Fraction.Rational) (right : List (Measure.Weighted β)) :
    essentialMaximumMagnitudeOn
        (fun pair => leftValue pair.1 * rightValue pair.2)
        (mapAtoms (fun rightItem => (leftItem, rightItem)) right) =
      Distance.rationalSeparation (leftValue leftItem) 0 *
        essentialMaximumMagnitudeOn rightValue right := by
  rw [essentialMaximumMagnitudeOn_mapAtoms]
  exact (⟨right⟩ : Measure.Content β).essentialMaximumMagnitude_scale
    (leftValue leftItem) rightValue

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Data.Rat.Fraction.Order in
/-- The essential maximum of a separated product observable over the exact product atoms factors into the two original
essential maxima.

The original left-major product consists of retained, scaled right rows.
Zero left weights remove precisely their rows; nonzero weights preserve their
maxima, and the scalar maximum distributes over the nonnegative right maximum. -/
private theorem essentialMaximumMagnitudeOn_productAtoms {α β : Type}
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    ∀ left : List (Measure.Weighted α), ∀ right : List (Measure.Weighted β),
    essentialMaximumMagnitudeOn
        (fun pair => leftValue pair.1 * rightValue pair.2)
        (productAtoms left right) =
      essentialMaximumMagnitudeOn leftValue left *
        essentialMaximumMagnitudeOn rightValue right
  | [], right => by
      change 0 = 0 * essentialMaximumMagnitudeOn rightValue right
      exact (zero_mul _).symm
  | atom :: remaining, right => by
      let rightMaximum := essentialMaximumMagnitudeOn rightValue right
      have rightMaximumNonnegative : 0 ≤ rightMaximum :=
        essentialMaximumMagnitudeOn_nonnegative rightValue right
      rw [productAtoms, Measure.essentialMaximumMagnitudeOn_append]
      by_cases atomZero : atom.weight = 0
      · rw [Measure.essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero _ atom.weight
          atom.nonnegative atomZero,
          essentialMaximumMagnitudeOn_productAtoms leftValue rightValue
            remaining right]
        rw [essentialMaximumMagnitudeOn, if_pos atomZero]
        exact Basic.max_eq_right
          (Arithmetic.mul_nonneg_direct
            (essentialMaximumMagnitudeOn_nonnegative leftValue remaining)
            rightMaximumNonnegative)
      · rw [Measure.essentialMaximumMagnitudeOn_scaleAtoms_of_ne _ atom.weight
          atom.nonnegative atomZero,
          essentialMaximumMagnitudeOn_productRow,
          essentialMaximumMagnitudeOn_productAtoms leftValue rightValue
            remaining right]
        rw [essentialMaximumMagnitudeOn, if_neg atomZero]
        exact Rat.max_mul_of_nonnegative_direct _ _ _
          rightMaximumNonnegative

namespace Content

open Purelib in
open Purelib.Data.Rat in
/-- A separated product observable's essential maximum under product content is the product of its original factor
essential maxima. -/
theorem product_essentialMaximumMagnitude_mul {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    (left.product right).essentialMaximumMagnitude
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.essentialMaximumMagnitude leftValue *
        right.essentialMaximumMagnitude rightValue :=
  essentialMaximumMagnitudeOn_productAtoms leftValue rightValue
    left.atoms right.atoms

end Content

end Purelib.Measure

end
