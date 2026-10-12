module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Kernel.EssentialMaximum
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Distribution.Pushforward.EssentialMaximum
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Tactic.Ring

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

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- A separated product observable has essential maximum equal to the product of its two original marginal essential
maxima. -/
theorem product_essentialMaximumMagnitude_mul {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    (left.product right).essentialMaximumMagnitude
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.essentialMaximumMagnitude leftValue *
        right.essentialMaximumMagnitude rightValue := by
  unfold Distribution.product
  rw [left.bind_essentialMaximumMagnitude]
  let rightMaximum := right.essentialMaximumMagnitude rightValue
  have rightMaximumNonnegative : 0 ≤ rightMaximum :=
    right.essentialMaximumMagnitude_nonnegative rightValue
  calc
    left.essentialMaximumMagnitude (fun leftItem =>
          (right.map fun rightItem => (leftItem, rightItem))
            |>.essentialMaximumMagnitude
              (fun pair => leftValue pair.1 * rightValue pair.2)) =
        left.essentialMaximumMagnitude (fun leftItem =>
          Distance.rationalSeparation (leftValue leftItem) 0 * rightMaximum) :=
      left.essentialMaximumMagnitude_congr _ _ (fun leftItem => by
        rw [right.map_essentialMaximumMagnitude]
        exact right.essentialMaximumMagnitude_scale
          (leftValue leftItem) rightValue)
    left.essentialMaximumMagnitude (fun leftItem =>
          Distance.rationalSeparation (leftValue leftItem) 0 * rightMaximum) =
        left.essentialMaximumMagnitude (fun leftItem =>
          rightMaximum * Distance.rationalSeparation (leftValue leftItem) 0) := by
      exact left.essentialMaximumMagnitude_congr _ _
        (fun leftItem => by ring1)
    _ = Distance.rationalSeparation rightMaximum 0 *
          left.essentialMaximumMagnitude (fun leftItem =>
            Distance.rationalSeparation (leftValue leftItem) 0) :=
      left.essentialMaximumMagnitude_scale rightMaximum _
    _ = rightMaximum * left.essentialMaximumMagnitude leftValue := by
      rw [Distance.rationalSeparation_zero_of_nonneg rightMaximumNonnegative,
        left.essentialMaximumMagnitude_magnitude leftValue]
    _ = left.essentialMaximumMagnitude leftValue * rightMaximum := by ring1

/-- A left-coordinate observable retains its original essential maximum under the product law. -/
theorem product_essentialMaximumMagnitude_left {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (value : α → Fraction.Rational) :
    (left.product right).essentialMaximumMagnitude
        (fun pair => value pair.1) =
      left.essentialMaximumMagnitude value := by
  calc
    (left.product right).essentialMaximumMagnitude
          (fun pair => value pair.1) =
        (left.product right).essentialMaximumMagnitude
          (fun pair => value pair.1 * 1) := by
      exact (left.product right).essentialMaximumMagnitude_congr _ _
        (fun pair => by ring1)
    _ = left.essentialMaximumMagnitude value *
          right.essentialMaximumMagnitude (fun _ => 1) :=
      left.product_essentialMaximumMagnitude_mul right value (fun _ => 1)
    _ = left.essentialMaximumMagnitude value := by
      rw [right.essentialMaximumMagnitude_constant,
        show Distance.rationalSeparation 1 0 = 1 by decide, mul_one]

/-- A right-coordinate observable retains its original essential maximum under the product law. -/
theorem product_essentialMaximumMagnitude_right {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (value : β → Fraction.Rational) :
    (left.product right).essentialMaximumMagnitude
        (fun pair => value pair.2) =
      right.essentialMaximumMagnitude value := by
  calc
    (left.product right).essentialMaximumMagnitude
          (fun pair => value pair.2) =
        (left.product right).essentialMaximumMagnitude
          (fun pair => 1 * value pair.2) := by
      exact (left.product right).essentialMaximumMagnitude_congr _ _
        (fun pair => by ring1)
    _ = left.essentialMaximumMagnitude (fun _ => 1) *
          right.essentialMaximumMagnitude value :=
      left.product_essentialMaximumMagnitude_mul right (fun _ => 1) value
    _ = right.essentialMaximumMagnitude value := by
      rw [left.essentialMaximumMagnitude_constant,
        show Distance.rationalSeparation 1 0 = 1 by decide, one_mul]

/-- Left-coordinate observables retain their original essential maximum distance under the product law. -/
theorem product_essentialMaximumDistance_left {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (first second : α → Fraction.Rational) :
    (left.product right).essentialMaximumDistance
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.essentialMaximumDistance first second := by
  unfold essentialMaximumDistance
  exact left.product_essentialMaximumMagnitude_left right
    (fun item => first item - second item)

/-- Right-coordinate observables retain their original essential maximum distance under the product law. -/
theorem product_essentialMaximumDistance_right {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (first second : β → Fraction.Rational) :
    (left.product right).essentialMaximumDistance
        (fun pair => first pair.2) (fun pair => second pair.2) =
      right.essentialMaximumDistance first second := by
  unfold essentialMaximumDistance
  exact left.product_essentialMaximumMagnitude_right right
    (fun item => first item - second item)

end

end Distribution

end Purelib.Measure

end
