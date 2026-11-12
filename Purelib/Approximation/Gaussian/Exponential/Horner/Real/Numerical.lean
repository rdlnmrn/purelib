module
public import Purelib.Approximation.Gaussian.Exponential.Horner.Real.State
public import Purelib.Approximation.Gaussian.Exponential.Horner.Real.Comparison
import Purelib.Data.Rat.Interval.Comparison
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Comparing a finite Taylor reading with an original numerical point state

One common later Horner depth is selected from the supplied finite depth and
the actual original Gaussian point state. Its sample belongs to that state;
the original earlier-depth allowance and actual interval width pay for the
comparison.
-/

public section

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Real

open Purelib.Data.Nat
open Purelib.Data.Rat

/-- Compare an original numerical point reading with one displayed finite Taylor reading.

The state and contained numerical reading are supplied from the original
point process. The explicit bound retains that state's actual width and the
original finite depth's coordinate tail radius. -/
theorem finite_numerical_difference (depth : Nat) (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1)
    (state : (source point).State) (reading : Fraction.Rational)
    (inside : ((source point).bound state).Contains reading) :
    Fraction.abs (finiteSource depth point - reading) ≤
      ((source point).bound state).width + tailRadius depth := by
  let current : Nat := (originalState point unit state).current
  let later := Nat.max depth current
  have depthLe : depth ≤ later := Order.le_max_left depth current
  have currentLe : current ≤ later := Order.le_max_right depth current
  have sample := sample_inside point unit state later currentLe
  let exact := Purelib.Data.Rat.Interval.exact (finiteSource depth point)
  have exactInside : exact.Contains (finiteSource depth point) :=
    (Purelib.Data.Rat.Interval.exact_contains_iff _ _).mpr rfl
  have comparison := Purelib.Data.Rat.Interval.abs_sub_le_of_readings exactInside inside exactInside sample
  have tail := finite_later_difference depth later depthLe point unit.1 unit.2
  rw [Bounds.Abs.abs_sub_comm_direct] at tail
  have bound := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl (exact.width + ((source point).bound state).width)) tail
  have identity : exact.width + ((source point).bound state).width + tailRadius depth =
      ((source point).bound state).width + tailRadius depth := by
    rw [Purelib.Data.Rat.Interval.exact_width]
    ring1
  rw [identity] at bound
  exact comparison.trans bound

end Purelib.Approximation.Gaussian.Exponential.Horner.Real

end
