module
public import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Data.CCL.Transducer.Mode.Bounds

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Every value possible at any state of the retained loop process has squared norm at least one.

The estimate uses the positive weight and strict coefficient bound stored in that exact process's loop-domain
certificate, preserving its original owner. -/
theorem loop_candidate_norm_lower (current : Mode.Basic.LoopState)
    (state : current.process.State) {value : Basic.Canonical}
    (possible : current.process.Possible state value) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq value := by
  have coefficientAboveOne :
      1 < (current.domain.weight + 1) / current.domain.weight := by
    apply (Fraction.Order.Field.lt_div_iff_pos
      current.domain.weightPositive).2
    calc
      1 * current.domain.weight = current.domain.weight := by ring1
      _ < current.domain.weight + 1 := by
        calc
          current.domain.weight = 0 + current.domain.weight := by ring1
          _ < 1 + current.domain.weight :=
            Fraction.Order.Arithmetic.add_lt_add_right_direct
              (by decide) current.domain.weight
          _ = current.domain.weight + 1 := _root_.add_comm _ _
  exact (coefficientAboveOne.trans current.domain.coefficient_lt).le.trans
    (current.domain.lower state possible)

end Purelib.Data.CCL.Transducer.Mode.Bounds

end
