module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds
public import Purelib.Approximation.Gaussian.Enclosure.Residual
public import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Approximation.Gaussian.Process.Bounds

/-- Every possible reading at a retained process state meets the observed ball's explicit small-upper quadrance bound.
-/
theorem smallUpper_bound
    {process : Approximation.Gaussian.Process} {state : process.State}
    {target : Fraction.Rational}
    (_small : Residual.SmallBall
      (process.ball state) target)
    {value : Data.Gaussian.Basic.Canonical} (possible : process.Possible state value) :
    Data.Gaussian.Norm.Basic.normSq value ≤ Ball.Bounds.smallUpper (process.ball state) := by
  have decomposition :
      value = (value - (process.ball state).center) +
        (process.ball state).center := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  rw [decomposition]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (process.possible_inside possible) le_rfl) (by decide))

end Purelib.Approximation.Gaussian.Process.Bounds

end
