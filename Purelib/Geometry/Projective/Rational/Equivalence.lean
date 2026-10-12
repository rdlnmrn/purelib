module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Geometry.Projective.Line.Basic

import Lean.Elab.Tactic.Omega
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line

/-!
# Constructive one-dimensional baseline algorithms

Executable versions of the real continued-fraction and continued-logarithm
algorithms used for comparison in the CCL manuscript.  Both encoders recurse
on the displayed natural measure and decode in explicit constructive rational
coordinates.
-/

@[expose] public section

namespace Purelib.Geometry.Projective.Rational.Equivalence

/-- Transitivity of finite projective equivalence using the explicit constructive-rational cancellation theorem, rather
than a derived domain instance. -/
theorem equivalent_trans_of_mid_q {left middle right : Line.Proj
  Fraction.Rational}
    (leftMiddle : left.Equivalent middle)
    (middleRight : middle.Equivalent right)
    (middleDenominatorNonzero : middle.q ≠ 0) :
    left.Equivalent right := by
  dsimp only [Proj.Equivalent] at leftMiddle middleRight ⊢
  apply Fraction.Field.mul_right_cancel_of_ne
    middleDenominatorNonzero
  calc
    (left.p * right.q) * middle.q =
        right.q * (left.p * middle.q) := by ring1
    _ = right.q * (middle.p * left.q) := by rw [leftMiddle]
    _ = left.q * (middle.p * right.q) := by ring1
    _ = left.q * (right.p * middle.q) := by rw [middleRight]
    _ = (right.p * left.q) * middle.q := by ring1
end Purelib.Geometry.Projective.Rational.Equivalence

end
