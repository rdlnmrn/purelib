module
import Purelib.Data.GaussianInt.Basic

import Purelib.Data.GaussianInt.Cancellation
public import Purelib.Geometry.Projective.Line.Basic
import Purelib.Tactic.Ring

namespace Purelib.Data.GaussianInt

open Purelib.Geometry.Projective.Line

public section

/-- Cross-multiplication equivalence of Gaussian-integer projective pairs is transitive
through a nonzero middle denominator.

The middle denominator is retained explicitly and cancelled from the two combined
cross-product identities. -/
theorem equivalent_trans_of_mid_q {left middle right : Proj GaussianInt}
    (leftMiddle : Proj.Equivalent left middle)
    (middleRight : Proj.Equivalent middle right)
    (middleDenominatorNonzero : middle.q ≠ 0) :
    Proj.Equivalent left right := by
  dsimp only [Proj.Equivalent] at leftMiddle middleRight ⊢
  apply mul_right_cancel_of_ne middleDenominatorNonzero
  calc
    (left.p * right.q) * middle.q =
        right.q * (left.p * middle.q) := by ring1
    _ = right.q * (middle.p * left.q) := by rw [leftMiddle]
    _ = left.q * (middle.p * right.q) := by ring1
    _ = left.q * (right.p * middle.q) := by rw [middleRight]
    _ = (right.p * left.q) * middle.q := by ring1

end

end Purelib.Data.GaussianInt
