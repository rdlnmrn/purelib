module
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

public section

namespace Purelib.Approximation.Gaussian.Enclosure.Ball

open Purelib.Data.Gaussian

/-- The conjugated ball retains the conjugate of its original center. -/
theorem conj_center (ball : Ball) : ball.conj.center = Basic.conj ball.center := rfl

/-- Conjugation sends every original admitted reading to an admitted conjugate reading.

The squared distance between the reading and center is unchanged, so the
original membership bound applies with the same squared-error allowance. -/
theorem contains_conj {ball : Ball} {value : Basic.Canonical}
    (inside : ball.Contains value) : ball.conj.Contains (Basic.conj value) := by
  change Norm.Basic.normSq (Basic.Canonical.conj value -
    Basic.Canonical.conj ball.center) ≤ ball.radiusSq
  rewrite [Norm.Basic.normSq_eq_canonical, Basic.Canonical.normSq_conj_sub,
    ← Norm.Basic.normSq_eq_canonical]
  exact inside

/-- A conjugated reading belongs to the conjugated ball exactly when the original does. -/
theorem contains_conj_iff (ball : Ball) (value : Basic.Canonical) :
    ball.conj.Contains (Basic.conj value) ↔ ball.Contains value := by
  constructor
  · intro inside
    have original := contains_conj inside
    rewrite [conj_conj, Basic.conj_conj] at original
    exact original
  · exact contains_conj

/-- Conjugating an exact point ball retains the exact conjugated point ball. -/
theorem conj_point (value : Basic.Canonical) : (point value).conj = point (Basic.conj value) := rfl

end Purelib.Approximation.Gaussian.Enclosure.Ball

end
