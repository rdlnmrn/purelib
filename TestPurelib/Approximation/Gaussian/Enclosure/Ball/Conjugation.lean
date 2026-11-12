module
import Purelib.Approximation.Gaussian.Enclosure.Ball.Conjugation

namespace TestPurelib.Approximation.Gaussian.Enclosure.Ball.Conjugation

open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Data.Gaussian

/-- Every reading of an arbitrary original sample sequence retains its original enclosure bound. -/
example (ball : Ball) (samples : Nat → Basic.Canonical)
    (inside : ∀ index, ball.Contains (samples index)) :
    ∀ index, ball.conj.Contains (Basic.conj (samples index)) :=
  fun index => Ball.contains_conj (inside index)

/-- Center and allowance readbacks identify the original inputs for every ball. -/
example (ball : Ball) :
    ball.conj.center = Basic.conj ball.center ∧ ball.conj.radiusSq = ball.radiusSq :=
  ⟨Ball.conj_center ball, Ball.conj_radiusSq ball⟩

/-- Twice conjugating an arbitrary original ball retains its complete record. -/
example (ball : Ball) : ball.conj.conj = ball := Ball.conj_conj ball

/-- Both directions of exact membership transport retain the original reading and ball. -/
example (ball : Ball) (value : Basic.Canonical) :
    ball.conj.Contains (Basic.conj value) ↔ ball.Contains value :=
  Ball.contains_conj_iff ball value

/-- Zero-radius enclosures retain the actual conjugated point construction. -/
example (value : Basic.Canonical) :
    (Ball.point value).conj = Ball.point (Basic.conj value) := Ball.conj_point value

end TestPurelib.Approximation.Gaussian.Enclosure.Ball.Conjugation
