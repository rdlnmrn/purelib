module

public import Purelib.Approximation.Gaussian.Process.Observation
public import Purelib.Approximation.Gaussian.Process.Based
public import Purelib.Approximation.Gaussian.Process.Multiplication
public import Purelib.Approximation.Gaussian.Process.Translation
public import Purelib.Approximation.Gaussian.Process.Division
public import Purelib.Approximation.Gaussian.Process.Apart.Preparation

/-!
# Original process operations on cached observations

These operations consume the original retained balls and possible witnesses.
They construct the observations of the original derived process states using
pure finite arithmetic, without calling any source observation again.
-/

public section

namespace Purelib.Approximation.Gaussian.Process.Observation

open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Enclosure

/-- Cache the original exact rational process's observation using its displayed point alone. -/
@[expose] def exact (value : Basic.Canonical) (state : Unit := ()) : Observation (Process.exact value) state :=
  ofReadings _ _ (Ball.point value) rfl ⟨value, rfl⟩ rfl

/-- Reuse the same original observation at a retained state of its based process. -/
@[expose] def based {process : Gaussian.Process} (base : process.State)
    (state : Process.Based.BasedState process base) (observation : Observation process state.source) :
    Observation (Process.Based.based process base) state :=
  ofReadings _ _ observation.ball observation.ballEq observation.witness observation.witnessEq

/-- Multiply two original cached observations at the same original paired process state. -/
@[expose] def mul {left right : Gaussian.Process} {leftState : left.State} {rightState : right.State}
    (first : Observation left leftState) (second : Observation right rightState) :
    Observation (Process.mul left right) (leftState, rightState) := by
  let ball := first.ball.mul second.ball
  let witness : { value : Basic.Canonical // (Process.mul left right).Possible (leftState, rightState) value } :=
    ⟨first.witness.val * second.witness.val, first.witness.val, second.witness.val,
      first.witness.property, second.witness.property, rfl⟩
  have ballEq : ball = (Process.mul left right).ball (leftState, rightState) :=
    congrArg₂ Ball.mul first.ballEq second.ballEq
  have witnessEq : witness = (Process.mul left right).witness (leftState, rightState) := by
    apply Subtype.ext
    exact congrArg₂ (fun x y : Basic.Canonical => x * y)
      (congrArg Subtype.val first.witnessEq) (congrArg Subtype.val second.witnessEq)
  exact ofReadings _ _ ball ballEq witness witnessEq

/-- Translate the original cached ball and witness by the same retained rational shift. -/
@[expose] def translate {process : Gaussian.Process} {state : process.State}
    (observation : Observation process state) (shift : Basic.Canonical) :
    Observation (Process.Translation.translate process shift) state := by
  let ball := observation.ball.sub (Ball.point shift)
  let witness : { value : Basic.Canonical // (Process.Translation.translate process shift).Possible state value } :=
    ⟨observation.witness.val - shift, observation.witness.val, observation.witness.property, rfl⟩
  have ballEq : ball = (Process.Translation.translate process shift).ball state :=
    congrArg (fun source => source.sub (Ball.point shift)) observation.ballEq
  have witnessEq : witness = (Process.Translation.translate process shift).witness state := by
    apply Subtype.ext
    exact congrArg (fun value : Basic.Canonical => value - shift) (congrArg Subtype.val observation.witnessEq)
  exact ofReadings _ _ ball ballEq witness witnessEq

/-- Reuse the same cached observation of an original apartified state and its original dependent source. -/
@[expose] def apartify {process : Gaussian.Process} (apart : Process.Apart.Possible.PossibleApart process)
    (state : Process.Apart.Preparation.ApartState process apart)
    (observation : Observation process state.source) :
    Observation (Process.Apart.Preparation.apartify apart) state :=
  ofReadings _ _ observation.ball observation.ballEq observation.witness observation.witnessEq

/-- Divide the same original cached observations using the denominator's retained whole-ball apartness.

The derived ball and witness use these exact caches. The apartness certificate
retains the original denominator's lower quadrance and does not reread it.
-/
@[expose] def div {left right : Gaussian.Process} {leftState : left.State} {rightState : right.State}
    (first : Observation left leftState) (second : Observation right rightState) (apart : Process.Apart right) :
    Observation (Process.div left right apart) (leftState, rightState) := by
  let separated : Ball.Apart second.ball := second.ballEq.symm ▸ apart.atState rightState
  let ball := first.ball.div second.ball separated
  let witness : { value : Basic.Canonical // (Process.div left right apart).Possible (leftState, rightState) value } :=
    ⟨first.witness.val / second.witness.val, first.witness.val, second.witness.val,
      first.witness.property, second.witness.property, rfl⟩
  have ballEq : ball = (Process.div left right apart).ball (leftState, rightState) := by
    rcases first with ⟨firstBall, firstBallEq, firstWitness, firstWitnessEq, firstGeneric, firstGenericEq⟩
    rcases second with ⟨secondBall, secondBallEq, secondWitness, secondWitnessEq, secondGeneric, secondGenericEq⟩
    cases firstBallEq
    cases secondBallEq
    rfl
  have witnessEq : witness = (Process.div left right apart).witness (leftState, rightState) := by
    apply Subtype.ext
    exact congrArg₂ (fun x y : Basic.Canonical => x / y)
      (congrArg Subtype.val first.witnessEq) (congrArg Subtype.val second.witnessEq)
  exact ofReadings _ _ ball ballEq witness witnessEq

end Purelib.Approximation.Gaussian.Process.Observation
