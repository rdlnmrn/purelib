module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Apart
public import Purelib.Approximation.Gaussian.Name.Coherent.Based
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
public import Purelib.Approximation.Gaussian.Process.Apart.Based
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Based
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

section
@[expose] public section

/-!
# Retryable finite preflight for constructive division

An ordinary progressive division is total only after its denominator carries
uniform whole-ball apartness.  This module searches for that certificate one
explicit finite refinement at a time.  It keeps the existing total `Process`
and productive transducer unchanged: a caller receives an ordinary
`CoherentNamed` only in the `ready` case.

Failure of the current rational separation test is represented solely by a
certified progress step.  It is neither evidence that the denominator is zero
nor evidence that zero lies in the current ball.  Manual resumption accepts an
apartness witness indexed by the exact retained denominator state.
-/

namespace Purelib.Approximation.Gaussian.Division.Partial.Preparation

/-- The coherent denominator restricted to the retained refinement future. -/
def basedDenominator {denominator :
  Coherent.CoherentNamed}
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) : Coherent.CoherentNamed :=
  CoherentNamed.based denominator state.source

/-- Turn exact state-indexed candidate apartness into the existing total, whole-ball-apart coherent denominator. -/
def preparedDenominator {denominator :
  Coherent.CoherentNamed}
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based denominator.name.process state.source)) :
    Coherent.CoherentNamed :=
  CoherentNamed.apartify
    (basedDenominator state) evidence

/-- Uniform whole-ball apartness consumed by ordinary total division. -/
def preparedApart {denominator :
  Coherent.CoherentNamed}
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based denominator.name.process state.source)) :
    Named.Apart
      (preparedDenominator state evidence).name where
  certificate := Preparation.apartifyApart evidence

/-- Convert the successful rational centre-separation test into the precisely indexed evidence required for manual or
automatic readiness. -/
def evidenceOfSeparation {denominator :
  Coherent.CoherentNamed}
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator)
    (separated :
      2 * (denominator.name.process.ball state.source).radiusSq <
        Data.Gaussian.Norm.Basic.normSq (denominator.name.process.ball state.source).center) :
    Possible.PossibleApart
      (Gaussian.Process.Based.based denominator.name.process state.source) :=
  Based.possibleApartOfBall
    denominator.name.process state.source
    (Residual.apartOfCenter
      (denominator.name.process.ball state.source) separated)

set_option genInjectivity false in
/-- Denominator-only preparation result. This separates acquisition of the apartness certificate from construction of a
quotient, allowing a dependency scheduler to prepare a denominator before its numerator is available. -/
inductive PreparationResult (denominator :
  Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) : Type
  /-- Retain apartness evidence for the denominator process based at this exact refinement state. -/ | prepared
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based denominator.name.process state.source))
  /-- Retain the next denominator refinement state and its certified progress from the original state. -/ | progressed
    (next : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) (progress : State.Progress state next)

constructive_injectivity PreparationResult

/-- Inspect or refine only the denominator. No placeholder numerator and no partial quotient is constructed. -/
def prepare (denominator : Coherent.CoherentNamed)
  (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) :
    PreparationResult denominator state :=
  if separated :
      2 * (denominator.name.process.ball state.source).radiusSq <
        Data.Gaussian.Norm.Basic.normSq (denominator.name.process.ball state.source).center then
    .prepared (evidenceOfSeparation state separated)
  else
    .progressed state.advance (.refined state)

/-- Successful center separation makes denominator preparation return the prepared alternative with state-indexed
apartness evidence. -/
theorem prepare_is_prepared_of_separated (denominator
  : Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator)
    (separated :
      2 * (denominator.name.process.ball state.source).radiusSq <
        Data.Gaussian.Norm.Basic.normSq (denominator.name.process.ball state.source).center) :
    ∃ evidence : Possible.PossibleApart
        (Gaussian.Process.Based.based denominator.name.process state.source),
      prepare denominator state = .prepared evidence := by
  rw [prepare, dif_pos separated]
  exact ⟨_, rfl⟩

/-- Without center separation, preparation returns the canonical refined state and its progress certificate. -/
theorem prepare_eq_progressed_of_not_separated
    (denominator : Coherent.CoherentNamed) (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator)
    (notSeparated : ¬
      2 * (denominator.name.process.ball state.source).radiusSq <
        Data.Gaussian.Norm.Basic.normSq (denominator.name.process.ball state.source).center) :
    prepare denominator state =
      .progressed state.advance (.refined state) := by
  rw [prepare, dif_neg notSeparated]
end Purelib.Approximation.Gaussian.Division.Partial.Preparation

end
