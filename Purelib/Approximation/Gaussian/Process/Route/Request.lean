module

public import Purelib.Approximation.Gaussian.Process.Route
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Apart.Based
import Purelib.Approximation.Gaussian.Process.Gamma.Inverse
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Addition
import Purelib.Approximation.Gaussian.Request.Multiplication
import Purelib.Approximation.Gaussian.Request.Division
import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Quarter
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original source requests through retained process routes

Each owned chart propagates its original positive accuracy request to one
original source state. The returned source receipt reconstructs the complete
derived refinement and lifts its cached observation without another callback.
-/

public section

namespace Purelib.Approximation.Gaussian.Process.Route

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Request.Basic (Name)
open Purelib.Approximation.Rational.Request
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq_zero)

/-- An exact source-state action at its original state and positive accuracy target. -/
abbrev StateHandler (m : Type → Type) (source : Gaussian.Process) :=
  (before : source.State) → (target : Fraction.Rational) → (positive : 0 < target) →
    m { state : source.State // state = source.refine before target positive }

/-- An exact observed source action retaining its same returned state, ball and witness. -/
abbrev Handler (m : Type → Type) (source : Gaussian.Process) :=
  (before : source.State) → (target : Fraction.Rational) → (positive : 0 < target) →
    m (Refinement (.input : Route source source) before target positive)

set_option genInjectivity false in
/-- One positive original source request and its exact continuation through the retained chart route.

The input source state is fixed by the original route and current state. Its
returned state must carry the original source refinement identity at the stored
target. Reconstruction preserves that state and the original derived process;
observation completion additionally consumes the same retained source cache.
-/
structure Request {source current : Gaussian.Process} (route : Route source current)
    (before : current.State) (target : Fraction.Rational) (positive : 0 < target) where
  /-- The propagated original source accuracy target. -/ sourceTarget : Fraction.Rational
  /-- The propagated original source target is positive. -/ sourcePositive : 0 < sourceTarget
  /-- Reconstruct the original derived state from its same returned source state. -/ rebuild :
    { state : source.State // state = source.refine (route.sourceState before) sourceTarget sourcePositive } →
      { state : current.State // state = current.refine before target positive }
  /-- Completion retains the actual supplied source state under the original route projection. -/ sourceStateEq :
    ∀ reply, route.sourceState (rebuild reply).val = reply.val

constructive_injectivity Request

/-- A zero-centred request name retains only the original process's stored global bound. -/
private def boundName (process : Gaussian.Process) : Name :=
  Name.centerOnly 0 process.centerBound process.centerBound_nonneg (by
    rw [normSq_zero]
    exact process.centerBound_nonneg)

/-- The original multiplication request and its positivity use the same retained operand bounds. -/
private def mulTarget (left right : Gaussian.Process) (target : Fraction.Rational) (positive : 0 < target) :
    { value : Fraction.Rational // 0 < value } :=
  ⟨Name.multiplicativeInputTarget (boundName left) (boundName right) target,
    Name.multiplicativeInputTarget_pos (boundName left) (boundName right) positive⟩

/-- The original division request retains the same denominator lower quadrance and operand bounds. -/
private def divTarget (left right : Gaussian.Process) (apart : Process.Apart right)
    (target : Fraction.Rational) (positive : 0 < target) : { value : Fraction.Rational // 0 < value } :=
  ⟨Name.divisionInputTarget (boundName left) (boundName right) apart.lowerSq target,
    Name.divisionInputTarget_pos (boundName left) (boundName right) apart.lowerSq apart.positive positive⟩

/-- Reconstruct the original based refinement from the same returned child state.

Persistence is transported through the supplied original refinement equality;
the child refiner is not called while rebuilding the based state.
-/
private def basedAfter (process : Gaussian.Process) (base : process.State)
    (before : Based.BasedState process base) (target : Fraction.Rational) (positive : 0 < target)
    (next : { state : process.State // state = process.refine before.source target positive }) :
    { state : Based.BasedState process base // state = (Based.based process base).refine before target positive } :=
  let state : Based.BasedState process base :=
    { source := next.val
      persists := by
        intro value possible
        exact before.persists (process.refine_persists before.source target positive (next.property ▸ possible)) }
  ⟨state, Based.BasedState.eq_of_source_eq next.property⟩

/-- Reconstruct the original whole-ball apart refinement from its returned child state.

The original apartified refinement supplies only the logical lower-bound proof.
All executable state comes from the retained child reply.
-/
private def apartAfter (process : Gaussian.Process) (apart : Apart.Possible.PossibleApart process)
    (before : Apart.Preparation.ApartState process apart) (target : Fraction.Rational) (positive : 0 < target)
    (next : { state : process.State // state = process.refine before.source
      (Common.commonTarget target (apart.lowerSq / 12)) (Common.commonTarget_pos positive apart.twelfth_pos) }) :
    { state : Apart.Preparation.ApartState process apart //
      state = (Apart.Preparation.apartify apart).refine before target positive } :=
  let state : Apart.Preparation.ApartState process apart :=
    { source := next.val
      wholeBallLower := by
        intro value inside
        apply ((Apart.Preparation.apartify apart).refine before target positive).wholeBallLower
        have originalInside :
            (process.ball (process.refine before.source (Common.commonTarget target (apart.lowerSq / 12))
              (Common.commonTarget_pos positive apart.twelfth_pos))).Contains value :=
          next.property ▸ inside
        exact originalInside }
  ⟨state, Apart.Preparation.ApartState.eq_of_source_eq next.property⟩

/-- Propagate a positive refinement through every original owned chart to one original source request.

The same multiplication, translation, division and whole-ball apartness
targets are retained. Completion consumes the returned child state and
observation at each chart; no source refinement or observation is repeated.
-/
def request {source : Gaussian.Process} : {current : Gaussian.Process} → (route : Route source current) →
    (before : current.State) → (target : Fraction.Rational) → (positive : 0 < target) →
      Request route before target positive
  | _, .input, _, target, positive =>
      { sourceTarget := target
        sourcePositive := positive
        rebuild := fun reply => reply
        sourceStateEq := fun _ => rfl }
  | _, @Route.upscale _ current earlier base exponent, before, target, positive =>
      let factor := Process.exact (Power.natPow Canonical.gamma exponent)
      let input := mulTarget factor (Based.based current base) target positive
      let child := earlier.request before.2.source input.val input.property
      { sourceTarget := child.sourceTarget
        sourcePositive := child.sourcePositive
        rebuild := fun reply =>
          let retained := child.rebuild reply
          let next := basedAfter current base before.2 input.val input.property retained
          let state : (Gamma.Upscale.upscaledProcess current base exponent).State := ((), next.val)
          have same : state = (Gamma.Upscale.upscaledProcess current base exponent).refine before target positive :=
            Prod.ext rfl next.property
          ⟨state, same⟩
        sourceStateEq := fun reply => (child.sourceStateEq reply) }
  | _, @Route.downscale _ current earlier base, before, target, positive =>
      let factor := Process.exact Canonical.gamma⁻¹
      let input := mulTarget factor (Based.based current base) target positive
      let child := earlier.request before.2.source input.val input.property
      { sourceTarget := child.sourceTarget
        sourcePositive := child.sourcePositive
        rebuild := fun reply =>
          let retained := child.rebuild reply
          let next := basedAfter current base before.2 input.val input.property retained
          let state : (Gamma.Downscale.unaryScaledProcess current base).State := ((), next.val)
          have same : state = (Gamma.Downscale.unaryScaledProcess current base).refine before target positive :=
            Prod.ext rfl next.property
          ⟨state, same⟩
        sourceStateEq := fun reply => (child.sourceStateEq reply) }
  | _, @Route.residual _ current earlier base sector, before, target, positive =>
      let input := Name.additiveInputTarget target
      have inputPositive := Bounds.Quarter.quarter_pos positive
      let child := earlier.request before.source input inputPositive
      { sourceTarget := child.sourceTarget
        sourcePositive := child.sourcePositive
        rebuild := fun reply =>
          let retained := child.rebuild reply
          basedAfter current base before input inputPositive retained
        sourceStateEq := fun reply => (child.sourceStateEq reply) }
  | _, @Route.inverse _ current earlier base certificate count, before, target, positive =>
      let candidateApart := Apart.Based.possibleApartOfBall current base certificate
      let denominator := Apart.Preparation.apartify candidateApart
      let inverse := Gamma.Inverse.inverseOfApartProcess current base certificate
      let factor := Process.exact (Power.natPow Canonical.gamma count)⁻¹
      let outerInput := mulTarget factor inverse target positive
      let innerInput := divTarget (Process.exact Canonical.gamma⁻¹) denominator
        (Apart.Preparation.apartifyApart candidateApart) outerInput.val outerInput.property
      let input := Common.commonTarget innerInput.val (candidateApart.lowerSq / 12)
      have inputPositive := Common.commonTarget_pos innerInput.property candidateApart.twelfth_pos
      let child := earlier.request before.2.2.source.source input inputPositive
      { sourceTarget := child.sourceTarget
        sourcePositive := child.sourcePositive
        rebuild := fun reply =>
          let retained := child.rebuild reply
          let based := basedAfter current base before.2.2.source input inputPositive retained
          let apart := apartAfter (Based.based current base) candidateApart before.2.2
            innerInput.val innerInput.property based
          let state : (Gamma.Inverse.Scale.normalizedInverseProcess current base certificate count).State :=
            ((), ((), apart.val))
          have same : state = (Gamma.Inverse.Scale.normalizedInverseProcess current base certificate count).refine
              before target positive :=
            Prod.ext rfl (Prod.ext rfl apart.property)
          ⟨state, same⟩
        sourceStateEq := fun reply => (child.sourceStateEq reply) }

namespace Request

/-- Complete the original routed refinement using the retained source state and its exact cached observation.

State reconstruction needs no source reads. The stored source-state identity
then transports the supplied observation through the same original chart route.
-/
def finish {source current : Gaussian.Process} {route : Route source current} {before : current.State}
    {target : Fraction.Rational} {positive : 0 < target} (question : Request route before target positive)
    (reply : Refinement (.input : Route source source) (route.sourceState before)
      question.sourceTarget question.sourcePositive) : Refinement route before target positive :=
  let rebuilt := question.rebuild ⟨reply.state, reply.stateEq⟩
  let original : Observation source (route.sourceState rebuilt.val) :=
    (question.sourceStateEq ⟨reply.state, reply.stateEq⟩).symm ▸ reply.observation
  ⟨rebuilt.val, rebuilt.property, route.observeFrom rebuilt.val original⟩

/-- A retained source reply completes to the exact full original derived refinement. -/
theorem finish_eq {source current : Gaussian.Process} {route : Route source current} {before : current.State}
    {target : Fraction.Rational} {positive : 0 < target} (question : Request route before target positive)
    (reply : Refinement (.input : Route source source) (route.sourceState before)
      question.sourceTarget question.sourcePositive) :
    question.finish reply = route.refine before target positive :=
  Refinement.unique _ _

end Request

/-- Run one original source-state handler and reconstruct the exact original derived state without observing it.

State-only preparations retain their original source-call boundary. No ball or
witness is read while propagating the returned state through its owned charts.
-/
def refineStateWith {m : Type → Type} [Monad m] {source current : Gaussian.Process}
    (route : Route source current)
    (handler : StateHandler m source)
    (before : current.State) (target : Fraction.Rational) (positive : 0 < target) :
    m { state : current.State // state = current.refine before target positive } := do
  let question := route.request before target positive
  let reply ← handler (route.sourceState before) question.sourceTarget question.sourcePositive
  pure (question.rebuild reply)

/-- A pure original state handler reconstructs the same complete original returned state and certificate. -/
theorem refineStateWith_pure {source current : Gaussian.Process} (route : Route source current)
    (before : current.State) (target : Fraction.Rational) (positive : 0 < target) :
    route.refineStateWith (m := Id)
      (fun state epsilon certificate => ⟨source.refine state epsilon certificate, rfl⟩)
      before target positive = ⟨current.refine before target positive, rfl⟩ := by
  apply Subtype.ext
  exact (route.refineStateWith (m := Id)
    (fun state epsilon certificate => ⟨source.refine state epsilon certificate, rfl⟩)
    before target positive).property

/-- Run one original source handler and reconstruct the same complete routed refinement from its retained reply.

Only the source handler has effects. The route, original input state and
positive request determine its one call; completion reuses that returned state
and observation without installing a replacement process.
-/
def refineWith {m : Type → Type} [Monad m] {source current : Gaussian.Process}
    (route : Route source current)
    (handler : Handler m source)
    (before : current.State) (target : Fraction.Rational) (positive : 0 < target) :
    m (Refinement route before target positive) := do
  let question := route.request before target positive
  let reply ← handler (route.sourceState before) question.sourceTarget question.sourcePositive
  pure (question.finish reply)

/-- The pure original source handler reconstructs the complete original routed refinement for every input. -/
theorem refineWith_pure {source current : Gaussian.Process} (route : Route source current)
    (before : current.State) (target : Fraction.Rational) (positive : 0 < target) :
    route.refineWith (m := Id)
      (fun state epsilon certificate => (.input : Route source source).refine state epsilon certificate)
      before target positive = route.refine before target positive :=
  Refinement.unique _ _

end Purelib.Approximation.Gaussian.Process.Route

end
