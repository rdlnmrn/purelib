module

public import Purelib.Approximation.Gaussian.Process.Observation.Operations
public import Purelib.Approximation.Gaussian.Process.Gamma.Upscale
public import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
public import Purelib.Approximation.Gaussian.Process.Sector.Residual
public import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale

/-!
# Original process routes through owned unary charts

A route retains the supplied process as its opaque boundary. Every later
constructor names an original owned chart and its exact dependent base state.
The route describes that same process; it installs no alternative evaluator.
-/

public section

namespace Purelib.Approximation.Gaussian.Process

open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.Rat

set_option genInjectivity false in
/-- An exact chain of owned unary charts over one original supplied process.

Only the supplied process's internals are opaque. Exact scaling factors,
rebasing, sector translation and the apart normalized inverse remain their
original process constructors, including their original states and bounds.
-/
inductive Route (source : Gaussian.Process) : Gaussian.Process → Type 1 where
  /-- The original supplied process is the boundary for numerical interface calls. -/ | input : Route source source
  /-- Retain the exact original upward unary chart over the same source route. -/ | upscale
      {current : Gaussian.Process} (earlier : Route source current) (base : current.State) (exponent : Nat) :
      Route source (Gamma.Upscale.upscaledProcess current base exponent)
  /-- Retain the exact original downward unary chart over the same source route. -/ | downscale
      {current : Gaussian.Process} (earlier : Route source current) (base : current.State) :
      Route source (Gamma.Downscale.unaryScaledProcess current base)
  /-- Retain the exact original selected-sector translation over the same source route. -/ | residual
      {current : Gaussian.Process} (earlier : Route source current) (base : current.State) (sector : Sector) :
      Route source (Process.Sector.Residual.residualProcess current base sector)
  /-- Retain the exact original apart inverse and unary normalization over the same source route. -/ | inverse
      {current : Gaussian.Process} (earlier : Route source current) (base : current.State)
      (certificate : Enclosure.Ball.Apart (current.ball base)) (count : Nat) :
      Route source (Gamma.Inverse.Scale.normalizedInverseProcess current base certificate count)

namespace Route

/-- Project the actual underlying source state through the original retained chart states. -/
@[expose] def sourceState {source : Gaussian.Process} :
    {current : Gaussian.Process} → Route source current → current.State → source.State
  | _, .input, state => state
  | _, .upscale earlier _ _, state => earlier.sourceState state.2.source
  | _, .downscale earlier _, state => earlier.sourceState state.2.source
  | _, .residual earlier _ _, state => earlier.sourceState state.source
  | _, .inverse earlier _ _ _, state => earlier.sourceState state.2.2.source.source

/-- Count the actual boundary calls routed by one ball, witness or refinement invocation.

Each owned chart delegates to its same retained child once. Exact factors and
chart arithmetic are pure; apartness certificates are proof data. Initial
apart-state preparation is a separate refinement and is charged by its actual
emission receipt, rather than hidden in this per-invocation count.
-/
@[expose] def calls {source current : Gaussian.Process} : Route source current → Nat
  | .input => 1
  | .upscale earlier _ _ | .downscale earlier _ | .residual earlier _ _ | .inverse earlier _ _ _ =>
      earlier.calls

/-- Every retained unary route reaches the same one original process boundary per interface invocation. -/
theorem calls_eq_one {source current : Gaussian.Process} (route : Route source current) : route.calls = 1 := by
  induction route with
  | input => rfl
  | upscale earlier base exponent induction => exact induction
  | downscale earlier base induction => exact induction
  | residual earlier base sector induction => exact induction
  | inverse earlier base certificate count induction => exact induction

/-- Lift one retained original source observation through the same owned charts.

Each recursive chart operation consumes the same cached child ball and witness.
The returned observation has the original derived process and state, together
with their canonical full readbacks. No source callback is invoked.
-/
@[expose] def observeFrom {source : Gaussian.Process} :
    {current : Gaussian.Process} → (route : Route source current) → (state : current.State) →
      Observation source (route.sourceState state) → Observation current state
  | _, .input, _, original => original
  | _, .upscale earlier base exponent, state, original =>
      Observation.mul (Observation.exact (Power.natPow Basic.Canonical.gamma exponent) state.1)
        (Observation.based base state.2 (earlier.observeFrom state.2.source original))
  | _, .downscale earlier base, state, original =>
      Observation.mul (Observation.exact Basic.Canonical.gamma⁻¹ state.1)
        (Observation.based base state.2 (earlier.observeFrom state.2.source original))
  | _, .residual earlier base sector, state, original =>
      Observation.translate (Observation.based base state (earlier.observeFrom state.source original)) sector.rep
  | _, @Route.inverse _ current earlier base certificate count, state, original =>
      let possibleApart := Process.Apart.Based.possibleApartOfBall current base certificate
      let child := earlier.observeFrom state.2.2.source.source original
      let based := Observation.based base state.2.2.source child
      let denominator := Observation.apartify possibleApart state.2.2 based
      let inverse := Observation.div (Observation.exact Basic.Canonical.gamma⁻¹ state.2.1) denominator
        (Process.Apart.Preparation.apartifyApart possibleApart)
      Observation.mul (Observation.exact (Power.natPow Basic.Canonical.gamma count)⁻¹ state.1) inverse

/-- Observe the original supplied boundary once and lift that same cache through every owned chart. -/
@[expose] def observe {source current : Gaussian.Process} (route : Route source current)
    (state : current.State) : Observation current state :=
  route.observeFrom state (Observation.build source (route.sourceState state))

/-- A retained source cache produces the complete same original routed observation. -/
theorem observeFrom_eq {source current : Gaussian.Process} (route : Route source current)
    (state : current.State) (original : Observation source (route.sourceState state)) :
    route.observeFrom state original = route.observe state :=
  Observation.unique _ _

/-- Count the actual ball and witness calls made at the supplied boundary by the routed observation builder. -/
@[expose] def observeSourceCalls {source current : Gaussian.Process} (route : Route source current) : Nat :=
  2 * route.calls

/-- Routed observation construction reads the same original boundary ball and witness exactly once each. -/
theorem observeSourceCalls_eq {source current : Gaussian.Process} (route : Route source current) :
    route.observeSourceCalls = 2 := by
  unfold observeSourceCalls
  rewrite [route.calls_eq_one]
  rfl

set_option genInjectivity false in
/-- One actual original refinement with its returned state and exact routed observation cached once. -/
structure Refinement {source current : Gaussian.Process} (route : Route source current)
    (before : current.State) (target : Fraction.Rational) (positive : 0 < target) where
  /-- The actual state returned by the original same process refinement. -/ state : current.State
  /-- The retained state is that exact original refinement result. -/ stateEq :
    state = current.refine before target positive
  /-- The exact returned state's original observation, using the retained source route. -/ observation :
    Observation current state

namespace Refinement

/-- Observe an exact already returned original state without repeating its refinement.

The supplied equality binds the state to this same process, input and positive
target. The routed observation reads its original source ball and witness once.
-/
@[expose] def ofState {source current : Gaussian.Process} (route : Route source current)
    (before : current.State) (target : Fraction.Rational) (positive : 0 < target)
    (retained : { state : current.State // state = current.refine before target positive }) :
    Refinement route before target positive :=
  ⟨retained.val, retained.property, route.observe retained.val⟩

end Refinement

/-- Refine the original same process once, then observe its actual returned state through the retained source route. -/
@[expose] def refine {source current : Gaussian.Process} (route : Route source current)
    (before : current.State) (target : Fraction.Rational) (positive : 0 < target) :
    Refinement route before target positive :=
  Refinement.ofState route before target positive ⟨current.refine before target positive, rfl⟩

namespace Refinement

/-- Exact original state and observation identities determine the complete refinement receipt.

Both receipts retain the same process, input state and positive request. Their
returned states and complete cached observations therefore agree, including
all dependent certificates.
-/
theorem unique {source current : Gaussian.Process} {route : Route source current}
    {before : current.State} {target : Fraction.Rational} {positive : 0 < target}
    (left right : Refinement route before target positive) : left = right := by
  rcases left with ⟨state, stateEq, observation⟩
  rcases right with ⟨other, otherEq, otherObservation⟩
  have same : other = state := otherEq.trans stateEq.symm
  cases same
  cases Observation.unique observation otherObservation
  rfl

/-- Count this actual original refinement and its same cached routed ball and witness reads. -/
@[expose] def sourceCalls {source current : Gaussian.Process} {route : Route source current}
    {before : current.State} {target : Fraction.Rational} {positive : 0 < target}
    (_receipt : Refinement route before target positive) : Nat :=
  route.calls + route.observeSourceCalls

/-- The actual refined observation pays one original boundary refinement, ball read and witness read. -/
theorem sourceCalls_eq {source current : Gaussian.Process} {route : Route source current}
    {before : current.State} {target : Fraction.Rational} {positive : 0 < target}
    (receipt : Refinement route before target positive) : receipt.sourceCalls = 3 := by
  unfold sourceCalls
  rewrite [route.calls_eq_one, route.observeSourceCalls_eq]
  rfl

end Refinement

end Route

end Purelib.Approximation.Gaussian.Process
