module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

section
@[expose] public section

/-!
# Automatic discovery of the initial positive enclosure

A cached rational ball passes when its centre is above the real axis and its
squared radius is below the squared half-height. The soundness proof gives a
positive imaginary lower bound for every point in that ball. Failed tests
perform one canonical finite refinement; bounded runs retain their exact
state on exhaustion and never infer a negative positivity verdict.
-/

namespace Purelib.Approximation.Gaussian.Acquisition

namespace State

set_option genInjectivity false in
/-- The retained source includes candidate provenance and the next canonical request index. The displayed ball is cached
instead of recomputed for tests. -/
structure StatePayload (sourceType : Type) (ballAt : sourceType
  → Enclosure.Ball) where
  /-- The exact source state whose enclosure is cached. -/ retained : sourceType
  /-- The cached rational enclosure of the retained source state. -/ ball : Enclosure.Ball
  /-- The cached enclosure equals the enclosure of that exact retained state. -/ ball_eq : ball = ballAt retained

constructive_injectivity StatePayload

end State

/-- The cached enclosure and canonical refinement state for the original coherent Gaussian name.

The dependent state preserves candidate provenance and the cache equality connects every test to the retained process
state. -/
def State (tau : Coherent.CoherentNamed) :=
  State.StatePayload (Name.Coherent.Refinement.State tau)
    (fun retained => tau.name.process.ball retained.source)

namespace State

/-- Cache the enclosure of the displayed refinement state without changing its source or candidate provenance. -/
def cache (tau : Coherent.CoherentNamed) (retained :
    Name.Coherent.Refinement.State
  tau) :
    State tau :=
  { retained := retained
    ball := tau.name.process.ball retained.source
    ball_eq := rfl }

/-- Cache the original name state at canonical refinement index zero. -/
def initial (tau : Coherent.CoherentNamed) :
  State tau :=
  Approximation.Gaussian.Acquisition.State.cache tau (Name.Coherent.Refinement.State.initial tau)

/-- Perform one canonical refinement and cache the resulting enclosure with its exact state equality. -/
def advance {tau : Coherent.CoherentNamed} (state :
  State tau) : State tau :=
  Approximation.Gaussian.Acquisition.State.cache tau state.retained.advance

/-- Every retained search candidate preserves its original input provenance. -/
theorem possible_at_initial {tau : Coherent.CoherentNamed}
  (state : State tau)
    {value : Data.Gaussian.Basic.Canonical} (possible : tau.name.process.Possible state.retained.source value) :
    tau.name.process.Possible tau.name.state value := state.retained.persists possible

end State

end Purelib.Approximation.Gaussian.Acquisition

end
