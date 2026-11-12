module
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
public import Purelib.Approximation.Gaussian.Process.Recipe.Basic
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.Program
import Purelib.Computation.Query.Basic

section
@[expose] public section

/-!
# Finite numerical chart expressions for transducer replay

The expression contains only displayed arithmetic data and cached center
bounds.  It has no model evaluator or hidden process callback.  Its source
accuracy request is pure finite arithmetic; observing its ball performs one
explicit model query and transforms that retained reply.

These expressions are the numerical part of the existing chart operations,
not independent semantic enclosure certificates.  `Represents` below ties a
generated expression to an actual certified process.  In particular, a raw
division expression alone does not establish apartness or accuracy.  The
controller bridge must derive that representation and reject invalid numeric
decisions; this module alone is not an arbitrary-prefix replay theorem.
-/

namespace Purelib.Approximation.Gaussian.Process.Recipe

open Purelib.Approximation.Gaussian
open Purelib.CCL.Progressive
open Purelib.Computation.Query (Program Protocol)

/-- Query the exact retained source stage and apply the supplied recipe to its checked ball reading.

Invalid source replies remain explicit errors; successful readings retain the original recipe transformation. -/
def ballProgram (control : IntegrationReplay.Control) (recipe
  : Recipe) (index : Nat) :
    IntegrationReplay.QueryProgram (Except IntegrationReplay.InvalidReply Enclosure.Ball.Data.BallData) :=
  (IntegrationReplay.readProgram control index).map fun result =>
    result.map (fun reading => recipe.transform (Enclosure.Ball.Data.BallData.ofBall reading.ball))

/-- Execute the retained recipe construction through its original protocol boundary. -/
def ball (control : IntegrationReplay.Control) (recipe : Recipe) (index : Nat) :
    IntegrationReplay.QueryComputation (Except IntegrationReplay.InvalidReply Enclosure.Ball.Data.BallData) :=
  (ballProgram control recipe index).protocol

/-- Recipe execution transforms the original checked reading and preserves its complete ordered trace. -/
theorem ball_run (control : IntegrationReplay.Control) (recipe : Recipe) (index : Nat)
    (oracle : Nat → IntegrationReplay.CachedModel) :
    (ball control recipe index).run oracle =
      ((IntegrationReplay.read control index).map fun result =>
        result.map fun reading => recipe.transform (Enclosure.Ball.Data.BallData.ofBall reading.ball)).run oracle :=
  Program.map_execution _ _ oracle

/-- The recipe ball query records exactly the original requested index and its oracle reply. -/
theorem ball_trace (control :
  IntegrationReplay.Control) (recipe : Recipe) (index : Nat)
    (oracle : Nat → IntegrationReplay.CachedModel) :
    ((recipe.ball control index).run oracle).trace = [⟨index, oracle index⟩] :=
  (congrArg (fun execution => execution.trace) (ball_run control recipe index oracle)).trans
    ((Protocol.map_run_trace _ _ _).trans (IntegrationReplay.read_trace control index oracle))

end Purelib.Approximation.Gaussian.Process.Recipe

end
