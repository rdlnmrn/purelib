module
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
public import Purelib.Approximation.Gaussian.Process.Recipe.Basic
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Computation
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
section Recipe

open Purelib.Approximation.Gaussian in
open Purelib.CCL.Progressive in
/-- Query the exact retained source stage and apply the supplied recipe to its checked ball reading.

Invalid source replies remain explicit errors; successful readings retain the original recipe transformation. -/
def ball (control : IntegrationReplay.Control) (recipe
  : Recipe) (index : Nat) :
    IntegrationReplay.QueryComputation (Except IntegrationReplay.InvalidReply Enclosure.Ball.Data.BallData) :=
  (IntegrationReplay.read control index).map fun result =>
    result.map (fun reading => recipe.transform (Enclosure.Ball.Data.BallData.ofBall reading.ball))

open Purelib.Approximation.Gaussian in
open Purelib.CCL.Progressive in
open Purelib.Computation.Query in
open Purelib.Integration.Program.Gaussian.Cached in
/-- The recipe ball query records exactly the original requested index and its oracle reply. -/
theorem ball_trace (control :
  IntegrationReplay.Control) (recipe : Recipe) (index : Nat)
    (oracle : Nat → Basic.CachedModel) :
    ((recipe.ball control index).run oracle).trace = [⟨index, oracle index⟩] :=
  (Computation.Query.Protocol.map_run_trace _ _ _).trans (IntegrationReplay.read_trace control index oracle)

end Recipe

end Purelib.Approximation.Gaussian.Process.Recipe

end
