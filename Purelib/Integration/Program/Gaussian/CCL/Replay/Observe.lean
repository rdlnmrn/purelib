module
import Purelib.Data.Rat.Fraction
public import Purelib.Integration.Program.Gaussian.Query.Recipe
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
import Purelib.CCL.Progressive.IntegrationQueries
public import Purelib.Data.CCL.Transducer.Replay.Check
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Computation.Query.Computation

section
@[expose] public section

/-!
# Finite numerical controller and adaptive replay

All executable state below is finite chart syntax, rational bounds, natural
source indices and bit lists.  In particular, neither a `Process` nor a
source evaluator occurs in a returned state.  Each productive chunk records
its model reads, including the second read after a residual inverse chart
change.  Buffered bits do not perform a model query.

This is the numerical interpreter.  Its connection to the certified
transducer is established separately; successful replay of an invented log
does not certify global coherence of its replies.
-/

namespace Purelib.Approximation.Gaussian.Process.Recipe.Cursor

open Purelib.Approximation.Gaussian in
open Purelib.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Refine the retained cursor for the target, query its exact recipe ball and check the returned radius.

Success retains the refined cursor and checked ball; source and radius failures remain explicit replay failures. -/
def observe (control : IntegrationReplay.Control)
  (cursor : Cursor) (target : Fraction.Rational) :
    IntegrationReplay.QueryComputation (Except Data.CCL.Transducer.Replay.Failure (Cursor ×
      Enclosure.Ball.Data.BallData)) :=
  let next := cursor.refined control target
  (ball control next.recipe next.index).map fun result =>
    match result with
    | .error error => .error (.source error)
    | .ok ball => (Replay.Check.checkedBall next.index target ball).map (fun checked => (next, checked))
end Purelib.Approximation.Gaussian.Process.Recipe.Cursor

end
