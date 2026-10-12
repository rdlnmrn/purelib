module
import Purelib.Data.Gaussian.Norm.Comparison
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observe
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data.Bounds
import Purelib.Approximation.Gaussian.Process.Normalization.Data
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
public import Purelib.Approximation.Gaussian.Process.Recipe.Inverse
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.CCL.Encoding.Padding.Residual
public import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Replay.Emission
public import Purelib.Data.CCL.Transducer.Replay.Emission.Step
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.CCL.Transducer.Replay.Mode
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Computation.Query.Computation

open Purelib.Approximation.Gaussian.Process.Recipe (Cursor)
open Purelib.Data.CCL.Transducer.Replay (Failure)

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

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Controller

section
open Purelib.Approximation.Gaussian
open Purelib.CCL.Progressive
section
open Purelib.Data.CCL.Transducer
/-- Observe the original cursor at the initial radius budget and construct its checked initial emission. -/
def initialStep (control : IntegrationReplay.Control)
  (cursor : Cursor) : IntegrationReplay.QueryComputation (Except
      Failure
  Data.CCL.Transducer.Replay.Emission) :=
  (Cursor.observe control cursor Emission.Initial.Budget.initialRadiusSq).map fun
      result =>
    result.map fun (next, ball) => Replay.Emission.Step.initialAfter control next ball

/-- Observe the retained low-mode cursor at the initial budget and continue its exact retained count. -/
def lowStep (control : IntegrationReplay.Control)
  (count : Nat) (cursor : Cursor) :
    IntegrationReplay.QueryComputation (Except Failure Data.CCL.Transducer.Replay.Emission)
      :=
  (Cursor.observe control cursor Emission.Initial.Budget.initialRadiusSq).map fun
      result =>
    result.bind fun (next, ball) => Replay.Emission.Step.lowAfter control count next ball

/-- Observe the original loop cursor at its retained domain target and construct the next checked emission. -/
def loopStep (control : IntegrationReplay.Control)
  (kind : Mode.Basic.RegularKind) (count : Nat) (cursor : Cursor) (domain :
  Process.Normalization.Data.Domain) :
    IntegrationReplay.QueryComputation (Except Failure Data.CCL.Transducer.Replay.Emission)
      :=
  (Cursor.observe control cursor domain.target).map fun result =>
    result.bind fun (next, ball) => Replay.Emission.Step.loopAfter control kind count next ball

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Program.Gaussian in
/-- Continue the retained residual mode by padding a sufficiently small ball or entering the exact inverse loop.

The padding branch emits one true bit and retains its updated count and upper bound; the inverse branch uses the
observed center and radius to prepare the lower estimate. -/
def residualAfter (control :
  IntegrationReplay.Control) (count : Nat) (upper : Fraction.Rational)
    (cursor : Cursor) (ball : Enclosure.Ball.Data.BallData) :
        IntegrationReplay.QueryComputation
      (Except Failure Data.CCL.Transducer.Replay.Emission) :=
  if Enclosure.Ball.Data.Bounds.smallUpper ball < Padding.Residual.paddingTarget (count + 1) then
    .pure (.ok ⟨[true], .residual cursor (count + 1) (Enclosure.Ball.Data.Bounds.smallUpper ball)⟩)
  else
    let lowerSq := Basic.Canonical.Norm.Comparison.normSqFromReduced ball.center / 2 - ball.radiusSq
    loopStep control .loop count (Process.Recipe.Inverse.inverseCursor control cursor lowerSq
      count) (Process.Normalization.Data.inverseDomain count upper)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
open Purelib.Integration.Program.Gaussian in
/-- Observe the retained residual cursor at one sixth of the next padding target, preserving explicit source failures.
-/
def residualStep (control : IntegrationReplay.Control)
  (cursor : Cursor) (count : Nat) (upper : Fraction.Rational) :
    IntegrationReplay.QueryComputation (Except Failure Data.CCL.Transducer.Replay.Emission)
      :=
  (Cursor.observe control cursor (Padding.Residual.paddingTarget (count + 1) /
      6)).bind fun result
    =>
    match result with
    | .error error => .pure (.error error)
    | .ok (next, ball) => residualAfter control count upper next ball

end

open Purelib.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian in
/-- Dispatch one replay-controller step from the exact retained mode, cursor, count and normalization domain. -/
def step (control : IntegrationReplay.Control) :
  Data.CCL.Transducer.Replay.Mode → IntegrationReplay.QueryComputation (Except Failure
    Data.CCL.Transducer.Replay.Emission)
  | .initial cursor => initialStep control cursor
  | .low count cursor => lowStep control count cursor
  | .loop kind count cursor domain => loopStep control kind count cursor domain
  | .residual cursor count upper => residualStep control cursor count upper
end Purelib.Integration.Program.Gaussian.CCL.Replay.Controller

end
