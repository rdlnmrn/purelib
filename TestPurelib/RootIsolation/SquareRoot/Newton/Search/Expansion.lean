module

import Purelib.RootIsolation.SquareRoot.Newton.Search.Expansion
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Complete root search with nested residual and occurrence checks -/

namespace TestPurelib.RootIsolation.SquareRoot.Newton.Search.Expansion

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Computation.Query
open Purelib.RootIsolation.SquareRoot.Newton.Search

/-- Consume the actual polynomial-root and positive-imaginary occurrence checks at one original proposal. -/
private def handler (point : Canonical) : Protocol (Canonical × Bool) Bool Bool :=
  (Protocol.query (point, false)).bind fun root =>
    (Protocol.query (point, true)).map fun occurrence => root && occurrence

/-- Execute the original proposal through two retained checks and replay the complete nested query boundary. -/
public def run : IO Unit := do
  let oracle : Canonical × Bool → Bool := fun question =>
    if question.2 then decide (0 < question.1.im) else decide (question.1 * question.1 = (⟨0, 2⟩ : Canonical))
  let computation := Observation.Expansion.computation handler ⟨0, 2⟩ 1 (1 / 4) ⟨1, 1⟩
  let original := computation.run oracle
  unless decide (original.value.value = some ⟨1, 1⟩) &&
      original.value.trace.length == 1 && original.trace.length == 2 do
    throw (IO.userError "expanded root search lost its actual residual or occurrence check")
  let changed := computation.run (Boundary.Trace.overlay original.trace (fun _ => false))
  unless decide (changed.value.value = original.value.value) &&
      decide (changed.trace.map (fun entry => (entry.query, entry.reply)) =
        original.trace.map (fun entry => (entry.query, entry.reply))) do
    throw (IO.userError "outside evaluator replies changed the complete expanded root search")
  match computation.replayExact original.trace with
  | .error _ => throw (IO.userError "expanded root search rejected its exact nested check transcript")
  | .ok replayed =>
      unless decide (replayed.value = original.value.value) && replayed.trace.length == 1 do
        throw (IO.userError "expanded root replay lost the original result or outer callback trace")
  let rejected := computation.run (fun _ => false)
  unless rejected.value.value.isNone do
    throw (IO.userError "changed consumed residual checks did not reject the actual proposal")
  IO.print "composed root search: residual/occurrence requests, both logs and exact replay/erasure passed\n"

end TestPurelib.RootIsolation.SquareRoot.Newton.Search.Expansion
