module

-- The exposed original main body retains its original printing owner.
public import Purelib.System.IO

-- Public JSON APIs and exposed wire operations retain the owned codec path.
public import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.Json.Printer
import Purelib.Data.String.Basic
public import Purelib.Examples.Approximation.Queries.Adaptive.WorkedExamples
import Purelib.Computation.Query.Basic

import Init.Prelude
import Init.System.IO
import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.Replay

open Purelib.Computation.Query.Basic

open Purelib.Examples.Approximation.Queries.Adaptive

open Purelib.Data (Json)
open scoped Purelib.Data.String
open Purelib.Data.Json (toJson)

public section

/-! Reproduce the finite adaptive query regression from compiled declarations. -/

/-- Report the adaptive query trace, computed value and exact replay outcome as JSON. -/
@[expose] def main : IO Unit := do
  let questions := (WorkedExamples.adaptive.run WorkedExamples.naturalOracle).trace.map
    Exchange.query
  let value := (WorkedExamples.adaptive.run WorkedExamples.naturalOracle).value
  let replay := WorkedExamples.adaptive.replayExact [⟨0, 1⟩, ⟨2, 3⟩, ⟨0, 1⟩]
  let replayJson := match replay with
    | .ok answer => Json.mkObj [("kind", toJson "ok"), ("value", toJson answer)]
    | .error _ => Json.mkObj [("kind", toJson "error")]
  Purelib.System.IO.println (Json.mkObj [
    ("module", toJson "Purelib.Examples.Approximation.Queries.Adaptive.WorkedExamples"),
    ("questions", toJson questions),
    ("value", toJson value),
    ("replay", replayJson)]).compress
