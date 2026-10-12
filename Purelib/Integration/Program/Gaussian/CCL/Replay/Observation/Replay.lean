module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.CertifiedProgram
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.Replay
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record

/-!
# Finite transcript replay

The original request computation consumes an ordered finite transcript.
Its outcomes distinguish query-protocol mismatches from checked integration
or machine failures, while exact retained records replay to their original values.
-/

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Transcript

-- The established stream and observation replay namespaces identify distinct
-- operations; preserve both original public paths in this owner.

open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Integration.CertifiedProgram (Request InvalidRequest)
open Purelib.Integration.Program.Gaussian.CCL.Replay
open Purelib.Computation.Query
open Purelib.Data.CCL.Transducer
open Purelib.Approximation.Gaussian
open Purelib.Integration.Program.Gaussian.CCL.Replay (Observation)

@[expose] public section

set_option genInjectivity false in
/-- An explicit transcript mismatch or checked integration replay failure.

Each original constructor retains its corresponding protocol or checked
numerical error, with no successful observation fabricated for either case. -/
inductive ReplayFailure where
  /-- The retained transcript violates the exact query replay protocol. -/ | transcript (error : Replay.ReplayError Nat)
  /-- The checked replay computation reports an explicit integration or transducer failure. -/ | invalid (error :
    Data.CCL.Transducer.Replay.Failure)
deriving DecidableEq

constructive_injectivity ReplayFailure

end

/-- Replay the exact observation request against the supplied transcript and report any transcript or checked-source
failure.

The same complete observation computation consumes the ordered
transcript; transcript failures and checked numerical failures remain distinct. -/
@[expose] public def replay (control : Control) (request : Request) (count : Nat) (trace : Trace) :
    Except ReplayFailure Observation :=
  match (Observation.Basic.computation control request count).replayExact trace with
  | .error error => .error (.transcript error)
  | .ok (.error error) => .error (.invalid error)
  | .ok (.ok observation) => .ok observation

/-- The original recorded transcript replays to its exact retained observation.

The original record equations identify both the successful value and
exact ordered transcript consumed by the retained replay computation. -/
public theorem observation_replay (program : CachedProgram) (request : Request) (count : Nat) :
    replay (control program) request count (Observation.Record.record program request count).trace =
      .ok (Observation.Record.record program request count).observation := by
  unfold replay
  rw [(Observation.Record.record program request count).trace_eq, Computation.Query.Protocol.replayExact_run,
    (Observation.Record.record program request count).value_eq]

/-- An oracle agreeing with the exact retained replies produces the same observation value and trace.

Agreement is required on the exact recorded exchanges. The original
adaptive computation then retains its complete value and ordered trace. -/
public theorem run_of_answers (control : Control) (request : Request) (count : Nat)
    (first second : Nat → CachedModel)
    (agrees : Basic.Answers second ((Observation.Basic.computation control request count).run first).trace) :
    (Observation.Basic.computation control request count).run second = (Observation.Basic.computation control request
      count).run first :=
  (Observation.Basic.computation control request count).run_of_answers first second agrees

end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Transcript
