module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume

import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.CertifiedProgram
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
public import Purelib.Integration.CCL.Program
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.List.Basic
import Purelib.Computation.Query.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Integration.Program.Gaussian.Cached.Basic

/-!
# Complete observation contracts

The retained original program, request, bit count and record index the
complete replay, accuracy, prefix and cursor-semantics certificate. Output
comparison retains both original programs and their separate observation contracts.
-/

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Integration.CertifiedProgram (Request InvalidRequest)
open Purelib.Integration.Program.Gaussian.CCL.Replay
open Purelib.Computation.Query
open Purelib.Data.CCL.Transducer
open Purelib.Approximation.Gaussian

universe u

public section

/-- Certified replay, accuracy and exact machine semantics for one original retained observation record.

The contract binds the target, emitted length, future sample containment, every original source reply and extension of
the retained prefix. -/
structure Contract (program : CachedProgram) (request : Request) (count : Nat)
    (recorded : Observation.Record.Recorded program request count) : Prop where
  /-- The retained transcript replays to the exact recorded observation. -/ replay : Transcript.replay (control
    program) request count recorded.trace = .ok recorded.observation
  /-- The exact selected ball radius is strictly below the original target. -/ accurate :
    recorded.observation.selected.ball.radiusSq < request.target
  /-- The retained selected model allowance is strictly below the original target. -/ allowance :
    recorded.observation.selected.allowance < request.target
  /-- The retained emitted word has exactly the original requested length. -/ length : recorded.observation.word.length
    = count
  /-- The recorded word equals the original refined-name machine's emitted prefix. -/ prefix_eq :
    recorded.observation.word =
    (Machine.Advance.advance (refinedName program request).machine count).emitted
  /-- The exact selected ball contains every original program sample at a later retained index. -/ contains_later : ∀
    {later : Nat}, selectedIndex (control program) request ≤ later →
    recorded.observation.selected.ball.Contains (program.stage later).sample
  /-- An actual machine emits the recorded word and retains exact original process-cursor semantics. -/ exact_cursor : ∃
    actual : Data.CCL.Transducer.Machine,
    actual.emitted = recorded.observation.word ∧
    Machine.Semantics.Basic.ExactCursor (refinedName program request).process
      (refinedName program request).state actual
  /-- Every recorded reply equals the original program stage at its exact query index. -/ source_reply : ∀ exchange ∈
    recorded.trace, exchange.reply = program.stage exchange.query
  /-- Every longer original observation retains the recorded word as a prefix. -/ prefix_extends : ∀ extra,
    recorded.observation.word.IsPrefix (Observation.Record.record program request (count + extra)).observation.word

end

namespace Contract

/-- The exact original observation record satisfies its retained replay, accuracy and machine-semantics contract.

Each contract field uses the original retained observation record,
its exact transcript and the same program, request and bit count. -/
public theorem observation_contract (program : CachedProgram) (request : Request) (count : Nat) :
    Contract program request count (Observation.Record.record program request count) where
  replay := Transcript.observation_replay program request count
  accurate := Observation.Record.recorded_accurate program request count
  allowance := Observation.Record.recorded_allowance program request count
  length := Observation.Record.recorded_length program request count
  prefix_eq := Observation.Record.recorded_prefix program request count
  contains_later := Observation.Record.recorded_contains_later program request count
  exact_cursor := Observation.Record.recorded_exactCursor program request count
  source_reply := Observation.Record.recorded_reply program request count
  prefix_extends := Observation.Record.recorded_extends program request count

end Contract

namespace Contract

/-- The combined resumed record satisfies the original request's contract at the full extended bit count.

The exact resumed-record equation transports the unchanged original
contract to the same extended bit count and combined transcript. -/
public theorem resumed_contract {program : CachedProgram} {request : Request} {count extra : Nat}
    {saved : Observation.Record.Recorded program request count} (resumed : Observation.Resume.IntegrationReplay.Resumed
      saved extra) :
    Contract program request (count + extra) resumed.recorded := by
  rw [resumed.recorded_eq]
  exact observation_contract program request (count + extra)

end Contract

@[expose] public section

namespace Contract

set_option genInjectivity false in
/-- Equivalent original program output names with separate certified observation contracts for both retained programs.

The two programs and their exact records remain distinct; output-name equivalence does not assert equality of their
emitted words. -/
structure Comparison (left right : CachedProgram) (request : Request) (count : Nat) where
  /-- The exact retained output names of the two original programs are equivalent. -/ outputs :
    Equivalence.NamedEquivalent left.output.name right.output.name
  /-- The original left program's retained observation contract. -/ left_observation : Contract left request count
    (Observation.Record.record left request count)
  /-- The original right program's retained observation contract. -/ right_observation : Contract right request count
    (Observation.Record.record right request count)

constructive_injectivity Comparison

end Contract

end

namespace Contract

/-- Retain the supplied output equivalence alongside both original programs' exact observation contracts.

The two original programs and their records remain separate. The
supplied output equivalence is retained alongside both certified contracts. -/
@[expose] public def comparison (left right : CachedProgram) (request : Request) (count : Nat)
    (equivalent : Equivalence.NamedEquivalent left.output.name right.output.name) :
    Comparison left right request count :=
  ⟨equivalent, observation_contract left request count, observation_contract right request count⟩

end Contract

end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation
