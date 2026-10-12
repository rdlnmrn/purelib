module
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.List.Control
public import Purelib.Data.List.ToString
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples
public import Purelib.Integration.Exponential.Equivalence.Policy
import Purelib.Integration.Exponential.Geometry.Policy
import Purelib.Integration.Exponential.Program
import Purelib.Integration.Exponential.Selection
import Purelib.Integration.Exponential.Selection.Cache
import Purelib.Integration.Polynomial.Gaussian.Partition.Request
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume
public import Purelib.Integration.Program.Gaussian.Cached.Schedule
import Purelib.Integration.Program.Gaussian.Exact
import Purelib.Polynomial.Ascending.Gaussian.Basic

import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Init.Data.Int.Basic
import Init.Prelude
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Replay
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Exponential.Polynomial.Source
import Purelib.Integration.Partition.Interval
import Purelib.Integration.Partition.QuadraticWeight.Cache
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Integration.Polynomial.Gaussian.Partition.Source
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

open Purelib.Integration

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.List

open Purelib

open Purelib.CCL.Progressive

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Nat.Schedule

open Purelib.Data.Rat

open Purelib.Examples.Integration.Polynomial.Gaussian.Partition

open Purelib.Integration.Exponential

open Purelib.Integration.Exponential.Equivalence

open Purelib.Integration.Exponential.Geometry

open Purelib.Integration.Exponential.Selection.Cache

open Purelib.Integration.Polynomial.Gaussian.Partition.Request

open Purelib.Integration.Program.Gaussian.Basic

open Purelib.Integration.Program.Gaussian.CCL.Replay

open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume

open Purelib.Integration.Program.Gaussian.Cached

open Purelib.Polynomial

public section

/-!
Certificate-free native regressions for complete integration observations.
No Riemann module or generated certificate bank is imported.  Every run checks
the real controller, source-free replay, requested enclosure, and continuation
from a retained numerical machine.  Different presentations are compared by
finite numerical bounds, never by assuming equal raw prefixes.

Build `integration_replay_regression` for the short native iteration cycle.
Run diagnostic executions with an explicit SIGKILL timeout and systemd memory
bound, as required by AGENTS.md.  This supplements the universal Lean proofs;
it does not replace the build or axiom gates.
-/

namespace IntegrationReplayRegression

open Purelib.Integration.CertifiedProgram (Request InvalidRequest)

open Purelib.CCL.Progressive.IntegrationReplay
open _root_.Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Transcript (replay)

/-- Print and flush one integration replay regression message. -/
@[expose] def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Fail the regression when the supplied Boolean condition is false. -/
@[expose] def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Compare the complete numerical machine and selected enclosure data of two observations. -/
@[expose] def sameObservation (left right : Integration.Program.Gaussian.CCL.Replay.Observation) : Bool :=
  left.machine == right.machine && left.selected.index == right.selected.index &&
    left.selected.sample == right.selected.sample &&
    left.selected.allowance == right.selected.allowance &&
    left.selected.ball.center == right.selected.ball.center &&
    left.selected.ball.radiusSq == right.selected.ball.radiusSq

/-- Every request and numerical reply field consumed by the controller. The original complete model remains in each
typed, certified trace entry. -/
@[expose] def numericTrace (trace : Trace) :=
  trace.map fun exchange =>
    (exchange.query, exchange.reply.sample, exchange.reply.allowance)

/-- Report whether source-free replay rejects the supplied finite transcript. -/
@[expose] def rejects (metadata : Control) (request : Request) (count : Nat) (trace : Trace) : Bool :=
  match replay metadata request count trace with
  | .error _ => true
  | .ok _ => false

/-- Check recording, source-free replay and resumption for one finite integration request.

Verify exact observation data, enclosure bounds, query ordering and multiplicity, then reject missing, reordered,
corrupted or unused replies. -/
@[expose] def runCase (label : String) (program : CachedProgram) (request : Request)
    (count split : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  report s!"{label}: current={request.current}, bits={count}, split={split}"
  check (split ≤ count) "invalid test split"
  let metadata := control program
  let recorded := Record.record program request count
  let replayed ← match replay metadata request count recorded.trace with
    | .error _ => throw (IO.userError s!"{label}: generated transcript rejected")
    | .ok observation => pure observation
  check (sameObservation replayed recorded.observation) "replay changed observation data"
  check (replayed.word.length == count) "wrong output length"
  check (replayed.selected.index ≥ request.current) "source cursor went backwards"
  check (replayed.selected.ball.radiusSq < request.target) "enclosure exceeds requested error"
  check (replayed.selected.allowance < request.target) "allowance exceeds requested error"
  let direct := Advance.advance (refinedName program request).machine count
  check (replayed.word == direct.emitted) "recorded prefix differs from the original transducer"
  match recorded.trace with
  | [] => throw (IO.userError "outer enclosure query is absent")
  | first :: rest =>
      check (rejects metadata request count []) "missing log accepted"
      check (rejects metadata request count (recorded.trace.dropLast)) "truncated log accepted"
      check (rejects metadata request count (recorded.trace ++ [first])) "extra reply accepted"
      check (rejects metadata request count (⟨first.query + 1, first.reply⟩ :: rest))
        "changed request key accepted"
      match rest with
      | second :: tail =>
          if first.query != second.query then
            check (rejects metadata request count (second :: first :: tail)) "reordered requests accepted"
      | [] => pure ()
  let earlier := Record.record program request split
  let continued := earlier.resume (count - split)
  check (sameObservation continued.observation recorded.observation)
    "resuming changed the complete observation"
  check (sameObservation continued.recorded.observation recorded.observation)
    "joined receipt changed the complete observation"
  check (numericTrace (earlier.trace ++ continued.trace) == numericTrace recorded.trace)
    "resuming changed query order, multiplicity or numerical replies"
  match IntegrationReplay.replayResume metadata earlier.observation (count - split) continued.trace with
  | .ok replayedObservation =>
      check (sameObservation replayedObservation continued.observation)
        "resumed source-free replay changed the observation"
  | _ => throw (IO.userError "resumed trace did not replay")
  let unchanged := earlier.resume 0
  check (sameObservation unchanged.observation earlier.observation && unchanged.trace.isEmpty)
    "zero-bit resume changed the observation or queried the source"
  match earlier.trace with
  | first :: _ =>
      match IntegrationReplay.replayResume metadata earlier.observation 0 [first] with
      | .error (.transcript (.trailing _)) => pure ()
      | _ => throw (IO.userError "zero-bit resume did not reject an unused reply")
  | [] => throw (IO.userError "saved enclosure query is absent")
  let finish ← IO.monoMsNow
  report
    s!"{label}: passed in {finish - start} ms; word={replayed.word}, queries={recorded.trace.map (·.query)}, saved \
      pending bits={earlier.observation.machine.pending.length}"

/-- The cached exact integration program for a constant Gaussian polynomial on the unit segment. -/
@[expose] def exact (value : Gaussian) : CachedProgram :=
  (RefinementProgram.exactPolynomial 0 1 (Ascending.Gaussian.Basic.constant value)).certifiedView.program

/-- The retained repeated-path polynomial program with fixed or alternating scheduled cuts. -/
@[expose] def polynomial (varying : Bool) : CachedProgram :=
  let source := WorkedExamples.repeatedPath
  if varying then
    Schedule.reindexCached
      (IntegrationPrograms.polynomialProgram source
        WorkedExamples.alternatingPolicy) ⟨3, 4⟩
  else IntegrationPrograms.polynomialProgram source
    (.fixed (CutRequest.every
      [1, 1 / 2, 0, 1 / 2, -1, 2] source))

/-- The exponential integration policy with a retained cut at one third. -/
@[expose] def fixedPolicy : Exponential.Geometry.Policy :=
  Policy.fixedCuts [1 / 3]

/-- The exponential policy alternating uniform refinement and a retained cut at one quarter. -/
@[expose] def varyingPolicy : Exponential.Geometry.Policy :=
  .alternating (.uniform 1 1) (Policy.fixedCuts [1 / 4])

/-- The exponential integration policy with six closely spaced dyadic cuts. -/
@[expose] def unevenPolicy : Exponential.Geometry.Policy :=
  Policy.fixedCuts
    [1 / 1024, 2 / 1024, 3 / 1024, 4 / 1024, 5 / 1024, 6 / 1024]

/-- Construct the exponential integration program with the requested policy and optional shifted presentation. -/
@[expose] def exponential (policy : Exponential.Geometry.Policy)
    (shifted : Bool) : CachedProgram :=
  Program.program policy (if shifted then ⟨2, 1⟩ else ⟨0, 0⟩)
    (if shifted then 1 else 0)

/-- Exercise empty allocations, first and later hits, repeated reads and a miss beyond a short selector cache. Canonical
selection is the independent specification; no generated geometry or certificate bank is involved. -/
@[expose] def selectionCaches : IO Unit := do
  for (label, policy) in [("fixed", fixedPolicy), ("varying", varyingPolicy), ("uneven", unevenPolicy)] do
    let schedule : Data.Nat.Schedule.PositiveStride := ⟨2, 1⟩
    for (size, index) in [(0, 0), (0, 2), (4, 0), (4, 3), (2, 3)] do
      let entries := SelectionCache.buildPrefix size
        (SelectionCache.first policy schedule)
      let observed := SelectionCache.read policy schedule index entries
      let repeated := SelectionCache.read policy schedule index entries
      let expected := Selection.selection policy schedule index
      let profile := fun selected : Integration.Exponential.Selection index =>
        (selected.depth, selected.geometry.factor, selected.geometry.partition.cuts,
          selected.geometry.partition.intervals.map fun interval => (interval.start, interval.finish))
      check (profile observed == profile expected && profile repeated == profile expected)
        "selector cache changed degree, geometry or amplification"
      report s!"selection cache/{label}: size={size}, index={index}; exact and repeated reads passed"

/-- Execute the generated synchronizer and then compare independently later samples. The all-later-pairs theorem remains
the universal guarantee. -/
@[expose] def compareExponential : IO Unit := do
  let agreement := Policy.programs_equivalent
    fixedPolicy varyingPolicy ⟨0, 0⟩ ⟨2, 1⟩ 0 1
  let left := exponential fixedPolicy false
  let right := exponential varyingPolicy true
  check ((left.stage 0).sample != (right.stage 0).sample) "coarse samples unexpectedly equal"
  for denominator in [1, 100, 10000] do
    let target := 1 / Fraction.Cast.fromInt (Int.ofNat denominator)
    if positive : 0 < target then
      let comparison := agreement.compare 1 2 target positive
      for extra in [0, 1, 3] do
        let first := (left.stage (comparison.leftIndex + extra)).sample
        let second := (right.stage (comparison.rightIndex + extra + 1)).sample
        check (Data.Gaussian.Norm.Basic.normSq (first - second) < target)
          "independently later exponential samples exceed the synchronized bound"
      report s!"exponential comparison: 1/{denominator} passed at ({comparison.leftIndex}, {comparison.rightIndex})"
    else throw (IO.userError "invalid comparison test target")

/-- Run the finite selector-cache, exact, polynomial, exponential and synchronized-comparison regressions. -/
@[expose] def main : IO Unit := do
  selectionCaches
  let request : Request := ⟨0, 1, by decide⟩
  runCase "empty prefix" (exact 0) request 0 0
  runCase "zero/low chart" (exact 0) request 8 3
  runCase "one/buffered resume" (exact 1) request 10 1
  runCase "inverse chart" (exact ⟨3 / 2, 0⟩) request 10 6
  runCase "polynomial/fixed" (polynomial false) request 8 1
  runCase "polynomial/scheduled" (polynomial true) ⟨3, 1, by decide⟩ 8 4
  runCase "exponential/fixed" (exponential fixedPolicy false) request 8 1
  runCase "exponential/varying" (exponential varyingPolicy true) request 8 4
  runCase "exponential/uneven" (exponential unevenPolicy false) ⟨3, 1 / 100, by decide +kernel⟩ 8 3
  compareExponential
  report "All certificate-free integration replay regressions passed."

end IntegrationReplayRegression

/-- Run the complete integration replay regression suite or only selector-cache checks. -/
@[expose] def main (arguments : List String) : IO Unit :=
  match arguments with
  | [] => IntegrationReplayRegression.main
  | ["selections"] => IntegrationReplayRegression.selectionCaches
  | _ => throw (IO.userError "usage: integration_replay_regression [selections]")
