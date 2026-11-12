module

import Purelib.Approximation.Gaussian.Observation.Observer.Source
public import Purelib.Approximation.Gaussian.Observation.Transcript
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

/-!
# Enclosure observer execution boundaries

The actual cached source run is compared with its source-free finite code
on empty, repeated, adaptive, iterated, exhausted and invalid-target runs,
and on explicit counters, data-dependent loops and nested calls.
The quantified theorem checks full execution transport for every source
and fuel, rather than only numerical equality at selected examples.
-/

namespace TestPurelib.Approximation.Gaussian.Observation.Enclosure

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Observation
open Purelib.Approximation.Gaussian.Observation.Observer

/-- Full first-order execution agreement holds at every original process and finite observer input. -/
theorem execution_agreement (process : Process) (initial : process.State)
    (instructions : List Instruction) (registers : List Value) (fuel : Nat) :
    let result := Source.continueExecution process initial [.block instructions] registers fuel
    Observer.execute [.block instructions] registers fuel result.continuation.code.interpret =
      result.execution.numerical :=
  (Source.continueExecution process initial [.block instructions] registers fuel).same_execution

/-- The positive initial request used by the concrete finite execution cases. -/
private def target : Request := Request.ofPositive 1 (by decide)

/-- A singleton-reading source whose actual displayed balls retain positive, request-dependent radii. -/
@[expose] public def looseProcess : Process where
  State := Request
  ball request :=
    { center := 0
      radiusSq := request.targetSq / 2
      radiusSq_nonneg := Fraction.Order.Field.div_nonneg_direct request.positive.le (by decide) }
  Possible _ value := value = 0
  witness _ := ⟨0, rfl⟩
  possible_inside := by
    intro state value equal
    cases equal
    unfold Enclosure.Ball.Contains
    rewrite [Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero]
    exact Fraction.Order.Field.div_nonneg_direct state.positive.le (by decide)
  refine _ epsilon positive := Request.ofPositive epsilon positive
  refine_persists := by intro _ _ _ _ possible; exact possible
  accurate _ _ positive := Fraction.Order.Field.half_lt_self positive
  centerBound := 0
  centerBound_nonneg := Fraction.Order.Basic.le_refl _
  center_bounded _ := by
    rewrite [Gaussian.Norm.Basic.normSq_zero]
    exact Fraction.Order.Basic.le_refl _

/-- Compare the actual complete numerical exchanges in their original order. -/
private def exchangesAgree : Computation.Query.Basic.Trace Question Enclosure.Ball →
    Computation.Query.Basic.Trace Question Enclosure.Ball → Bool
  | [], [] => true
  | left :: remainingLeft, right :: remainingRight =>
      decide (left.query = right.query) &&
        decide (left.reply.center.re = right.reply.center.re) &&
        decide (left.reply.center.im = right.reply.center.im) &&
        decide (left.reply.radiusSq = right.reply.radiusSq) &&
        exchangesAgree remainingLeft remainingRight
  | _, _ => false

/-- Compare a machine's actual outcome and ordered exchanges with its independently interpreted rational code. -/
private def checkControl (process : Process) (initial : process.State) (control : List Frame)
    (fuel expectedQueries : Nat) (expectedOutcome : Outcome → Bool)
    (expectedTargets : Option (List Fraction.Rational) := none)
    (expectedFresh : Option Nat := none) : IO Unit := do
  let result := Source.continueExecution process initial control [] fuel
  let fresh := expectedFresh.getD expectedQueries
  unless result.execution.requestCount == fresh && result.execution.sourceCalls == 2 + 3 * fresh do
    throw (IO.userError "source-call accounting changed setup, fresh refinement or cached recall work")
  unless result.execution.budget == fuel &&
      result.execution.simulation.usedFuel + result.execution.simulation.remainingFuel == fuel do
    throw (IO.userError "retained numerical transitions lost their original finite budget")
  unless result.execution.numerical.trace.length == expectedQueries do
    throw (IO.userError "unexpected original observer query count")
  unless expectedOutcome result.execution.numerical.value do
    throw (IO.userError "original observer returned an unexpected finite outcome")
  let replacement := Observer.execute control [] fuel result.continuation.code.interpret
  unless expectedOutcome replacement.value do
    throw (IO.userError "replacement changed the expected finite outcome")
  unless exchangesAgree result.execution.numerical.trace replacement.trace do
    throw (IO.userError "replacement changed an ordered numerical exchange")
  match expectedTargets with
  | none => pure ()
  | some targets =>
      unless decide (result.execution.numerical.trace.map (fun entry => entry.query.request.targetSq) = targets) do
        throw (IO.userError "machine changed its actual ordered numerical request targets")

/-- Keep each original first-order case on its unchanged block-frame fuel convention. -/
private def checkCase (code : List Instruction) (fuel expectedQueries : Nat)
    (expectedOutcome : Outcome → Bool) (expectedFresh : Option Nat := none) : IO Unit :=
  checkControl (Process.exact 0) () [.block code] fuel expectedQueries expectedOutcome none expectedFresh

/-- The actual reply's radius decides whether another refinement is needed. -/
private def radiusAbove (threshold : Fraction.Rational) : Expr :=
  .binary .less (.literal (.rational threshold)) (.unary .radiusSq (.variable 0))

/-- Each refinement target comes from the preceding actual reply, rather than a predetermined loop count. -/
private def nextRadius : Expr :=
  .binary .divide (.unary .radiusSq (.variable 0)) (.literal (.rational 2))

/-- A numerical while loop repeats only while its current observed radius exceeds the supplied threshold. -/
private def whileRefinement (threshold : Fraction.Rational) : List Instruction :=
  [.refine (.literal (.rational 1)), .while (radiusAbove threshold) [.refine nextRadius],
    .returnValue (.unary .radiusSq (.variable 0))]

/-- An explicit instruction counter expresses the same reply-dependent loop using finite jump targets. -/
private def counterRefinement (threshold : Fraction.Rational) : List Instruction :=
  [.refine (.literal (.rational 1)), .jumpIf (radiusAbove threshold) 2 4,
    .refine nextRadius, .jump 1, .returnValue (.unary .radiusSq (.variable 0))]

/-- Retain both caller boundaries and repeated recalls at the exact witnessed stop and a larger budget. -/
private def checkSavedCall : IO Unit := do
  let inner : List Instruction :=
    [.refine (.variable 0), .recall (.literal (.natural 0)), .recall (.literal (.natural 0)),
      .returnCall (.variable 0)]
  let outer : List Instruction := [.call inner (.variable 0), .returnCall (.variable 1)]
  let control : List Frame :=
    [.counter [.call outer (.literal (.rational 1)), .returnValue (.variable 0)] 0]
  let returned : Outcome → Bool := fun outcome => match outcome with
    | .returned (.rational value) => decide (value = 1)
    | _ => false
  checkControl (Process.exact 0) () control 40 3 returned (some [1, 1, 1]) (some 1)
  let stopped := Source.continueExecution (Process.exact 0) () control [] 8
  let later := Source.continueExecution (Process.exact 0) () control [] 40
  let pending := Source.execute (Process.exact 0) () control [] 7
  unless returned stopped.execution.outcome && returned later.execution.outcome do
    throw (IO.userError "nested return did not restore the caller's original rational argument")
  unless stopped.execution.simulation.usedFuel == 8 && stopped.execution.simulation.remainingFuel == 0 &&
      later.execution.simulation.usedFuel == 8 && later.execution.simulation.remainingFuel == 32 do
    throw (IO.userError "witnessed nested-call halt changed its exact consumed or unused fuel")
  unless later.execution.simulation.configurations.map (fun configuration => configuration.state.past.length) ==
      [0, 0, 0, 1, 2, 3, 3, 3, 3] do
    throw (IO.userError "retained configurations lost the chronological calls, recalls or returns")
  match later.execution.state.registers with
  | [.rational value] =>
      unless decide (value = 1) do
        throw (IO.userError "the final numerical registers retained a callee's local values")
  | _ => throw (IO.userError "the original caller's register boundary was not restored")
  match pending.outcome with
  | .exhausted => pure ()
  | _ => throw (IO.userError "the immediately preceding finite attempt was reported as stopped")
  unless pending.simulation.usedFuel == 7 && pending.simulation.remainingFuel == 0 &&
      pending.numerical.trace.length == 3 && pending.requestCount == 1 && pending.sourceCalls == 5 do
    throw (IO.userError "pre-stop exhaustion changed the saved recalls or charged them as fresh requests")
  unless exchangesAgree stopped.execution.numerical.trace later.execution.numerical.trace do
    throw (IO.userError "a larger budget changed the witnessed halt's ordered exchanges")
  let replacement := Observer.execute control [] 40 stopped.continuation.code.interpret
  unless returned replacement.value && exchangesAgree stopped.execution.numerical.trace replacement.trace do
    throw (IO.userError "the witnessed rational continuation changed execution at a larger budget")

/-- Check numerical loops with different query counts, explicit counters, nested calls and concrete stop boundaries. -/
private def checkMachines : IO Unit := do
  checkControl looseProcess target [.block (whileRefinement (1 / 8))] 40 2
    (fun outcome => match outcome with | .returned (.rational value) => decide (value = 1 / 8) | _ => false)
    (some [1, 1 / 4])
  checkControl looseProcess target [.block (whileRefinement (1 / 32))] 40 3
    (fun outcome => match outcome with | .returned (.rational value) => decide (value = 1 / 32) | _ => false)
    (some [1, 1 / 4, 1 / 16])
  checkControl looseProcess target [.counter (counterRefinement (1 / 8)) 0] 40 2
    (fun outcome => match outcome with | .returned (.rational value) => decide (value = 1 / 8) | _ => false)
    (some [1, 1 / 4])
  checkControl looseProcess target [.block (whileRefinement (1 / 8))] 6 2
    (fun outcome => match outcome with | .exhausted => true | _ => false) (some [1, 1 / 4])
  checkSavedCall
  checkCase [.store 3 (.literal (.natural 7)), .returnValue (.variable 3)] 4 0
    (fun outcome => match outcome with | .returned (.natural 7) => true | _ => false)
  checkCase [.jump 0] 2 0
    (fun outcome => match outcome with | .failed .missingCounter => true | _ => false)
  checkCase [.returnCall (.literal (.natural 0))] 2 0
    (fun outcome => match outcome with | .failed .missingCaller => true | _ => false)
  checkCase [.while (.literal (.natural 0)) []] 3 0
    (fun outcome => match outcome with | .failed (.branchType (.natural 0)) => true | _ => false)

/-- Check the actual positive-radius branch and its reply-dependent second target. -/
private def checkAdaptive : IO Unit := do
  let code := adaptiveEnclosureComparison target
  let result := Source.continueExecution looseProcess target [.block code] [] 16
  match result.execution.numerical.trace with
  | [first, second] =>
      unless decide (first.query.request.targetSq = (1 : Fraction.Rational)) &&
          decide (second.query.request.targetSq = (1 / 4 : Fraction.Rational)) do
        throw (IO.userError "the second target did not use the first positive observed radius")
  | _ => throw (IO.userError "adaptive source execution did not issue exactly two requests")
  match result.execution.numerical.value with
  | .returned (.bit true) => pure ()
  | _ => throw (IO.userError "adaptive source execution did not return its numerical comparison")
  let replacement := Observer.execute [.block code] [] 16 result.continuation.code.interpret
  unless exchangesAgree result.execution.numerical.trace replacement.trace do
    throw (IO.userError "adaptive replacement changed the complete saved numerical replies")
  match replacement.value with
  | .returned (.bit true) => pure ()
  | _ => throw (IO.userError "adaptive replacement changed the returned numerical comparison")

/-- Execute empty, repeated, adaptive, iterated and failed control with its expected finite outcomes. -/
public def run : IO Unit := do
  checkCase [.returnValue (.literal (.natural 7))] 3 0
    (fun outcome => match outcome with | .returned (.natural 7) => true | _ => false)
  checkCase (adaptiveEnclosureComparison target) 16 2
    (fun outcome => match outcome with | .returned (.bit true) => true | _ => false)
  checkCase [.refine (.literal (.rational 1)), .recall (.literal (.natural 0)),
    .returnValue (.variable 0)] 8 2
    (fun outcome => match outcome with | .returned (.ball _) => true | _ => false) (some 1)
  checkCase [.iterate (.literal (.natural 3)) [.refine (.literal (.rational 1))],
    .returnValue (.variable 0)] 30 3
    (fun outcome => match outcome with | .returned (.ball _) => true | _ => false)
  checkCase [.refine (.literal (.rational 1)), .returnValue (.variable 0)] 1 1
    (fun outcome => match outcome with | .exhausted => true | _ => false)
  checkCase [.refine (.literal (.rational 0)), .returnValue (.variable 0)] 4 0
    (fun outcome => match outcome with | .failed (.nonpositiveTarget _ _) => true | _ => false)
  checkCase [.iterate (.literal (.bit true)) [], .returnValue (.literal (.natural 0))] 4 0
    (fun outcome => match outcome with | .failed (.countType (.bit true)) => true | _ => false)
  checkCase [.recall (.literal (.natural 0)), .returnValue (.literal (.natural 0))] 4 0
    (fun outcome => match outcome with | .failed (.missingRecall 0) => true | _ => false)
  checkAdaptive
  checkMachines
  IO.print "enclosure observer: eighteen first-order and coded-machine execution boundaries passed\n"

end TestPurelib.Approximation.Gaussian.Observation.Enclosure
