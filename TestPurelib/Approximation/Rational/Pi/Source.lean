module
import Purelib.Integration.Partition.Unit.Occurrence
import Purelib.Integration.Partition.Unit.Check
meta import Purelib.Integration.Partition.Unit.Occurrence
meta import Purelib.Integration.Partition.Unit.Check

import Purelib.Examples.Approximation.Rational.Pi.Source
import Purelib.Approximation.Rational.Pi.Polygon
import Purelib.Approximation.Rational.Pi.Source.Presentation
import Purelib.Approximation.Gaussian.Pi.Integral.Presentation
meta import Purelib.Approximation.Gaussian.Pi.Integral.Presentation
meta import Purelib.Approximation.Rational.Pi.Source.Presentation
meta import Purelib.Integration.Cell.Source.Comparison
import Purelib.Approximation.AccuracyRequest.Presentation
import Purelib.Data.Rat.Interval.Presentation
import Purelib.Integration.Cell.Refinement.Presentation
meta import Purelib.Integration.Cell.Refinement.Presentation
import Purelib.Integration.Cell.Source.Refinement
meta import Purelib.Integration.Cell.Source.Refinement
meta import Purelib.Approximation.AccuracyRequest.Presentation
public meta import Purelib.Examples.Approximation.Rational.Pi.Source
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import TestPurelib.Geometry.Gaussian.UnitCircle.Polygon
meta import Purelib.Geometry.Gaussian.UnitCircle.Polygon.Presentation
meta import Purelib.Geometry.Gaussian.UnitCircle.Polygon

namespace TestPurelib.Approximation.Rational.Pi.Source

open Purelib.Approximation.Rational.Pi
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Pi
open Purelib.Approximation.Gaussian.Process
open Purelib.Examples.Approximation.Rational.Pi
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Interval.Presentation
open Purelib.Geometry.Gaussian
open Purelib.Integration
open Purelib.Integration.Partition
open Purelib.Integration.SourceFrontier
open Purelib.Approximation.Rational.Pi.Source
open Presentation.History

/-- info: (true, true) -/
#guard_msgs in
#eval ( (match UnitCircle.Polygon.Presentation.Ordered.check (UnitCircle.Polygon.vertices 0) with
    | .accepted _ => true | .notUnit _ _ => false),
  (match UnitCircle.Polygon.Presentation.Ordered.check [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩] with
    | .accepted _ => false | .notUnit index _ => index.val == 1))

example (state : Source.boundProcess.State) := Integral.named_observations state

example (index : Nat) := Integral.sample_eq index

example (state : Source.boundProcess.State) (target : Fraction.Rational) (positive : 0 < target) :=
  Integral.check_refinement state target positive

private def intervalDisplay : Interval.Presentation.Display := ⟨(0, 1), by decide⟩

private def singletonDisplay : Interval.Presentation.Display := ⟨(1, 1), by decide⟩

example : (match Interval.Presentation.check (0, 1) with
    | .valid _ => true | .reversed _ => false) = true := by decide

example : (match Interval.Presentation.check (1, 1) with
    | .valid _ => true | .reversed _ => false) = true := by decide

example : (match Interval.Presentation.check (1, 0) with
    | .valid _ => false | .reversed _ => true) = true := by decide

example : (match Interval.Presentation.compare intervalDisplay intervalDisplay with
    | .isTrue _ => true | .isFalse _ => false) = true := by decide

example : (match Interval.Presentation.compare intervalDisplay singletonDisplay with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example (bound : Rat.Interval) : Interval.Presentation.read (Interval.Presentation.quote bound) = bound :=
  Interval.Presentation.read_quote bound

example (display : Interval.Presentation.Display) :
    Interval.Presentation.quote (Interval.Presentation.read display) = display :=
  Interval.Presentation.quote_read display

example (left right : Interval.Presentation.Display) :
    Interval.Presentation.Same left right ↔ Interval.Presentation.read left = Interval.Presentation.read right :=
  Interval.Presentation.same_iff_read_eq left right

example (lower upper : Fraction.Rational) (first second : lower ≤ upper) :
    (⟨lower, upper, first⟩ : Rat.Interval) = ⟨lower, upper, second⟩ := Interval.ext rfl rfl

example (state : Source.boundProcess.State) :
    Interval.Presentation.read (Interval.Presentation.quote (Source.boundProcess.bound state)) =
      Source.boundProcess.bound state :=
  Interval.Presentation.read_quote _

example (state : Source.boundProcess.State) :
    (Interval.Presentation.read (Interval.Presentation.quote (Source.boundProcess.bound state))).midpoint =
      Integral.answer state := by
  rw [Interval.Presentation.read_quote]
  rfl

example (bounds : Interval.Bounds) :
    Bounds.read (Bounds.quote bounds) = bounds :=
  Bounds.read_quote bounds

example (lower upper : Fraction.Rational) (first second : lower ≤ upper) :
    (⟨lower, upper, first⟩ : Interval.Bounds) = ⟨lower, upper, second⟩ := by
  rfl

example : Bounds.read intervalDisplay ≠ Bounds.read singletonDisplay := by
  intro equal
  have same := (Bounds.same_iff_read_eq _ _).mpr equal
  have : (0 : Fraction.Rational) = 1 := congrArg Prod.fst same
  exact (by decide : (0 : Fraction.Rational) ≠ 1) this

example (left right : Interval.Presentation.Display) :
    Interval.Presentation.Same left right ↔
      Bounds.read left = Bounds.read right :=
  Bounds.same_iff_read_eq left right

example (state : Source.boundProcess.State) :
    Interval.Bisection.midpoint (Bounds.read
        (Bounds.quote
          ⟨(Source.boundProcess.bound state).lower, (Source.boundProcess.bound state).upper,
            (Source.boundProcess.bound state).valid⟩)) = Integral.answer state := by
  rw [Bounds.read_quote]
  rfl

private def displayedRequest : AccuracyRequest.Presentation.Display := ⟨16, by decide⟩

private def otherRequest : AccuracyRequest.Presentation.Display := ⟨8, by decide⟩

example : (match AccuracyRequest.Presentation.check 16 with
    | .valid _ => true | .nonpositive _ => false) = true := by decide

example : (match AccuracyRequest.Presentation.check 0 with
    | .valid _ => false | .nonpositive _ => true) = true := by decide

example : (match AccuracyRequest.Presentation.check (-1) with
    | .valid _ => false | .nonpositive _ => true) = true := by decide

example : (match AccuracyRequest.Presentation.compare displayedRequest displayedRequest with
    | .isTrue _ => true | .isFalse _ => false) = true := by decide

example : (match AccuracyRequest.Presentation.compare displayedRequest otherRequest with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example (request : AccuracyRequest) :
    AccuracyRequest.Presentation.read (AccuracyRequest.Presentation.quote request) = request :=
  AccuracyRequest.Presentation.read_quote request

example (display : AccuracyRequest.Presentation.Display) :
    AccuracyRequest.Presentation.quote (AccuracyRequest.Presentation.read display) = display :=
  AccuracyRequest.Presentation.quote_read display

example (left right : AccuracyRequest.Presentation.Display) :
    AccuracyRequest.Presentation.Same left right ↔
      AccuracyRequest.Presentation.read left = AccuracyRequest.Presentation.read right :=
  AccuracyRequest.Presentation.same_iff_read_eq left right

example (value : Fraction.Rational) (first second : 0 < value) :
    (⟨value, first⟩ : AccuracyRequest) = ⟨value, second⟩ :=
  AccuracyRequest.eq_of_tolerance_eq rfl

example : (integralBound (Source.producer.frontier
    (Source.producer.request (AccuracyRequest.Presentation.read displayedRequest))).cells).width <
      (AccuracyRequest.Presentation.read displayedRequest).tolerance :=
  Source.producer.accurate (AccuracyRequest.Presentation.read displayedRequest)

example : Source.producer.request (AccuracyRequest.Presentation.read displayedRequest) = Source.coarse := rfl

private def preparationCode : Presentation.Preparation.Code :=
  (Presentation.Preparation.quote Source.coarse.preparation).val

example : (match Presentation.Preparation.check preparationCode with
    | .valid _ => true | _ => false) = true := by decide

example : (match Presentation.Preparation.check
    (displayedRequest.val, 5, preparationCode.2.2.1, preparationCode.2.2.2) with
    | .wrongVariation _ => true | _ => false) = true := by decide

example : (match Presentation.Preparation.check
    (displayedRequest.val, 4, 0, preparationCode.2.2.2) with
    | .wrongMesh _ => true | _ => false) = true := by decide

example : (match Presentation.Preparation.check
    (displayedRequest.val, 4, preparationCode.2.2.1, Partition.Unit.Normalized.ofRequest []) with
    | .wrongPartition _ => true | _ => false) = true := by decide

example : Presentation.Preparation.read (Presentation.Preparation.quote Source.coarse.preparation) =
    Source.coarse.preparation := Presentation.Preparation.read_quote _

example (display : Presentation.Preparation.Display) :
    Presentation.Preparation.quote (Presentation.Preparation.read display) = display :=
  Presentation.Preparation.quote_read display

example (left right : Presentation.Preparation.Display) :
    Presentation.Preparation.Same left right ↔
      Presentation.Preparation.read left = Presentation.Preparation.read right :=
  Presentation.Preparation.same_iff_read_eq left right

example (code : Presentation.Preparation.Code) (first second : Presentation.Preparation.Valid code) :
    Presentation.Preparation.read ⟨code, first⟩ = Presentation.Preparation.read ⟨code, second⟩ := by rfl

private def resultCode : Presentation.Result.Code := (Presentation.Result.quote Source.coarse).val

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval (let original := Source.coarse.frontier
  let cells := Presentation.Frontier.quoteCells original.cells
  ( (match Presentation.Frontier.checkRaw original.partition.cuts cells with
     | .accepted display _ _ =>
       let code : Presentation.Result.Code := (Presentation.Preparation.quote Source.coarse.preparation, display)
       match Presentation.Result.check code with
       | .valid binding =>
         let result := Presentation.Result.read ⟨code, binding⟩
         match Presentation.Frontier.compare (Presentation.Frontier.quote result.frontier)
             (Presentation.Frontier.quote original) with
         | .isTrue _ => true | .isFalse _ => false
       | .wrongFrontier _ => false
     | _ => false),
    (match Presentation.Frontier.checkRaw [0] cells with
     | .invalidCuts (.outOfRange index _) _ => index.val == 0 | _ => false),
    (match Presentation.Frontier.checkRaw [2 / 3, 1 / 3] cells with
     | .invalidCuts (.badAdjacent _ _ _ _ _ _ _) _ => true | _ => false),
    (match Presentation.Frontier.checkRaw [] [] with
     | .invalidCells _ _ _ _ => true | _ => false)))

namespace ResultInput

open Presentation.Result

private def resultInput : Input.Code := (Input.quote Source.coarse).val

example : (match Input.check resultInput with
    | .valid _ => true | _ => false) = true := by decide

example : (match Input.check
    ((displayedRequest.val, 5, preparationCode.2.2.1, preparationCode.2.2.2), resultInput.2) with
    | .invalidPreparation (.wrongVariation _) _ => true | _ => false) = true := by decide

example : (match Input.check (resultInput.1, (resultInput.2.1, [])) with
    | .invalidFrontier (.missingCell ..) => true | _ => false) = true := by decide

example : Input.read (Input.quote Source.coarse) = Source.coarse := Input.read_quote _

example (display : Input.Display) : Input.quote (Input.read display) = display := Input.quote_read display

example (left right : Input.Display) : Input.Same left right ↔ Input.read left = Input.read right :=
  Input.same_iff_read_eq left right

end ResultInput

example : (match Presentation.Result.check resultCode with
    | .valid _ => true | .wrongFrontier _ => false) = true := by decide

example : (match Presentation.Result.check
    (Presentation.Preparation.quote Source.coarse.preparation, Presentation.Frontier.quote Source.cached.frontier) with
    | .valid _ => false | .wrongFrontier _ => true) = true := by decide

example : Presentation.Result.read (Presentation.Result.quote Source.coarse) = Source.coarse :=
  Presentation.Result.read_quote _

example : Presentation.Result.read (Presentation.Result.quote Source.cached) = Source.cached :=
  Presentation.Result.read_quote _

example (display : Presentation.Result.Display) :
    Presentation.Result.quote (Presentation.Result.read display) = display :=
  Presentation.Result.quote_read display

example (left right : Presentation.Result.Display) :
    Presentation.Result.Same left right ↔ Presentation.Result.read left = Presentation.Result.read right :=
  Presentation.Result.same_iff_read_eq left right

example (code : Presentation.Result.Code) (first second : Presentation.Result.Valid code) :
    Presentation.Result.read ⟨code, first⟩ = Presentation.Result.read ⟨code, second⟩ := by rfl

private def reusedContinuation :=
  Source.producer.advanceCached Source.retainedReadings Source.coarse.frontier ⟨16, by decide⟩

private def refinedContinuation :=
  Source.producer.advanceCached Source.retainedReadings Source.coarse.frontier ⟨4, by decide⟩

private def mismatchedContinuation : Presentation.Continuation.Code Source.coarse.frontier :=
  match refinedContinuation with
  | .reused _ _ => .reused ⟨4, by decide⟩
  | .refined _ cached fresh _ common split => .refined ⟨16, by decide⟩ cached fresh common split

example : (match reusedContinuation with | .reused .. => true | .refined .. => false) = true := by decide

example : (match refinedContinuation with | .reused .. => false | .refined .. => true) = true := by decide

example : (match Presentation.Continuation.check
    (.reused ⟨4, by decide⟩ : Presentation.Continuation.Code Source.coarse.frontier) with
    | .invalidReuse _ => true | _ => false) = true := by decide

example : (match Presentation.Continuation.check mismatchedContinuation with
    | .wrongFresh _ => true | _ => false) = true := by decide

example : Presentation.Continuation.read (Presentation.Continuation.quote reusedContinuation) =
    reusedContinuation := Presentation.Continuation.read_quote _

example : Presentation.Continuation.read (Presentation.Continuation.quote refinedContinuation) =
    refinedContinuation := Presentation.Continuation.read_quote _

example (display : Presentation.Continuation.Display Source.coarse.frontier) :
    Presentation.Continuation.quote (Presentation.Continuation.read display) = display :=
  Presentation.Continuation.quote_read display

example (left right : Presentation.Continuation.Display Source.coarse.frontier) :
    Presentation.Continuation.Same left right ↔
      Presentation.Continuation.read left = Presentation.Continuation.read right :=
  Presentation.Continuation.same_iff_read_eq left right

example : (match Presentation.Continuation.compare (Presentation.Continuation.quote reusedContinuation)
    (Presentation.Continuation.quote refinedContinuation) with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example : (match Presentation.Continuation.compare (Presentation.Continuation.quote refinedContinuation)
    (Presentation.Continuation.quote refinedContinuation) with
    | .isTrue _ => true | .isFalse _ => false) = true := by decide

example (code : Presentation.Continuation.Code Source.coarse.frontier)
    (first second : Presentation.Continuation.Valid code) :
    Presentation.Continuation.read ⟨code, first⟩ = Presentation.Continuation.read ⟨code, second⟩ := by rfl

open Presentation.Continuation
open Presentation.Result

example : Proposal.read (Proposal.quote refinedContinuation) =
    refinedContinuation := Proposal.read_quote _

example (display : Proposal.Display Source.coarse.frontier) :
    Proposal.quote (Proposal.read display) = display :=
  Proposal.quote_read display

example (left right : Proposal.Display Source.coarse.frontier) :
    Proposal.Same left right ↔
      Proposal.read left = Proposal.read right :=
  Proposal.same_iff_read_eq left right

private def isLeftCellFailure {left right : SourceFrontier Source.value}
    {inputs : List Presentation.CommonReading.Input} {intervals : List Partition.Interval}
    (failure : Presentation.CommonReadings.Failure left right inputs intervals) : Bool :=
  match failure with
  | .badReading _ _ _ _ (.leftCell _) _ => true
  | _ => false

private def checksNestedFailure (request : AccuracyRequest) (cached : List (SourcePoint Source.value))
    (fresh : Continuous.Result Source.modulus) (common : Presentation.CommonReadings.Code) : Bool :=
  let freshCode := (Input.quote fresh).val
  match Proposal.check (previous := Source.coarse.frontier)
      (.refined request (Presentation.Bank.quote cached) freshCode common) with
  | .invalidCommon _ _ _ _ _ nested => isLeftCellFailure nested
  | _ => false

/-- info: (true, true) -/
#guard_msgs in
#eval (let proposal := Proposal.quote refinedContinuation
  (match Proposal.check proposal.val with
    | .accepted valid _ _ =>
      match Presentation.Continuation.compareOwner
          (Proposal.read ⟨proposal.val, valid⟩) refinedContinuation with
      | .isTrue _ => true | .isFalse _ => false
    | _ => false,
   match refinedContinuation with
   | .reused .. => false
   | .refined request cached fresh _ common _ =>
     let original := (Presentation.CommonReadings.quote common).val
     match original.2 with
     | [] => false
     | first :: rest =>
       let changed := (original.1, { first with leftReading := first.leftReading + 1 } :: rest)
       match Presentation.CommonReadings.checkCode Source.coarse.frontier fresh.frontier changed with
       | .accepted _ => false
       | .rejected _ => checksNestedFailure request cached fresh changed))

private def commonReadingExample :=
  (SourceFrontier.commonReadings Source.coarse.frontier Source.cached.frontier).readings.head?

/-- info: (true, true, true, true, true, true, true, true, true, true, true, true) -/
#guard_msgs in
#eval (match commonReadingExample with
  | none => (false, false, false, false, false, false, false, false, false, false, false, false)
  | some reading =>
    let proposed := Presentation.CommonReading.input reading
    let left := Source.coarse.frontier
    let right := Source.cached.frontier
    ( (match Presentation.CommonReading.check left right proposed with | .valid _ => true | _ => false),
      (match Presentation.CommonReading.check left right proposed with
        | .valid proof =>
          match Presentation.CommonReading.compare (Presentation.CommonReading.read ⟨proposed, proof⟩) reading with
          | .isTrue _ => true | .isFalse _ => false
        | _ => false),
      (match Presentation.CommonReading.check left right { proposed with child := ⟨0, 0⟩ } with
        | .invalidChild _ => true | _ => false),
      (match Presentation.CommonReading.check left right { proposed with leftIndex := 99 } with
        | .leftIndex _ => true | _ => false),
      (match Presentation.CommonReading.check left right { proposed with leftParent := ⟨0, 0⟩ } with
        | .leftParent _ => true | _ => false),
      (match Presentation.CommonReading.check left right { proposed with child := ⟨0, 1⟩ } with
        | .leftContains _ => true | _ => false),
      (match Presentation.CommonReading.check left right { proposed with rightIndex := 99 } with
        | .rightIndex _ => true | _ => false),
      (match Presentation.CommonReading.check left right { proposed with rightParent := ⟨0, 0⟩ } with
        | .rightParent _ => true | _ => false),
      (match Presentation.CommonReading.check left right { proposed with child := proposed.leftParent } with
        | .rightContains _ => true | _ => false),
      (match Presentation.CommonReading.check left right { proposed with tag := -1 } with
        | .invalidTag _ => true | _ => false),
      (match Presentation.CommonReading.check left right { proposed with leftReading := proposed.leftReading + 1 } with
        | .leftCell _ => true | _ => false),
      (match Presentation.CommonReading.check left right
          { proposed with rightReading := proposed.rightReading + 1 } with
        | .rightCell _ => true | _ => false)))

example {left right : SourceFrontier Source.value} (reading : SourceFrontier.CommonReading left right) :
    Presentation.CommonReading.read (Presentation.CommonReading.quote reading) = reading :=
  Presentation.CommonReading.read_quote reading

example {left right : SourceFrontier Source.value} (display : Presentation.CommonReading.Display left right) :
    Presentation.CommonReading.quote (Presentation.CommonReading.read display) = display :=
  Presentation.CommonReading.quote_read display

example {left right : SourceFrontier Source.value} (first second : Presentation.CommonReading.Display left right) :
    Presentation.CommonReading.Same first second ↔
      Presentation.CommonReading.read first = Presentation.CommonReading.read second :=
  Presentation.CommonReading.same_iff_read_eq first second

example {left right : SourceFrontier Source.value} (input : Presentation.CommonReading.Input)
    (first second : Presentation.CommonReading.Valid left right input) :
    Presentation.CommonReading.read ⟨input, first⟩ = Presentation.CommonReading.read ⟨input, second⟩ := by rfl

private def wholeFrontier : SourceFrontier Source.value := Endpoint.frontier 0

private theorem wholeCuts : wholeFrontier.partition.cuts = [] := by decide

private def extraPartition : Partition.Unit.Normalized := Partition.Unit.Normalized.ofRequest [1 / 2]

private theorem extraPartitionIncludes : ∀ cut ∈ wholeFrontier.partition.cuts, cut ∈ extraPartition.cuts := by
  intro cut member
  rw [wholeCuts] at member
  cases member

private def extraRefinement := Partition.Unit.Common.CommonRefinement.ofPartition
  wholeFrontier.partition wholeFrontier.partition extraPartition extraPartitionIncludes extraPartitionIncludes

private def extraCommon := SourceFrontier.readRefinement wholeFrontier wholeFrontier extraRefinement
  (fun interval => interval.start) (fun _ valid => ⟨le_rfl, valid.2.1.1⟩)

example : extraCommon.refinement.partition.cuts ≠ wholeFrontier.partition.cuts := by decide

example : IntegrationFrontierRefines extraCommon.intersection.cells wholeFrontier.cells :=
  extraCommon.intersection_split

example {left right : SourceFrontier Source.value} (common : SourceFrontier.CommonReadings left right) :
    IntegrationFrontierRefines common.intersection.cells left.cells := common.intersection_split

example {left right : SourceFrontier Source.value} (common : SourceFrontier.CommonReadings left right) :
    Presentation.CommonReadings.read (Presentation.CommonReadings.quote common) = common :=
  Presentation.CommonReadings.read_quote common

example {left right : SourceFrontier Source.value} (display : Presentation.CommonReadings.Display left right) :
    Presentation.CommonReadings.quote (Presentation.CommonReadings.read display) = display :=
  Presentation.CommonReadings.quote_read display

example {left right : SourceFrontier Source.value} (first second : Presentation.CommonReadings.Display left right) :
    Presentation.CommonReadings.Same first second ↔
      Presentation.CommonReadings.read first = Presentation.CommonReadings.read second :=
  Presentation.CommonReadings.same_iff_read_eq first second

example {left right : SourceFrontier Source.value} (code : Presentation.CommonReadings.Code)
    (first second : Presentation.CommonReadings.Valid left right code) :
    Presentation.CommonReadings.read ⟨code, first⟩ = Presentation.CommonReadings.read ⟨code, second⟩ := by rfl

/-- info: (true, true, true, true, true, true, true) -/
#guard_msgs in
#eval (let inputs := Presentation.CommonReadings.quoteReadings extraCommon.readings
  let intervals := extraCommon.refinement.partition.intervals
  match inputs, intervals with
  | first :: second :: _, interval :: next :: _ =>
    ( (match Presentation.CommonReadings.check wholeFrontier wholeFrontier inputs intervals with
        | .accepted _ => true | _ => false),
      (match Presentation.CommonReadings.check wholeFrontier wholeFrontier inputs intervals with
        | .accepted proof =>
          let display : Presentation.CommonReadings.Display wholeFrontier wholeFrontier :=
            ⟨(extraCommon.refinement.partition, inputs), proof⟩
          match Presentation.CommonReadings.compare (Presentation.CommonReadings.read display) extraCommon with
          | .isTrue _ => true | .isFalse _ => false
        | _ => false),
      (match Presentation.CommonReadings.check wholeFrontier wholeFrontier [] [interval, next] with
        | .rejected (.missingReading ..) => true | _ => false),
      (match Presentation.CommonReadings.check wholeFrontier wholeFrontier [first] [] with
        | .rejected (.extraReading ..) => true | _ => false),
      (match Presentation.CommonReadings.check wholeFrontier wholeFrontier [second, first] [interval, next] with
        | .rejected (.wrongChild ..) => true | _ => false),
      (match Presentation.CommonReadings.check wholeFrontier wholeFrontier
          [{ first with leftReading := first.leftReading + 1 }, second] [interval, next] with
        | .rejected (.badReading ..) => true | _ => false),
      (match Presentation.CommonReadings.check wholeFrontier wholeFrontier [first] [interval, next] with
        | .rejected (.later _ _ (.missingReading ..)) => true | _ => false))
  | _, _ => (false, false, false, false, false, false, false))

private def initialHistoryStep : Producer.Continuation Source.producer Presentation.History.initial.1 :=
  Source.producer.advanceCached [] Presentation.History.initial.1 ⟨16, by decide⟩

private def continuedHistory : Presentation.History.State :=
  Presentation.History.append Presentation.History.initial initialHistoryStep

private def wrongHistory : Presentation.History.Code :=
  [⟨Source.coarse.frontier, .reused ⟨16, by decide⟩⟩]

private def unpaidHistory : Presentation.History.Code :=
  [⟨Presentation.History.initial.1, .reused ⟨1 / 8, by decide⟩⟩]

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval (let first : Presentation.History.CutsStep := ([], [], .reused ⟨16, by decide⟩)
  let cuts : Presentation.History.CutsStep := ([1 / 2], [], .reused ⟨16, by decide⟩)
  let cells : Presentation.History.CutsStep := ([], [((⟨0, 1⟩, 0, 4), 1, 2, 4)], .reused ⟨16, by decide⟩)
  let proposal : Presentation.History.CutsStep := ([], [], .reused ⟨8, by decide⟩)
  let same := fun a b => match Presentation.History.compareCutsCode a b with
    | .isTrue _ => true | .isFalse _ => false
  (same [first, cuts] [first, cuts], !same [first] [cuts], !same [first] [cells],
    !same [first] [proposal], !same [first, cuts] [cuts, first]))

private def compareInvalidCuts (first second : CutsFailure) : Option Bool :=
  match first, second with
  | .invalidCuts firstPosition _ firstReason firstInvalid,
    .invalidCuts secondPosition _ secondReason secondInvalid =>
      some (match CutsFailure.compareInvalidCuts firstPosition secondPosition
          firstReason firstInvalid secondReason secondInvalid with
        | .isTrue _ => true | .isFalse _ => false)
  | _, _ => none

private def firstHistoryAdjacent : Unit.Presentation.Check [2 / 3, 1 / 3, 1 / 3] :=
  .badAdjacent [] (2 / 3) (1 / 3) [1 / 3] rfl (by decide) (by decide)

private def secondHistoryAdjacent : Unit.Presentation.Check [2 / 3, 1 / 3, 1 / 3] :=
  .badAdjacent [2 / 3] (1 / 3) (1 / 3) [] rfl (by decide) (by decide)

private theorem historyAdjacentInvalid : ¬ Unit.Presentation.Valid [2 / 3, 1 / 3, 1 / 3] := by
  intro valid
  have notSorted : ¬ ([2 / 3, 1 / 3, 1 / 3] : Unit.Presentation.Code).Pairwise (· < ·) := by decide
  exact notSorted valid.1

example (first second : ¬ Unit.Presentation.Valid [2 / 3, 1 / 3, 1 / 3]) :
    CutsFailure.invalidCuts 0 _ firstHistoryAdjacent first =
      CutsFailure.invalidCuts 0 _ firstHistoryAdjacent second := rfl

/-- info: (true, true) -/
#guard_msgs in
#eval (match CutsFailure.compareInvalidCuts 0 0
    firstHistoryAdjacent historyAdjacentInvalid firstHistoryAdjacent historyAdjacentInvalid with
      | .isTrue _ => true | .isFalse _ => false,
  match CutsFailure.compareInvalidCuts 0 0
    firstHistoryAdjacent historyAdjacentInvalid secondHistoryAdjacent historyAdjacentInvalid with
      | .isTrue _ => false | .isFalse _ => true)

/-- info: (true, false) -/
#guard_msgs in
#eval (let first := CutsFailure.invalidCuts 0 _ firstHistoryAdjacent historyAdjacentInvalid
  let other := CutsFailure.invalidCuts 0 _ secondHistoryAdjacent historyAdjacentInvalid
  (match CutsFailure.compare first first with
    | .isTrue _ => true | .isFalse _ => false,
   match CutsFailure.compare first other with
    | .isTrue _ => true | .isFalse _ => false))

/-- info: (some true, some false) -/
#guard_msgs in
#eval (let bad : Presentation.History.CutsStep := ([0], [], .reused ⟨16, by decide⟩)
  let first := Presentation.History.checkCuts [bad]
  let later := Presentation.History.checkCuts (Presentation.History.quoteCuts continuedHistory ++ [bad])
  match first, later with
  | .error firstFailure, .error laterFailure =>
      (compareInvalidCuts firstFailure firstFailure, compareInvalidCuts firstFailure laterFailure)
  | _, _ => (none, none))

example (state : Presentation.History.State) :
    Presentation.History.checkCuts (Presentation.History.quoteCuts state) = .ok state :=
  Presentation.History.checkCuts_quoteCuts state

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval (let bad : Presentation.History.CutsStep := ([0], [], .reused ⟨16, by decide⟩)
  ( (match Presentation.History.checkCuts (Presentation.History.quoteCuts continuedHistory) with
      | .ok state =>
        match Presentation.History.compare (Presentation.History.display state)
            (Presentation.History.display continuedHistory) with
        | .isTrue _ => true | .isFalse _ => false
      | .error _ => false),
    (match Presentation.History.checkCuts [bad] with
      | .error (.invalidCuts 0 _ _ _) => true | _ => false),
    (match Presentation.History.checkCuts (Presentation.History.quoteCuts continuedHistory ++ [bad]) with
      | .error (.invalidCuts 1 _ _ _) => true | _ => false),
    (match Presentation.History.checkCuts ((wrongHistory.map Presentation.History.rawStep).map
        Presentation.History.cutsStep) with
      | .error (.invalidSaved (.wrongPrevious 0 ..)) => true | _ => false),
    (match Presentation.History.checkCuts ((unpaidHistory.map Presentation.History.rawStep).map
        Presentation.History.cutsStep) with
      | .error (.invalidSaved (.invalidStep 0 ..)) => true | _ => false)))

private def requestedContinuation (epsilon : Fraction.Rational) : Option Bool :=
  match Presentation.History.requestRaw [] epsilon with
  | .accepted previous _ positive returned _ _ _ =>
    let step := Source.producer.advanceWithBank
      (fun _ => Source.producer.retainedReadings previous.2) previous.1 ⟨epsilon, positive⟩
    let reused := match step with
      | .reused .. => true
      | .refined .. => false
    match reused, Presentation.History.compareFrontier previous.1 returned.1 with
    | true, .isTrue _ => some true
    | false, .isFalse _ => some false
    | _, _ => none
  | _ => none

private def namedRefinementBranch (target : Fraction.Rational) : Option Bool :=
  match Integral.refineRaw [] target with
  | .accepted previous _ positive returned _ _ _ _ _ =>
    let gap := Rational.Request.Square.gapTarget target
    let step := Source.producer.advanceWithBank
      (fun _ => Source.producer.retainedReadings previous.2) previous.1
      ⟨gap, Rational.Request.Square.gapTarget_pos positive⟩
    let reused := match step with
      | .reused .. => true
      | .refined .. => false
    let observation := Integral.checkObservation returned
      (Gaussian.Enclosure.Ball.Data.BallData.ofBall (Integral.named.name.process.ball returned))
      (Integral.named.name.process.witness returned).val
    match reused, observation with
    | true, .valid _ => some true
    | false, .valid _ => some false
    | _, _ => none
  | _ => none

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval ((match Integral.refineRaw (wrongHistory.map Presentation.History.rawStep) 4 with
    | .invalidHistory (.wrongPrevious 0 ..) _ => true | _ => false),
  (match Integral.refineRaw [] 0 with | .nonpositive _ => true | _ => false),
  namedRefinementBranch 16 == some true,
  namedRefinementBranch (1 / 8) == some false)

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval (let bad : Presentation.History.CutsStep := ([0], [], .reused ⟨16, by decide⟩)
  ((match Integral.refineCuts (Presentation.History.quoteCuts continuedHistory) 16 with
    | .accepted previous _ _ returned _ _ _ _ _ =>
      match Presentation.History.compare (Presentation.History.display previous)
          (Presentation.History.display continuedHistory),
        Integral.checkObservation returned
          (Gaussian.Enclosure.Ball.Data.BallData.ofBall (Integral.named.name.process.ball returned))
          (Integral.named.name.process.witness returned).val with
      | .isTrue _, .valid _ => true | _, _ => false
    | _ => false),
  (match Integral.refineCuts [bad] 16 with
    | .invalidHistory (.invalidCuts 0 _ _ _) _ => true | _ => false),
  (match Integral.refineCuts (Presentation.History.quoteCuts continuedHistory ++ [bad]) 16 with
    | .invalidHistory (.invalidCuts 1 _ _ _) _ => true | _ => false),
  (match Integral.refineCuts ((wrongHistory.map Presentation.History.rawStep).map
      Presentation.History.cutsStep) 16 with
    | .invalidHistory (.invalidSaved (.wrongPrevious 0 ..)) _ => true | _ => false),
  (match Integral.refineCuts [bad] 0 with | .nonpositive _ => true | _ => false)))

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval ((match Presentation.History.requestRaw (wrongHistory.map Presentation.History.rawStep) 16 with
    | .invalidHistory (.wrongPrevious 0 ..) _ => true | _ => false),
  (match Presentation.History.requestRaw [] 0 with
    | .nonpositive _ _ _ => true | _ => false),
  requestedContinuation 16 == some true,
  requestedContinuation (1 / 8) == some false,
  (match Presentation.History.requestRaw (Presentation.History.quoteRaw continuedHistory) 16 with
    | .accepted previous _ _ returned _ _ _ =>
      match Presentation.History.compare (Presentation.History.display previous)
          (Presentation.History.display continuedHistory),
          Presentation.History.checkRaw (Presentation.History.quoteRaw returned) with
      | .isTrue _, .ok checked =>
        match Presentation.History.compare (Presentation.History.display checked)
            (Presentation.History.display returned) with
        | .isTrue _ => true | .isFalse _ => false
      | _, _ => false
    | _ => false))

example : (match Presentation.History.check wrongHistory with
    | .error (.wrongPrevious 0 _ _ _) => true | _ => false) = true := by decide

/-- info: true -/
#guard_msgs in
#eval (match Presentation.History.check unpaidHistory with
    | .error (.invalidStep 0 _ _ _ _) => true | _ => false)

private def refinedHistoryStep : Producer.Continuation Source.producer Presentation.History.initial.1 :=
  Source.producer.advanceCached [] Presentation.History.initial.1 ⟨1 / 8, by decide⟩

private def refinedHistory : Presentation.History.State :=
  Presentation.History.append Presentation.History.initial refinedHistoryStep

example : Presentation.History.read (Presentation.History.display refinedHistory) = refinedHistory :=
  Presentation.History.read_display _

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval (match refinedHistoryStep with
  | .reused .. => (false, false, false, false)
  | .refined request cached fresh freshEq common split =>
    let left := Presentation.History.initial.1
    let right := fresh.frontier
    let inputs := Presentation.CommonReadings.quoteReadings common.readings
    ( (match Presentation.CommonReadings.checkRaw left right common.refinement.partition.cuts inputs with
       | .accepted display _ _ =>
         let reconstructed := Presentation.CommonReadings.read display
         match Presentation.CommonReadings.compare reconstructed common with
         | .isFalse _ => false
         | .isTrue equal =>
           let next : Producer.Continuation Source.producer left :=
             .refined request cached fresh freshEq reconstructed (by rw [equal]; exact split)
           match Presentation.History.check
               (Presentation.History.quote (Presentation.History.append Presentation.History.initial next)) with
           | .ok _ => true | .error _ => false
       | _ => false),
      (match Presentation.CommonReadings.checkRaw left right [0] inputs with
       | .invalidCuts (.outOfRange index _) _ => index.val == 0 | _ => false),
      (match Presentation.CommonReadings.checkRaw left right [2 / 3, 1 / 3] inputs with
       | .invalidCuts (.badAdjacent _ _ _ _ _ _ _) _ => true | _ => false),
      (match Presentation.CommonReadings.checkRaw left right [] [] with
       | .invalidReadings _ _ _ _ => true | _ => false)))

private def isNestedHistoryFailure (failure : Presentation.History.Failure) : Bool :=
  match failure with
  | .invalidStep position _ _ result _ =>
      position == 7 && match result with
        | .invalidCommon _ _ _ _ _ nested => isLeftCellFailure nested
        | _ => false
  | _ => false

private def checksNestedHistory (request : AccuracyRequest) (cached : List (SourcePoint Source.value))
    (fresh : Continuous.Result Source.modulus) (common : Presentation.CommonReadings.Code) : Bool :=
  let freshCode := (Input.quote fresh).val
  let step : Presentation.History.StepCode :=
    ⟨Presentation.History.initial.1, .refined request (Presentation.Bank.quote cached) freshCode common⟩
  match Presentation.History.scanFrom Presentation.History.initial 7 [step] with
  | .error failure => isNestedHistoryFailure failure
  | .ok _ => false

private def actualHistory (target : Fraction.Rational) (positive : 0 < target) :
    Presentation.History.State :=
  Integral.named.name.process.refine Integral.named.name.state target positive

private def actualStep (target : Fraction.Rational) (positive : 0 < target) :
    Producer.Continuation Source.producer Presentation.History.initial.1 :=
  Source.producer.advanceWithBank
    (fun _ => Source.producer.retainedReadings Presentation.History.initial.2)
    Presentation.History.initial.1
    ⟨Rational.Request.Square.gapTarget target, Rational.Request.Square.gapTarget_pos positive⟩

example (target : Fraction.Rational) (positive : 0 < target) :
    actualHistory target positive = Presentation.History.append Presentation.History.initial
      (actualStep target positive) := rfl

example (state : Presentation.History.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Source.boundProcess.request state epsilon positive = Presentation.History.append state
      (Source.producer.advanceWithBank (fun _ => Source.producer.retainedReadings state.2)
        state.1 ⟨epsilon, positive⟩) :=
  Presentation.History.boundProcess_request state epsilon positive

example (state : Presentation.History.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (accurate : (integralBound state.1.cells).width < epsilon) :
    Source.boundProcess.request state epsilon positive =
      Presentation.History.append state (.reused ⟨epsilon, positive⟩ accurate) :=
  Presentation.History.boundProcess_request_reused state epsilon positive accurate

private def isReusedStep (step : Producer.Continuation Source.producer Presentation.History.initial.1) : Bool :=
  match step with
  | .reused .. => true
  | .refined .. => false

private def rejectsActualHistoryCache
    (step : Producer.Continuation Source.producer Presentation.History.initial.1) : Bool :=
  match step with
  | .reused .. => false
  | .refined request cached fresh _ common _ =>
    let original := (Presentation.CommonReadings.quote common).val
    match original.2 with
    | [] => false
    | first :: rest =>
      let changed := (original.1, { first with leftReading := first.leftReading + 1 } :: rest)
      match Presentation.CommonReadings.checkCode Presentation.History.initial.1 fresh.frontier changed with
      | .accepted _ => false
      | .rejected _ => checksNestedHistory request cached fresh changed

/-- info: (true, true, true, true, true, true, true) -/
#guard_msgs in
#eval (let reused := actualHistory 16 (by decide)
  let refined := actualHistory (1 / 8) (by decide)
  let bound := Source.boundProcess.bound refined
  let ball := Integral.named.name.process.ball refined
  let witness := (Integral.named.name.process.witness refined).val
  (isReusedStep (actualStep 16 (by decide)),
   (match Presentation.History.check (Presentation.History.quote reused) with
     | .ok _ => true | .error _ => false),
   (match Presentation.History.check (Presentation.History.quote refined) with
     | .ok _ => true | .error _ => false),
   rejectsActualHistoryCache (actualStep (1 / 8) (by decide)),
   decide (ball.center.re = bound.lower),
   decide (witness.re = bound.midpoint),
   decide (ball.radiusSq = bound.width ^ 2)))

private def frontierFailureKind {cells : List Presentation.Cell.Code} {intervals : List Partition.Interval}
    (failure : Presentation.Frontier.Failure cells intervals) : Nat :=
  match failure with
  | .missingCell .. => 2
  | _ => 0

private def resultFailureKind {code : Input.Code}
    (failure : Input.Check code) : Nat :=
  match failure with
  | .invalidPreparation (.nonpositiveRequest _) _ => 4
  | .invalidPreparation (.wrongVariation _) _ => 1
  | .invalidFrontier failure => frontierFailureKind failure
  | .wrongFrontier .. => 3
  | _ => 0

private def isWrongResultHistory (expected : Nat) (failure : Presentation.History.Failure) : Bool :=
  match failure with
  | .invalidStep position _ _ result _ =>
      position == 7 && match result with
        | .invalidResult _ _ _ _ reason _ => resultFailureKind reason == expected
        | _ => false
  | _ => false

private def checksWrongResultHistory (request : AccuracyRequest) (cached : List (SourcePoint Source.value))
    (fresh : Input.Code) (common : Presentation.CommonReadings.Code) (expected : Nat) : Bool :=
  let step : Presentation.History.StepCode :=
    ⟨Presentation.History.initial.1, .refined request (Presentation.Bank.quote cached) fresh common⟩
  match Presentation.History.scanFrom Presentation.History.initial 7 [step] with
  | .error failure => isWrongResultHistory expected failure
  | .ok _ => false

/-- info: (true, true, true, true, true, true, true) -/
#guard_msgs in
#eval ( (match Presentation.History.check (Presentation.History.quote refinedHistory) with
          | .ok _ => true | .error _ => false),
  (match refinedHistoryStep with
  | .reused .. => false
  | .refined request cached fresh _ common _ =>
    let original := (Presentation.CommonReadings.quote common).val
    match original.2 with
    | [] => false
    | first :: rest =>
      let changed := (original.1, { first with leftReading := first.leftReading + 1 } :: rest)
      match Presentation.CommonReadings.checkCode Presentation.History.initial.1 fresh.frontier changed with
      | .accepted _ => false
      | .rejected _ => checksNestedHistory request cached fresh changed),
  (match refinedHistoryStep with
  | .reused .. => false
  | .refined request cached fresh _ common _ =>
    let wrong := ((Input.quote fresh).val.1,
      (Presentation.Frontier.quote Source.coarse.frontier).val)
    match (Input.check wrong).decision with
    | .isTrue _ => false
    | .isFalse _ =>
      checksWrongResultHistory request cached wrong (Presentation.CommonReadings.quote common).val 3),
  (match refinedHistoryStep with
  | .reused .. => false
  | .refined request cached fresh _ common _ =>
    let code := (Input.quote fresh).val
    let prep := code.1
    let wrong := ((prep.1, prep.2.1 + 1, prep.2.2.1, prep.2.2.2), code.2)
    match (Input.check wrong).decision with
    | .isTrue _ => false
    | .isFalse _ =>
      checksWrongResultHistory request cached wrong (Presentation.CommonReadings.quote common).val 1),
  (match refinedHistoryStep with
  | .reused .. => false
  | .refined request cached fresh _ common _ =>
    let code := (Input.quote fresh).val
    let wrong := (code.1, (code.2.1, []))
    match (Input.check wrong).decision with
    | .isTrue _ => false
    | .isFalse _ =>
      checksWrongResultHistory request cached wrong (Presentation.CommonReadings.quote common).val 2),
  (match refinedHistoryStep with
  | .reused .. => false
  | .refined request cached fresh _ common _ =>
    let code := (Input.quote fresh).val
    let wrong := ((0, code.1.2), code.2)
    match (Input.check wrong).decision with
    | .isTrue _ => false
    | .isFalse _ =>
      checksWrongResultHistory request cached wrong (Presentation.CommonReadings.quote common).val 4),
  match refinedHistoryStep with
  | .reused .. => false
  | .refined request cached fresh _ common _ =>
    let code := (Input.quote fresh).val
    let wrong := ((-1, code.1.2), code.2)
    match (Input.check wrong).decision with
    | .isTrue _ => false
    | .isFalse _ =>
      checksWrongResultHistory request cached wrong (Presentation.CommonReadings.quote common).val 4)

example : Presentation.History.read (Presentation.History.display Source.initialHistory) =
    Source.initialHistory := Presentation.History.read_display _

example : Presentation.History.read (Presentation.History.display continuedHistory) = continuedHistory :=
  Presentation.History.read_display _

example (display : Presentation.History.Display) :
    Presentation.History.display (Presentation.History.read display) = display :=
  Presentation.History.display_read display

example (left right : Presentation.History.Display) :
    Presentation.History.Same left right ↔ Presentation.History.read left = Presentation.History.read right :=
  Presentation.History.same_iff_read_eq left right

example : continuedHistory.1 = Presentation.History.initial.1 := by
  have accurate : (integralBound Presentation.History.initial.1.cells).width <
      (⟨16, by decide⟩ : AccuracyRequest).tolerance := by
    exact (Source.producer.accurate ⟨1, by decide⟩).trans (by decide)
  simp only [continuedHistory, Presentation.History.append, initialHistoryStep,
    Producer.advanceCached, Producer.advanceWithBank, dif_pos accurate, Producer.Continuation.frontier]

example : (match Presentation.History.compare (Presentation.History.display Presentation.History.initial)
    (Presentation.History.display continuedHistory) with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

/-- info: true -/
#guard_msgs in
#eval (match Presentation.History.check (Presentation.History.quote continuedHistory) with
    | .ok _ => true | .error _ => false)

example (state : Source.boundProcess.State) := Integral.actualObservation_valid state

example (state : Source.boundProcess.State) :
    Integral.PairedPresentation.read
        (Integral.PairedPresentation.quote
          ((RationalBound.locatedPair Source.boundProcess).observation state)) =
      (RationalBound.locatedPair Source.boundProcess).observation state :=
  Integral.PairedPresentation.read_quote _

example : Integral.PairedPresentation.read
    (Integral.PairedPresentation.quote
      ((RationalBound.locatedPair Source.boundProcess).observation continuedHistory)) =
    (RationalBound.locatedPair Source.boundProcess).observation continuedHistory :=
  Integral.PairedPresentation.read_quote _

example : Integral.PairedPresentation.read
    (Integral.PairedPresentation.quote
      ((RationalBound.locatedPair Source.boundProcess).observation refinedHistory)) =
    (RationalBound.locatedPair Source.boundProcess).observation refinedHistory :=
  Integral.PairedPresentation.read_quote _

example (display : Integral.PairedPresentation.Display) :
    Integral.PairedPresentation.quote (Integral.PairedPresentation.read display) = display :=
  Integral.PairedPresentation.quote_read display

example (first second : Integral.PairedPresentation.Display) :
    Integral.PairedPresentation.Same first second ↔
      Integral.PairedPresentation.read first = Integral.PairedPresentation.read second :=
  Integral.PairedPresentation.same_iff_read_eq first second

example (observation : Integral.PairedPresentation.Observation)
    (ordered : (Source.boundProcess.bound observation.lowerState).lower ≤
      (Source.boundProcess.bound observation.upperState).upper) :
    (⟨observation.lowerState, observation.upperState, ordered⟩ : Integral.PairedPresentation.Observation) =
      observation := by
  cases observation
  rfl

example (display : Integral.PairedPresentation.Display)
    (lowerBinding : display.val.1.val = Presentation.History.quote Presentation.History.initial)
    (upperBinding : display.val.2.val = Presentation.History.quote continuedHistory) :
    (Integral.PairedPresentation.read display).lowerState = Presentation.History.initial ∧
      (Integral.PairedPresentation.read display).upperState = continuedHistory := by
  constructor
  · apply Presentation.History.read_of_success
    rw [lowerBinding]
    exact Presentation.History.check_quote _
  · apply Presentation.History.read_of_success
    rw [upperBinding]
    exact Presentation.History.check_quote _

/-- info: (true, true, true, true, true, true) -/
#guard_msgs in
#eval (match Integral.PairedPresentation.checkRaw
    (Presentation.History.quoteRaw Presentation.History.initial) (Presentation.History.quoteRaw refinedHistory),
    Integral.PairedPresentation.checkRaw
      (Presentation.History.quoteRaw Presentation.History.initial)
      (Presentation.History.quoteRaw Presentation.History.initial) with
  | .accepted pair _ _, .accepted changed _ _ =>
    ((match Presentation.History.compare (Presentation.History.display pair.lowerState)
        (Presentation.History.display Presentation.History.initial) with
        | .isTrue _ => true | .isFalse _ => false),
      (match Presentation.History.compare (Presentation.History.display pair.upperState)
        (Presentation.History.display refinedHistory) with
        | .isTrue _ => true | .isFalse _ => false),
      (match Presentation.History.compare
          (Presentation.History.display
            (Integral.PairedPresentation.read (Integral.PairedPresentation.quote pair)).lowerState)
          (Presentation.History.display Presentation.History.initial) with
        | .isTrue _ => true | .isFalse _ => false),
      (match Presentation.History.compare
          (Presentation.History.display
            (Integral.PairedPresentation.read (Integral.PairedPresentation.quote pair)).upperState)
          (Presentation.History.display refinedHistory) with
        | .isTrue _ => true | .isFalse _ => false),
      (match Integral.PairedPresentation.compare (Integral.PairedPresentation.quote pair)
          (Integral.PairedPresentation.quote pair) with
        | .isTrue _ => true | .isFalse _ => false),
      (match Integral.PairedPresentation.compare (Integral.PairedPresentation.quote pair)
          (Integral.PairedPresentation.quote changed) with
        | .isTrue _ => false | .isFalse _ => true))
  | _, _ => (false, false, false, false, false, false))

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval ((match Integral.PairedPresentation.checkRaw [] [] with
    | .accepted .. => true | _ => false),
  (match Integral.PairedPresentation.checkRaw (wrongHistory.map Presentation.History.rawStep) [] with
    | .invalidLower (.wrongPrevious 0 ..) _ => true | _ => false),
  (match Integral.PairedPresentation.checkRaw [] (wrongHistory.map Presentation.History.rawStep) with
    | .invalidUpper (.wrongPrevious 0 ..) _ => true | _ => false),
  (match Integral.PairedPresentation.checkRaw [] (unpaidHistory.map Presentation.History.rawStep) with
    | .invalidUpper (.invalidStep 0 ..) _ => true | _ => false))

example (state : Source.boundProcess.State)
    (ball : Gaussian.Enclosure.Ball.Data.BallData) (midpoint : Basic.Canonical)
    (valid : Integral.ObservationValid state ball midpoint) :=
  Integral.observation_eq_bound state ball midpoint valid

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval (match Presentation.History.check (Presentation.History.quote continuedHistory) with
  | .error _ => (false, false, false, false)
  | .ok state =>
    let ball := Gaussian.Enclosure.Ball.Data.BallData.ofBall (Integral.named.name.process.ball state)
    let midpoint := (Integral.named.name.process.witness state).val
    let changedCenter := { ball with center := { ball.center with re := ball.center.re + 1 } }
    let changedRadius := { ball with radiusSq := ball.radiusSq + 1 }
    let changedMidpoint := { midpoint with re := midpoint.re + 1 }
    ((match Integral.checkObservation state ball midpoint with | .valid _ => true | _ => false),
     (match Integral.checkObservation state changedCenter midpoint with | .wrongCenter _ => true | _ => false),
     (match Integral.checkObservation state changedRadius midpoint with | .wrongRadius _ => true | _ => false),
     (match Integral.checkObservation state ball changedMidpoint with | .wrongMidpoint _ => true | _ => false)))

/-- info: true -/
#guard_msgs in
#eval (match Presentation.History.compare (Presentation.History.display continuedHistory)
    (Presentation.History.display continuedHistory) with
    | .isTrue _ => true | .isFalse _ => false)

#eval (match AccuracyRequest.Presentation.check 16 with
  | .valid positive =>
    (Source.producer.request (AccuracyRequest.Presentation.read ⟨16, positive⟩)).frontier.cells.length
  | .nonpositive _ => 0)

private def savedPoint : Presentation.Display := ⟨(⟨0, 1⟩, 0, 4), by decide⟩

private def otherPoint : Presentation.Display := ⟨(⟨0, 1⟩, 1, 2), by decide⟩

private def bankPoints : List (SourcePoint Source.value) :=
  [Presentation.read savedPoint, Presentation.read otherPoint]

example : Presentation.Bank.read (Presentation.Bank.quote bankPoints)
    (Presentation.Bank.quote_valid bankPoints) = bankPoints := Presentation.Bank.read_quote _ _

example (code : Presentation.Bank.Code) (valid : Presentation.Bank.Valid code) :
    Presentation.Bank.quote (Presentation.Bank.read code valid) = code := Presentation.Bank.quote_read code valid

example : (match Presentation.Bank.check [savedPoint.val, (⟨0, 1⟩, 2, 4)] with
    | .rejected (.later _ (.here _ _ (.aboveFinish _) _)) => true | _ => false) = true := by decide

example : (match Presentation.Bank.check [savedPoint.val, (⟨0, 1⟩, 0, 2)] with
    | .rejected (.later _ (.here _ _ (.wrongReading _) _)) => true | _ => false) = true := by decide

example : SourcePoint.readCached Source.value
    (Presentation.Bank.read (Presentation.Bank.quote bankPoints)
      (Presentation.Bank.quote_valid bankPoints)) 0 = 4 := by decide

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval (match (Proposal.quote refinedContinuation).val with
  | .reused _ => (false, false, false, false)
  | .refined request bank fresh common =>
    (bank.length > 0,
      match Proposal.check (previous := Source.coarse.frontier)
          (.refined request [savedPoint.val, (⟨0, 1⟩, 2, 4)] fresh common) with
      | .invalidBank _ _ _ _ (.later _ (.here _ _ (.aboveFinish _) _)) => true | _ => false,
      match Proposal.check (previous := Source.coarse.frontier)
          (.refined request [savedPoint.val, (⟨0, 1⟩, 0, 2)] fresh common) with
      | .invalidBank _ _ _ _ (.later _ (.here _ _ (.wrongReading _) _)) => true | _ => false,
      match Presentation.History.checkSaved (Presentation.Frontier.quote Presentation.History.initial.1).val
          (.refined request [savedPoint.val, (⟨0, 1⟩, 0, 2)] fresh common) with
      | .checked _ _ _ _ (.invalidBank _ _ _ _ (.later _ (.here _ _ (.wrongReading _) _))) => true
      | _ => false))

example : (match Presentation.check (⟨⟨0, 1⟩, 0, 4⟩ : Presentation.Code) with
    | .valid _ => true | _ => false) = true := by decide

example : (match Presentation.check (⟨⟨0, 1⟩, -1, 4⟩ : Presentation.Code) with
    | .belowStart _ => true | _ => false) = true := by decide

example : (match Presentation.check (⟨⟨0, 1⟩, 2, 4⟩ : Presentation.Code) with
    | .aboveFinish _ => true | _ => false) = true := by decide

example : (match Presentation.check (⟨⟨0, 1⟩, 0, 2⟩ : Presentation.Code) with
    | .wrongReading _ => true | _ => false) = true := by decide

example : SourcePoint.readCached Source.value [Presentation.read savedPoint] 0 = 4 := by decide

example : (match Presentation.compare savedPoint savedPoint with
    | .isTrue _ => true | .isFalse _ => false) = true := by decide

example : (match Presentation.compare savedPoint otherPoint with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example (point : SourcePoint Source.value) : Presentation.read (Presentation.quote point) = point :=
  Presentation.read_quote point

example (display : Presentation.Display) : Presentation.quote (Presentation.read display) = display :=
  Presentation.quote_read display

example (left right : Presentation.Display) :
    Presentation.Same left right ↔ Presentation.read left = Presentation.read right :=
  Presentation.same_iff_read_eq left right

example (code : Presentation.Code) (first second : Presentation.Valid code) :
    Presentation.read ⟨code, first⟩ = Presentation.read ⟨code, second⟩ := by
  rfl

private def savedCell : Presentation.Cell.Display := ⟨((⟨0, 1⟩, 0, 4), 1, 2, 4), by decide⟩

private def otherCell : Presentation.Cell.Display := ⟨((⟨0, 1⟩, 0, 4), 1, 2, 5), by decide⟩

private def lowerSplitCell : Presentation.Cell.Display := ⟨((⟨0, 1⟩, 0, 4), 1, 1, 4), by decide⟩

/-- The original saved pi cell has its interval's weight and encloses the source. -/
private theorem savedCell_admitted : IntegrationCell.Source.Admitted (Presentation.Cell.read savedCell) := by
  constructor
  · decide
  · intro point lower upper
    exact ⟨Source.two_le_value lower upper, Source.value_le_four point⟩

/-- Split the saved pi cell at its midpoint with the two endpoint tags. -/
private def savedCellSplit : IntegrationSplit (Presentation.Cell.read savedCell) :=
  IntegrationCell.Source.splitAt (Presentation.Cell.read savedCell) savedCell_admitted
    (1 / 2) 0 1 (by decide) (by decide) (by decide)

/-- info: (true, true, true) -/
#guard_msgs in
#eval (match IntegrationSplit.Presentation.check (Presentation.Cell.read savedCell) savedCellSplit.children with
  | .accepted found _ =>
    match found.children, savedCellSplit.children with
    | [left, right], [originalLeft, originalRight] =>
      (true,
        (match Presentation.Cell.compare (Presentation.Cell.quote left) (Presentation.Cell.quote originalLeft) with
          | .isTrue _ => true | .isFalse _ => false),
        (match Presentation.Cell.compare (Presentation.Cell.quote right) (Presentation.Cell.quote originalRight) with
          | .isTrue _ => true | .isFalse _ => false))
    | _, _ => (true, false, false)
  | _ => (false, false, false))

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval ((match IntegrationSplit.Presentation.check (Presentation.Cell.read savedCell)
      [Presentation.Cell.read savedCell] with | .accepted _ _ => true | _ => false),
  (match IntegrationSplit.Presentation.check (Presentation.Cell.read savedCell) [] with
      | .wrongWeight _ => true | _ => false),
  (match IntegrationSplit.Presentation.check (Presentation.Cell.read savedCell)
      [Presentation.Cell.read lowerSplitCell] with
      | .lowerOutOfRange index _ => index.val == 0 | _ => false),
  (match IntegrationSplit.Presentation.check (Presentation.Cell.read savedCell)
      [Presentation.Cell.read otherCell] with
      | .upperOutOfRange index _ => index.val == 0 | _ => false))

example {α : Type} {parent : IntegrationCell α} (split : IntegrationSplit parent) :
    IntegrationSplit.Presentation.read (IntegrationSplit.Presentation.quote split) = split :=
  IntegrationSplit.Presentation.read_quote split

example {α : Type} {parent : IntegrationCell α} (split : IntegrationSplit parent) :=
  IntegrationSplit.Presentation.check_quote split

example (parent : IntegrationCell (SourcePoint Source.value))
    (admitted : IntegrationCell.Source.Admitted parent) (cut left right : Fraction.Rational)
    (inside : parent.item.interval.start ≤ cut ∧ cut ≤ parent.item.interval.finish)
    (leftInside : parent.item.interval.start ≤ left ∧ left ≤ cut)
    (rightInside : cut ≤ right ∧ right ≤ parent.item.interval.finish) :=
  IntegrationSplit.Presentation.check_quote
    (IntegrationCell.Source.splitAt parent admitted cut left right inside leftInside rightInside)

example {α : Type} {parent : IntegrationCell α} (children : List (IntegrationCell α))
    (first second : IntegrationSplit.Presentation.Valid parent children) :
    IntegrationSplit.Presentation.read ⟨children, first⟩ =
      IntegrationSplit.Presentation.read ⟨children, second⟩ := rfl

example {α : Type} {parent : IntegrationCell α}
    (left right : {children : List (IntegrationCell α) // IntegrationSplit.Presentation.Valid parent children}) :
    IntegrationSplit.Presentation.read left = IntegrationSplit.Presentation.read right ↔ left.val = right.val :=
  IntegrationSplit.Presentation.read_eq_iff left right

example : (match Presentation.Cell.check (((⟨0, 1⟩, 0, 4), 1, 2, 4) : Presentation.Cell.Code) with
    | .valid _ => true | _ => false) = true := by decide

example : (match Presentation.Cell.check (((⟨0, 1⟩, -1, 4), 1, 2, 4) : Presentation.Cell.Code) with
    | .belowStart _ => true | _ => false) = true := by decide

example : (match Presentation.Cell.check (((⟨0, 1⟩, 2, 4), 1, 2, 4) : Presentation.Cell.Code) with
    | .aboveFinish _ => true | _ => false) = true := by decide

example : (match Presentation.Cell.check (((⟨0, 1⟩, 0, 2), 1, 2, 4) : Presentation.Cell.Code) with
    | .wrongReading _ => true | _ => false) = true := by decide

example : (match Presentation.Cell.check (((⟨0, 1⟩, 0, 4), -1, 2, 4) : Presentation.Cell.Code) with
    | .negativeWeight _ => true | _ => false) = true := by decide

example : (match Presentation.Cell.check (((⟨0, 1⟩, 0, 4), 1, 4, 2) : Presentation.Cell.Code) with
    | .reversedRange _ => true | _ => false) = true := by decide

example : (match Presentation.Cell.compare savedCell savedCell with
    | .isTrue _ => true | .isFalse _ => false) = true := by decide

example : (match Presentation.Cell.compare savedCell otherCell with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example : lowerIntegral [Presentation.Cell.read savedCell] = 2 := by decide

example : SourcePoint.readCached Source.value [(Presentation.Cell.read savedCell).item] 0 = 4 := by decide

example (cell : IntegrationCell (SourcePoint Source.value)) :
    Presentation.Cell.read (Presentation.Cell.quote cell) = cell := Presentation.Cell.read_quote cell

example (display : Presentation.Cell.Display) :
    Presentation.Cell.quote (Presentation.Cell.read display) = display := Presentation.Cell.quote_read display

example (left right : Presentation.Cell.Display) :
    Presentation.Cell.Same left right ↔ Presentation.Cell.read left = Presentation.Cell.read right :=
  Presentation.Cell.same_iff_read_eq left right

example (code : Presentation.Cell.Code) (first second : Presentation.Cell.Valid code) :
    Presentation.Cell.read ⟨code, first⟩ = Presentation.Cell.read ⟨code, second⟩ := by
  rfl

private def frontierCell : Presentation.Cell.Code := ((⟨0, 1⟩, 0, 4), 1, 2, 4)

private def noCuts : Unit.Presentation.Display :=
  ⟨[], ⟨List.Pairwise.nil, fun _ member => by nomatch member⟩⟩

private def badLowerFrontier : Presentation.Frontier.Display :=
  ⟨(Unit.Presentation.read noCuts, [((⟨0, 1⟩, 0, 4), 1, 3, 4)]), by decide⟩

private def badUpperFrontier : Presentation.Frontier.Display :=
  ⟨(Unit.Presentation.read noCuts, [((⟨0, 1⟩, 0, 4), 1, 0, 3)]), by decide⟩

private def bothRangeCell : IntegrationCell (SourcePoint Source.value) :=
  Presentation.Cell.read ⟨((⟨0, 1⟩, 0, 4), 1, 3, 3), by decide⟩

private def firstLowerRangeFailure : Presentation.Frontier.RangeFailure [bothRangeCell, bothRangeCell] :=
  .lower bothRangeCell [bothRangeCell] (by decide)

private def firstUpperRangeFailure : Presentation.Frontier.RangeFailure [bothRangeCell, bothRangeCell] :=
  .upper bothRangeCell [bothRangeCell] (by decide)

private def laterLowerRangeFailure : Presentation.Frontier.RangeFailure [bothRangeCell, bothRangeCell] :=
  .later bothRangeCell (.lower bothRangeCell [] (by decide))

example (first second : Source.value bothRangeCell.item.interval.finish < bothRangeCell.lower) :
    Presentation.Frontier.RangeFailure.lower bothRangeCell [] first =
      Presentation.Frontier.RangeFailure.lower bothRangeCell [] second := rfl

/-- info: (true, true, true) -/
#guard_msgs in
#eval (match Presentation.Frontier.RangeFailure.compare firstLowerRangeFailure firstLowerRangeFailure with
    | .isTrue _ => true | .isFalse _ => false,
  match Presentation.Frontier.RangeFailure.compare firstLowerRangeFailure firstUpperRangeFailure with
    | .isTrue _ => false | .isFalse _ => true,
  match Presentation.Frontier.RangeFailure.compare firstLowerRangeFailure laterLowerRangeFailure with
    | .isTrue _ => false | .isFalse _ => true)

private def isWrongFrontierReading {cells : List Presentation.Cell.Code} {intervals : List Partition.Interval}
    (failure : Presentation.Frontier.Failure cells intervals) : Bool :=
  match failure with
  | .badCell _ _ _ _ (.wrongReading _) _ => true
  | _ => false

private def isLowerRangeFailure {cells : List (IntegrationCell (SourcePoint Source.value))}
    (failure : Presentation.Frontier.RangeFailure cells) : Bool :=
  match failure with
  | .lower .. => true
  | _ => false

private def isUpperRangeFailure {cells : List (IntegrationCell (SourcePoint Source.value))}
    (failure : Presentation.Frontier.RangeFailure cells) : Bool :=
  match failure with
  | .upper .. => true
  | _ => false

private def isSavedLowerFailure {saved : Presentation.Frontier.Code}
    {step : Proposal.Code Presentation.History.initial.1}
    (result : Presentation.History.SavedCheck saved step) : Bool :=
  match result with
  | .invalidRange _ failure => isLowerRangeFailure failure
  | _ => false

private def rawInitialStep : Presentation.History.RawStep :=
  ((Presentation.Frontier.quote Presentation.History.initial.1).val, .reused ⟨16, by decide⟩)

private def rawWrongReading : Presentation.Frontier.Code :=
  (Unit.Presentation.read noCuts, [((⟨0, 1⟩, 0, 2), 1, 2, 4)])

private def sameRawFailure (first second : RawFailure) : Bool :=
  match RawFailure.compare first second with
  | .isTrue _ => true | .isFalse _ => false

private def sameCutsFailure (first second : CutsFailure) : Bool :=
  match CutsFailure.compare first second with
  | .isTrue _ => true | .isFalse _ => false

/-- info: (true, false, true, false, false, false) -/
#guard_msgs in
#eval (let proposal := Proposal.Code.reused ⟨16, by decide⟩
  let wrong : Presentation.History.RawStep := ((Presentation.Frontier.quote Source.coarse.frontier).val, proposal)
  let unpaid : Presentation.History.RawStep := (rawInitialStep.1, .reused ⟨1 / 8, by decide⟩)
  let otherUnpaid : Presentation.History.RawStep := (rawInitialStep.1, .reused ⟨1 / 16, by decide⟩)
  match Presentation.History.checkRaw [wrong], Presentation.History.checkRaw [rawInitialStep, wrong],
      Presentation.History.checkRaw [unpaid], Presentation.History.checkRaw [otherUnpaid] with
  | .error first, .error later, .error step, .error otherStep =>
    (sameRawFailure first first, sameRawFailure first later,
      sameRawFailure step step, sameRawFailure step otherStep, sameRawFailure first step,
      sameCutsFailure (.invalidSaved first) (.invalidSaved step))
  | _, _, _, _ => (false, true, false, true, true, true))

private def doublyBadPoint : Presentation.Code := (⟨0, 1⟩, -1, 0)

private theorem doublyBadPointInvalid : ¬ Presentation.Valid doublyBadPoint := by decide

private def firstBankFailure : Presentation.Bank.Failure [doublyBadPoint] :=
  .here doublyBadPoint [] (.belowStart (by decide)) doublyBadPointInvalid

private def otherBankFailure : Presentation.Bank.Failure [doublyBadPoint] :=
  .here doublyBadPoint [] (.wrongReading (by decide)) doublyBadPointInvalid

/-- info: (true, false) -/
#guard_msgs in
#eval (match (Proposal.quote refinedContinuation).val with
  | .reused _ => (false, true)
  | .refined request _ fresh common =>
    let code : Proposal.Code Presentation.History.initial.1 := .refined request [doublyBadPoint] fresh common
    let invalid : ¬ Proposal.Valid code := fun valid => firstBankFailure.notValid valid.1
    let first : Proposal.Check code := .invalidBank request [doublyBadPoint] fresh common firstBankFailure
    let other : Proposal.Check code := .invalidBank request [doublyBadPoint] fresh common otherBankFailure
    let firstFailure := RawFailure.invalidStep 0 _ code first invalid
    let otherFailure := RawFailure.invalidStep 0 _ code other invalid
    (sameRawFailure firstFailure firstFailure, sameRawFailure firstFailure otherFailure))

private def compareInvalidRange (first second : RawFailure) : Option Bool :=
  match first, second with
  | .invalidRange firstPosition firstSaved firstAligned firstFailure,
    .invalidRange secondPosition secondSaved secondAligned secondFailure =>
    some (match RawFailure.compareInvalidRange firstPosition secondPosition
        firstSaved secondSaved firstAligned secondAligned firstFailure secondFailure with
      | .isTrue _ => true | .isFalse _ => false)
  | _, _ => none

private def bothRangeFrontier : Presentation.Frontier.Display :=
  ⟨(Unit.Presentation.read noCuts, [((⟨0, 1⟩, 0, 4), 1, 3, 3)]), by decide⟩

private def bothRangeLower : Presentation.Frontier.RangeFailure
    (Presentation.Frontier.readCells bothRangeFrontier.val.2 bothRangeFrontier.val.1.intervals
      bothRangeFrontier.property) := .lower bothRangeCell [] (by decide)

private def bothRangeUpper : Presentation.Frontier.RangeFailure
    (Presentation.Frontier.readCells bothRangeFrontier.val.2 bothRangeFrontier.val.1.intervals
      bothRangeFrontier.property) := .upper bothRangeCell [] (by decide)

example (first second : Presentation.Frontier.Valid bothRangeFrontier.val)
    (failure : Presentation.Frontier.RangeFailure
      (Presentation.Frontier.readCells bothRangeFrontier.val.2 bothRangeFrontier.val.1.intervals first)) :
    RawFailure.invalidRange 0 bothRangeFrontier.val first failure =
      RawFailure.invalidRange 0 bothRangeFrontier.val second failure := rfl

/-- info: some false -/
#guard_msgs in
#eval compareInvalidRange
  (.invalidRange 0 bothRangeFrontier.val bothRangeFrontier.property bothRangeLower)
  (.invalidRange 0 bothRangeFrontier.val bothRangeFrontier.property bothRangeUpper)

/-- info: (some true, some false, some false) -/
#guard_msgs in
#eval (let proposal := Proposal.Code.reused ⟨16, by decide⟩
  let lower : Presentation.History.RawStep := (badLowerFrontier.val, proposal)
  let upper : Presentation.History.RawStep := (badUpperFrontier.val, proposal)
  match Presentation.History.checkRaw [lower], Presentation.History.checkRaw [rawInitialStep, lower],
      Presentation.History.checkRaw [upper] with
  | .error first, .error later, .error different =>
    (compareInvalidRange first first, compareInvalidRange first later, compareInvalidRange first different)
  | _, _, _ => (none, none, none))

private def compareInvalidCells (first second : RawFailure) : Option Bool :=
  match first, second with
  | .invalidCells firstPosition firstSaved firstFailure,
    .invalidCells secondPosition secondSaved secondFailure =>
    some (match RawFailure.compareInvalidCells firstPosition secondPosition
        firstSaved secondSaved firstFailure secondFailure with
      | .isTrue _ => true | .isFalse _ => false)
  | _, _ => none

private def doublyBadCell : Presentation.Cell.Code := ((⟨0, 1⟩, -1, 0), -1, 0, 0)

private def belowStartResult : Presentation.Cell.Check doublyBadCell := .belowStart (by decide)

private def negativeWeightResult : Presentation.Cell.Check doublyBadCell := .negativeWeight (by decide)

private theorem doublyBadInvalid : ¬ Presentation.Cell.Valid doublyBadCell := by decide

private def firstCellFailure : Presentation.Frontier.Failure
    [doublyBadCell, doublyBadCell] [⟨0, 1⟩, ⟨0, 1⟩] :=
  .badCell doublyBadCell [doublyBadCell] ⟨0, 1⟩ [⟨0, 1⟩] belowStartResult doublyBadInvalid

private def otherCellReason : Presentation.Frontier.Failure
    [doublyBadCell, doublyBadCell] [⟨0, 1⟩, ⟨0, 1⟩] :=
  .badCell doublyBadCell [doublyBadCell] ⟨0, 1⟩ [⟨0, 1⟩] negativeWeightResult doublyBadInvalid

private def laterCellFailure : Presentation.Frontier.Failure
    [doublyBadCell, doublyBadCell] [⟨0, 1⟩, ⟨0, 1⟩] :=
  .later doublyBadCell ⟨0, 1⟩
    (.badCell doublyBadCell [] ⟨0, 1⟩ [] belowStartResult doublyBadInvalid)

example (first second : doublyBadCell.2.1 < 0) :
    Presentation.Cell.Check.negativeWeight first = Presentation.Cell.Check.negativeWeight second := rfl

/-- info: (true, true) -/
#guard_msgs in
#eval (match Presentation.Cell.Check.compare belowStartResult belowStartResult with
  | .isTrue _ => true | .isFalse _ => false,
  match Presentation.Cell.Check.compare belowStartResult negativeWeightResult with
  | .isTrue _ => false | .isFalse _ => true)

/-- info: (true, true, true) -/
#guard_msgs in
#eval (match Presentation.Frontier.Failure.compare firstCellFailure firstCellFailure with
    | .isTrue _ => true | .isFalse _ => false,
  match Presentation.Frontier.Failure.compare firstCellFailure otherCellReason with
    | .isTrue _ => false | .isFalse _ => true,
  match Presentation.Frontier.Failure.compare firstCellFailure laterCellFailure with
    | .isTrue _ => false | .isFalse _ => true)

/-- info: (some true, some false, some false) -/
#guard_msgs in
#eval (let proposal := Proposal.Code.reused ⟨16, by decide⟩
  let bad : Presentation.History.RawStep := (rawWrongReading, proposal)
  let other : Presentation.History.RawStep :=
    ((Unit.Presentation.read noCuts, [doublyBadCell]), proposal)
  match Presentation.History.checkRaw [bad], Presentation.History.checkRaw [rawInitialStep, bad],
      Presentation.History.checkRaw [other] with
  | .error first, .error later, .error different =>
    (compareInvalidCells first first, compareInvalidCells first later, compareInvalidCells first different)
  | _, _, _ => (none, none, none))

private def expectedAdjacent : Unit.Presentation.Check [1 / 3, 2 / 3, 1 / 3] :=
  .badAdjacent [1 / 3] (2 / 3) (1 / 3) [] rfl (by decide) (by decide)

/-- info: true -/
#guard_msgs in
#eval (let saved := rawInitialStep.1
  let step := rawInitialStep.2
  match Presentation.History.checkSavedCuts [1 / 3, 2 / 3, 1 / 3] saved.2 step with
  | .invalidCuts reason _ =>
      match Unit.Presentation.Check.compare reason expectedAdjacent with
      | .isTrue _ => true | .isFalse _ => false
  | _ => false)

/-- info: (true, true) -/
#guard_msgs in
#eval (let cuts : Unit.Presentation.Code := [1 / 2, 0, 0]
  let saved := rawInitialStep.1
  let step := rawInitialStep.2
  (match Partition.Unit.Occurrence.check cuts 1 with
    | .accepted selected _ => selected.index.val == 1 && selected.entry == 0
    | _ => false,
   match Presentation.History.checkSavedCuts cuts saved.2 step with
    | .invalidCuts (.outOfRange index _) _ => index.val == 1
    | _ => false))

example (frontier : SourceFrontier Source.value)
    (step : Proposal.Code Presentation.History.initial.1) :=
  Presentation.History.checkSavedCuts_quote frontier step

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval (let saved := rawInitialStep.1
  let step := rawInitialStep.2
  let checked := Presentation.History.checkSavedCuts saved.1.cuts saved.2 step
  (match checked.step with
    | some input => match Presentation.History.scanFrom Presentation.History.initial 0 [input] with
      | .ok _ => true | .error _ => false
    | none => false,
   match Presentation.History.checkSavedCuts [0] saved.2 step with
    | .invalidCuts (.outOfRange ..) _ => true | _ => false,
   match Presentation.History.checkSavedCuts [1 / 2, 1 / 2] saved.2 step with
    | .invalidCuts (.badAdjacent ..) _ => true | _ => false,
   match Presentation.History.checkSavedCuts [] rawWrongReading.2 step with
    | .checked _ _ _ (.invalidCells failure) => isWrongFrontierReading failure | _ => false,
   let other := (Presentation.Frontier.quote Source.coarse.frontier).val
   match (Presentation.History.checkSavedCuts other.1.cuts other.2 step).step with
    | some input => match Presentation.History.scanFrom Presentation.History.initial 0 [input] with
      | .error (.wrongPrevious ..) => true | _ => false
    | none => false))

private def isLaterRawFailure (failure : RawFailure) : Nat :=
  match failure with
  | .wrongPrevious position _ _ _ => if position == 1 then 1 else 0
  | .invalidCells position _ reason => if position == 1 && isWrongFrontierReading reason then 2 else 0
  | .invalidRange position _ _ reason => if position == 1 && isLowerRangeFailure reason then 3 else 0
  | _ => 0

/-- info: (true, true, true) -/
#guard_msgs in
#eval (let proposal := Proposal.Code.reused ⟨16, by decide⟩
  let check (entry : Presentation.History.RawStep) :=
    Presentation.History.checkCuts ([rawInitialStep, entry].map Presentation.History.cutsStep)
  ( (match check ((Presentation.Frontier.quote Source.coarse.frontier).val, proposal) with
      | .error (.invalidSaved failure) => isLaterRawFailure failure == 1 | _ => false),
    (match check (rawWrongReading, proposal) with
      | .error (.invalidSaved failure) => isLaterRawFailure failure == 2 | _ => false),
    (match check (badLowerFrontier.val, proposal) with
      | .error (.invalidSaved failure) => isLaterRawFailure failure == 3 | _ => false)))

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval ((match Presentation.History.checkRaw [rawInitialStep, rawInitialStep] with
    | .ok state =>
      match Presentation.History.compare (Presentation.History.display state)
          (Presentation.History.display continuedHistory) with
      | .isTrue _ => false | .isFalse _ => true
    | .error _ => false),
  (match Presentation.History.checkRaw [rawInitialStep,
      ((Presentation.Frontier.quote Source.coarse.frontier).val, .reused ⟨16, by decide⟩)] with
    | .error failure => isLaterRawFailure failure == 1 | .ok _ => false),
  (match Presentation.History.checkRaw [rawInitialStep, (rawWrongReading, .reused ⟨16, by decide⟩)] with
    | .error failure => isLaterRawFailure failure == 2 | .ok _ => false),
  (match Presentation.History.checkRaw [rawInitialStep, (badLowerFrontier.val, .reused ⟨16, by decide⟩)] with
    | .error failure => isLaterRawFailure failure == 3 | .ok _ => false))

/-- info: (true, true, true, true, true, true) -/
#guard_msgs in
#eval (let wrongPrevious : Presentation.History.RawCode := [rawInitialStep,
    ((Presentation.Frontier.quote Source.coarse.frontier).val, .reused ⟨16, by decide⟩)]
  let wrongCache : Presentation.History.RawCode := [rawInitialStep, (rawWrongReading, .reused ⟨16, by decide⟩)]
  let wrongRange : Presentation.History.RawCode := [rawInitialStep, (badLowerFrontier.val, .reused ⟨16, by decide⟩)]
  ((match Integral.PairedPresentation.checkRaw wrongPrevious [] with
    | .invalidLower failure _ => isLaterRawFailure failure == 1 | _ => false),
   (match Integral.PairedPresentation.checkRaw [] wrongPrevious with
    | .invalidUpper failure _ => isLaterRawFailure failure == 1 | _ => false),
   (match Integral.PairedPresentation.checkRaw wrongCache [] with
    | .invalidLower failure _ => isLaterRawFailure failure == 2 | _ => false),
   (match Integral.PairedPresentation.checkRaw [] wrongCache with
    | .invalidUpper failure _ => isLaterRawFailure failure == 2 | _ => false),
   (match Integral.PairedPresentation.checkRaw wrongRange [] with
    | .invalidLower failure _ => isLaterRawFailure failure == 3 | _ => false),
   (match Integral.PairedPresentation.checkRaw [] wrongRange with
    | .invalidUpper failure _ => isLaterRawFailure failure == 3 | _ => false)))

example (observation : Integral.PairedPresentation.Observation) :
    ∃ (result : Integral.PairedPresentation.Observation)
      (lowerEq : Presentation.History.quoteRaw result.lowerState =
        (Integral.PairedPresentation.quoteRaw observation).1)
      (upperEq : Presentation.History.quoteRaw result.upperState =
        (Integral.PairedPresentation.quoteRaw observation).2),
      Integral.PairedPresentation.checkRaw (Integral.PairedPresentation.quoteRaw observation).1
        (Integral.PairedPresentation.quoteRaw observation).2 = .accepted result lowerEq upperEq ∧
          result = observation := Integral.PairedPresentation.checkRaw_quoteRaw observation

example (state : Presentation.History.State) :
    Presentation.History.checkRaw (Presentation.History.quoteRaw state) = .ok state :=
  Presentation.History.checkRaw_quoteRaw state

example (code : Presentation.History.RawCode) (state result : Presentation.History.State) (position : Nat)
    (success : Presentation.History.scanRawFrom state position code = .ok result) :
    Presentation.History.quoteRaw result = Presentation.History.quoteRaw state ++ code :=
  Presentation.History.quoteRaw_scanRawFrom code state result position success

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval ((match Presentation.Frontier.checkCompleteRaw [] [frontierCell] with
    | .accepted .. => true | _ => false),
  (match Presentation.Frontier.checkCompleteRaw [0] [frontierCell] with
    | .invalidCuts .. => true | _ => false),
  (match Presentation.Frontier.checkCompleteRaw [] [((⟨0, 1⟩, 0, 2), 1, 2, 4)] with
    | .invalidCells _ _ _ failure => isWrongFrontierReading failure | _ => false),
  (match Presentation.Frontier.checkComplete badLowerFrontier.val with
    | .invalidRange _ failure => isLowerRangeFailure failure | _ => false),
  (match Presentation.Frontier.checkComplete badUpperFrontier.val with
    | .invalidRange _ failure => isUpperRangeFailure failure | _ => false))

/-- info: (true, true) -/
#guard_msgs in
#eval ((match Presentation.History.checkSaved (Presentation.Frontier.quote Source.endpointFrontier).val
      (.reused ⟨16, by decide⟩) with
    | .checked _ _ owner _ (.accepted ..) =>
      match Presentation.History.compareFrontier owner Source.endpointFrontier with
      | .isTrue _ => true | .isFalse _ => false
    | _ => false),
  isSavedLowerFailure (Presentation.History.checkSaved badLowerFrontier.val (.reused ⟨16, by decide⟩)))

/-- info: (true, true) -/
#guard_msgs in
#eval ((match (Presentation.History.checkSaved
      (Presentation.Frontier.quote Presentation.History.initial.1).val (.reused ⟨16, by decide⟩)).step with
    | some step => match Presentation.History.check [step] with | .ok _ => true | .error _ => false
    | none => false),
  (match (Presentation.History.checkSaved badLowerFrontier.val (.reused ⟨16, by decide⟩)).step with
    | none => true | some _ => false))

/-- info: (true, true, true) -/
#guard_msgs in
#eval ((match Presentation.Frontier.checkSourceRange (Presentation.Frontier.quote Source.endpointFrontier) with
    | .accepted _ => true | .rejected _ => false),
  (match Presentation.Frontier.checkSourceRange badLowerFrontier with
    | .rejected (.lower ..) => true | _ => false),
  (match Presentation.Frontier.checkSourceRange badUpperFrontier with
    | .rejected (.upper ..) => true | _ => false))

private def failureDepth : {cells : List (IntegrationCell (SourcePoint Source.value))} →
    Presentation.Frontier.RangeFailure cells → Nat
  | _, .lower .. => 0
  | _, .upper .. => 0
  | _, .later _ failure => failureDepth failure + 1

private def isLaterFailure {cells : List (IntegrationCell (SourcePoint Source.value))}
    (result : Presentation.Frontier.RangeCheck cells) : Bool :=
  match result with
  | .accepted _ => false
  | .rejected failure => failureDepth failure == 1

/-- info: true -/
#guard_msgs in
#eval isLaterFailure (Presentation.Frontier.checkEndpoints
    [Presentation.Cell.read ⟨frontierCell, by decide⟩,
      Presentation.Cell.read ⟨((⟨0, 1⟩, 0, 4), 1, 3, 4), by decide⟩])

example (display : Presentation.Frontier.Display) :
    Presentation.Frontier.SourceRange display ↔
      Presentation.Frontier.EndpointRange
        (Presentation.Frontier.readCells display.val.2 display.val.1.intervals display.property) :=
  Presentation.Frontier.sourceRange_iff_endpoints display

example (display : Presentation.Frontier.Display)
    (failure : Presentation.Frontier.RangeFailure
      (Presentation.Frontier.readCells display.val.2 display.val.1.intervals display.property)) :
    ¬ Presentation.Frontier.SourceRange display := failure.notSourceRange display

example : (match Presentation.Frontier.checkCode (Presentation.Frontier.fromCuts noCuts [frontierCell]) with
    | .accepted _ => true | .rejected _ => false) = true := by decide

example : (match Presentation.Frontier.check [frontierCell] [⟨0, 1⟩] with
    | .accepted _ => true | .rejected _ => false) = true := by decide

example : (match Presentation.Frontier.check [frontierCell] [⟨0, 2⟩] with
    | .rejected (.wrongDomain ..) => true | _ => false) = true := by decide

example : (match Presentation.Frontier.check [frontierCell, frontierCell] [⟨0, 1⟩, ⟨1, 2⟩] with
    | .rejected (.later _ _ (.wrongDomain ..)) => true | _ => false) = true := by decide

example : (match Presentation.Frontier.check [((⟨0, 1⟩, 0, 4), 2, 2, 4)] [⟨0, 1⟩] with
    | .rejected (.wrongWeight ..) => true | _ => false) = true := by decide

example : (match Presentation.Frontier.check
    [frontierCell, ((⟨0, 1⟩, 0, 2), 1, 2, 4)] [⟨0, 1⟩, ⟨0, 1⟩] with
    | .rejected (.later _ _ (.badCell _ _ _ _ (.wrongReading _) _)) => true
    | _ => false) = true := by decide

example : (match Presentation.Frontier.check [] [⟨0, 1⟩] with
    | .rejected (.missingCell ..) => true | _ => false) = true := by decide

example : (match Presentation.Frontier.check [frontierCell] [] with
    | .rejected (.extraCell ..) => true | _ => false) = true := by decide

example : Presentation.Frontier.read (Presentation.Frontier.quote Source.endpointFrontier)
    (Presentation.Frontier.quote_sourceRange Source.endpointFrontier) = Source.endpointFrontier :=
  Presentation.Frontier.read_quote Source.endpointFrontier _

example : Presentation.Frontier.read (Presentation.Frontier.quote Source.coarse.frontier)
    (Presentation.Frontier.quote_sourceRange Source.coarse.frontier) = Source.coarse.frontier :=
  Presentation.Frontier.read_quote Source.coarse.frontier _

example : (match Presentation.Frontier.checkCode (Presentation.Frontier.quote Source.endpointFrontier).val with
    | .accepted _ => true | .rejected _ => false) = true := by decide

example (display : Presentation.Frontier.Display) (first second : Presentation.Frontier.SourceRange display) :
    Presentation.Frontier.read display first = Presentation.Frontier.read display second := by rfl

example (left right : Presentation.Frontier.Display) (leftRange : Presentation.Frontier.SourceRange left)
    (rightRange : Presentation.Frontier.SourceRange right) :
    Presentation.Frontier.Same left right ↔
      Presentation.Frontier.read left leftRange = Presentation.Frontier.read right rightRange :=
  Presentation.Frontier.same_iff_read_eq left right leftRange rightRange

example : Source.value 0 = 4 := by decide

example : Source.value 1 = 2 := by decide

example : Source.value (1 / 2) = 16 / 5 := by decide

example : Source.polygonFirst.re = 2 := by decide

example : UnitCircle.Polygon.quarterArea 1 = 14 / 5 := by decide

example : (Gaussian.Pi.Polygon.sample 1).re = 14 / 5 := by decide

example : 3 ≤ Source.polygonRefinedStage := Source.polygonRefinedStage_floor

example : Gaussian.Pi.Polygon.approximation.radiusSq Source.polygonRefinedStage < 4 :=
  Source.polygonRefinedStage_accurate

example : Source.polygonIntegralComparison.leftIndex = 5 := by decide

example : Source.polygonIntegralComparison.rightIndex = 3 := by decide

example {polygonStage integralStage : Nat}
    (polygonFloor : Source.polygonIntegralComparison.leftIndex ≤ polygonStage)
    (integralFloor : Source.polygonIntegralComparison.rightIndex ≤ integralStage) :
    Norm.Basic.normSq
      ((Gaussian.Name.Sampling.approximation Gaussian.Pi.Polygon.named.name).sample polygonStage -
        (Gaussian.Name.Sampling.approximation Gaussian.Pi.Integral.named.name).sample integralStage) < 4 :=
  Source.polygonIntegralComparison.close polygonFloor integralFloor

example (stage : Nat) : (Gaussian.Pi.Polygon.approximation.sample stage).im = 0 :=
  Gaussian.Pi.Polygon.sample_im_zero stage

example (current : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    current ≤ Gaussian.Pi.Polygon.approximation.refineIndex current target positive ∧
      Gaussian.Pi.Polygon.approximation.radiusSq
        (Gaussian.Pi.Polygon.approximation.refineIndex current target positive) < target :=
  ⟨Gaussian.Pi.Polygon.approximation.refineIndex_ge current target positive,
    Gaussian.Pi.Polygon.approximation.refineIndex_accurate current target positive⟩

example (time : Fraction.Rational) (lower : 0 ≤ time) (upper : time ≤ 1) :
    2 ≤ Source.value time ∧ Source.value time ≤ 4 :=
  ⟨Source.two_le_value lower upper, Source.value_le_four time⟩

example : 0 < Source.modulus.radius 8 := Source.modulus.radius_pos 8 (by decide)

example : Source.coarse.preparation.request.tolerance = 16 := rfl

example : Source.cached.preparation.request.tolerance = 8 := by
  unfold Purelib.Examples.Approximation.Rational.Pi.Source.cached
  rw [Source.producer.requestCached_eq]
  rfl

example : Source.retainedReadings.length = Source.coarse.frontier.cells.length := by
  simp only [Source.retainedReadings, List.length_map]

#eval (Source.coarse.frontier.cells.length, Source.retainedReadings.length,
  Source.cached.frontier.cells.length, Source.coarse.answer.num, Source.coarse.answer.den)

example : Integral.answer Source.initialHistory =
    (Source.producer.request ⟨1, by decide⟩).answer := Integral.answer_initial

example (index : Nat) :
    ((Purelib.Approximation.Gaussian.Name.Sampling.approximation Integral.named.name).sample index).im = 0 :=
  Integral.sample_im_zero index

example : (Source.boundProcess.bound Source.firstHistory).Overlaps
    (Source.boundProcess.bound Source.secondHistory) := Source.history_overlap

example : Integral.process.refine Source.initialHistory 4 (by decide) =
    Source.boundProcess.request Source.initialHistory
      (Purelib.Approximation.Rational.Request.Square.gapTarget 4) (by decide) := by
  exact Integral.refine_eq Source.initialHistory 4 (by decide)

#eval (Source.initialHistory.1.cells.length, Source.firstHistory.1.cells.length,
  Source.secondHistory.1.cells.length, (Integral.answer Source.initialHistory).num,
  (Integral.answer Source.initialHistory).den)

example (cell : IntegrationCell (SourcePoint Source.value))
    (member : cell ∈ Source.endpointFrontier.cells) :
    cell.item.point = cell.item.interval.start ∧
      cell.lower = Source.value cell.item.interval.finish ∧
      cell.upper = Source.value cell.item.interval.start :=
  Endpoint.frontier_endpoints 1 cell member

example (cell : IntegrationCell (SourcePoint Source.value))
    (member : cell ∈ Source.endpointFrontier.cells) : cell.weight = 1 / 2 :=
  Endpoint.frontier_weight 1 cell member

example : (integralBound (Endpoint.frontier 0).cells).width = 2 := by decide

example : (integralBound Source.endpointFrontier.cells).width = 1 := by decide

example : (integralBound (Endpoint.frontier 2).cells).width = 2 / 3 := by decide

example (extra : Nat) : (integralBound (Endpoint.frontier extra).cells).width =
    2 / ((extra + 1 : Nat) : Fraction.Rational) := Endpoint.frontier_width extra

example (state : Source.boundProcess.State) (extra : Nat) (reading : Fraction.Rational)
    (inside : (integralBound (Endpoint.frontier extra).cells).Contains reading) :
    Fraction.abs (Integral.answer state - reading) ≤
      (Source.boundProcess.bound state).width + 2 / ((extra + 1 : Nat) : Fraction.Rational) :=
  Integral.answer_endpoint_difference_le_mesh state extra reading inside

example (extra : Nat) :
    (integralBound (Endpoint.frontier extra).cells).Contains
      (UnitCircle.Polygon.area extra) :=
  Polygon.area_in_frontier extra

example {first second : Fraction.Rational} (nonnegative : 0 ≤ first) (ordered : first ≤ second) :
    (second - first) * (1 / (1 + second ^ 2)) ≤
      (second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)) ∧
    (second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)) ≤
      (second - first) * (1 / (1 + first ^ 2)) :=
  Polygon.edge_unscaled_bounds nonnegative ordered

example : (integralBound (Endpoint.frontier 1).cells).Contains (14 / 5) := by
  have inside := Polygon.area_in_frontier 1
  have area : UnitCircle.Polygon.area 1 = 14 / 5 := by decide
  rw [area] at inside
  exact inside

example (state : Source.boundProcess.State) (extra : Nat) :
    Fraction.abs (Integral.answer state - UnitCircle.Polygon.area extra) ≤
      (Source.boundProcess.bound state).width + 2 / ((extra + 1 : Nat) : Fraction.Rational) :=
  Integral.answer_endpoint_difference_le_mesh state extra _ (Polygon.area_in_frontier extra)

example : Interval.Refines (integralBound (Endpoint.frontier 1).cells)
    (integralBound (Endpoint.frontier 0).cells) := by
  exact Polygon.doubled_frontier_refines 0

example (earlier later : Nat) (ordered : earlier ≤ later) :
    Interval.Refines (integralBound (Endpoint.frontier (Polygon.dyadicExtra later)).cells)
      (integralBound (Endpoint.frontier (Polygon.dyadicExtra earlier)).cells) :=
  Polygon.dyadic_frontier_refines ordered

example (earlier later : Nat) (ordered : earlier ≤ later) :
    Fraction.abs (UnitCircle.Polygon.area (Polygon.dyadicExtra later) -
      UnitCircle.Polygon.area (Polygon.dyadicExtra earlier)) ≤
      2 / ((2 ^ earlier : Nat) : Fraction.Rational) :=
  Polygon.dyadic_area_abs_difference_le ordered

example (earlier later : Nat) (ordered : earlier ≤ later) :
    Norm.Basic.normSq
      (RationalEmbedding.realPoint
          (UnitCircle.Polygon.area (Polygon.dyadicExtra later)) -
        RationalEmbedding.realPoint
          (UnitCircle.Polygon.area (Polygon.dyadicExtra earlier))) ≤
      4 * (1 / 4 : Fraction.Rational) ^ earlier :=
  Polygon.dyadic_area_normSq_difference_le_quarter ordered

example : Interval.Refines (integralBound (Endpoint.frontier (Polygon.dyadicExtra 3)).cells)
    (integralBound (Endpoint.frontier (Polygon.dyadicExtra 1)).cells) :=
  Polygon.dyadic_frontier_refines (by decide)

example (fine coarse : Nat)
    (nested : Interval.Refines (integralBound (Endpoint.frontier fine).cells)
      (integralBound (Endpoint.frontier coarse).cells)) :
    Fraction.abs (UnitCircle.Polygon.area fine -
      UnitCircle.Polygon.area coarse) ≤
      2 / ((coarse + 1 : Nat) : Fraction.Rational) :=
  Polygon.area_abs_difference_le_of_refines fine coarse nested

example (fine coarse : Nat)
    (nested : Interval.Refines (integralBound (Endpoint.frontier fine).cells)
      (integralBound (Endpoint.frontier coarse).cells)) :
    Norm.Basic.normSq
      (RationalEmbedding.realPoint
          (UnitCircle.Polygon.area fine) -
        RationalEmbedding.realPoint
          (UnitCircle.Polygon.area coarse)) ≤
      (2 / ((coarse + 1 : Nat) : Fraction.Rational)) ^ 2 :=
  Polygon.area_normSq_difference_le_of_refines fine coarse nested

#eval ((Endpoint.frontier 0).cells.length,
  (integralBound (Endpoint.frontier 0).cells).lower.num,
  (integralBound (Endpoint.frontier 0).cells).lower.den,
  (integralBound (Endpoint.frontier 0).cells).upper.num,
  (integralBound (Endpoint.frontier 0).cells).upper.den,
  Source.endpointFrontier.cells.length,
  (integralBound Source.endpointFrontier.cells).lower.num,
  (integralBound Source.endpointFrontier.cells).lower.den,
  (integralBound Source.endpointFrontier.cells).upper.num,
  (integralBound Source.endpointFrontier.cells).upper.den)

end TestPurelib.Approximation.Rational.Pi.Source
