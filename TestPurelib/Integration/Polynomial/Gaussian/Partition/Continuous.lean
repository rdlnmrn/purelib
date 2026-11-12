module
import Purelib.Integration.Polynomial.Gaussian.Partition.Continuous
import Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous
import Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation
import Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation.Independent
import Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation.Runner
import Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation.Runner.Independent

/-! Original Gaussian segment compilations in finite rational source enclosures. -/

namespace TestPurelib.Integration.Polynomial.Gaussian.Partition.Continuous

open Purelib.CCL.Progressive.IntegrationPrograms
open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Integration
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Partition
open Purelib.Integration.Polynomial.Gaussian.Partition.Continuous
open Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation
open Purelib.Integration.Polynomial.Rational.Continuous

/-- A nonconstant Gaussian polynomial on a segment with non-real displacement. -/
private def source : Segment.Basic.PolynomialSegment :=
  ⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨[⟨1, 2⟩, ⟨2, 0⟩]⟩⟩

/-- Two independently compiled partitions retain the same original segment owner. -/
private def first := Segment.CompiledSegment.canonical source [1 / 2]
private def second := Segment.CompiledSegment.canonical source [1 / 3, 2 / 3]

/-- The original segment followed by its oriented reverse. -/
private def path : Partition.Source.PolynomialPath := [source, source.reversed]

/-- Two original path compilations retain independent cut requests on each segment. -/
private def leftPath : Partition.Cells.CompiledCells path :=
  .cons first (.cons (Segment.CompiledSegment.canonical source.reversed [1 / 3]) .nil)
private def rightPath : Partition.Cells.CompiledCells path :=
  .cons second (.cons (Segment.CompiledSegment.canonical source.reversed [1 / 2]) .nil)

/-- Two independent rational integration requests. -/
private def firstRequest : AccuracyRequest := ⟨8, by decide⟩
private def secondRequest : AccuracyRequest := ⟨4, by decide⟩

/-- Independent saved histories of the same original multi-segment source process. -/
private def process := Cells.Continuous.boundProcess path
private def saved := process.request process.initial firstRequest.tolerance firstRequest.positive
private def continued := process.request saved secondRequest.tolerance secondRequest.positive
private def independent := process.request process.initial secondRequest.tolerance secondRequest.positive

example : (Partition.Continuous.projected source).eval 0 = (-1 : Fraction.Rational) ∧
    (Partition.Continuous.projected source).eval 1 = 1 := by decide +kernel

example : (integralBound (Partition.Continuous.integrate source firstRequest).frontier.cells).Contains
    first.sample.re := Partition.Continuous.compiled_sample_contains first firstRequest

example : (integralBound (Partition.Continuous.integrate source secondRequest).frontier.cells).Contains
    second.sample.re := Partition.Continuous.compiled_sample_contains second secondRequest

example : Fraction.abs (first.sample.re - second.sample.re) ≤
    (integralBound (Partition.Continuous.integrate source firstRequest).frontier.cells).width +
      (integralBound (Partition.Continuous.integrate source secondRequest).frontier.cells).width :=
  Partition.Continuous.compiled_samples_difference_le first second firstRequest secondRequest

example : (process.bound continued).Contains leftPath.sample.re :=
  Cells.Continuous.sample_contains leftPath continued

example : (process.bound independent).Contains rightPath.sample.re :=
  Cells.Continuous.sample_contains rightPath independent

example : Fraction.abs ((process.bound continued).midpoint - (process.bound independent).midpoint) ≤
    (process.bound continued).width + (process.bound independent).width :=
  Cells.Continuous.midpoints_difference_le leftPath rightPath continued independent

/-- The imaginary source retains the same nonreal segment and its signed displacement. -/
private def imaginaryProcess := Cells.Continuous.imaginaryBoundProcess [source]
private def imaginarySaved :=
  imaginaryProcess.request imaginaryProcess.initial firstRequest.tolerance firstRequest.positive
private def imaginaryIndependent :=
  imaginaryProcess.request imaginaryProcess.initial secondRequest.tolerance secondRequest.positive

/-- One-segment compilations retain the original nonzero imaginary sample. -/
private def singleLeft : Partition.Cells.CompiledCells [source] := .cons first .nil
private def singleRight : Partition.Cells.CompiledCells [source] := .cons second .nil
private def singleReal := Cells.Continuous.boundProcess [source]
private def realSaved := singleReal.request singleReal.initial firstRequest.tolerance firstRequest.positive
private def realIndependent := singleReal.request singleReal.initial secondRequest.tolerance secondRequest.positive

example : (Partition.Continuous.projectedIm source).eval 0 = (3 : Fraction.Rational) ∧
    (Partition.Continuous.projectedIm source).eval 1 = 5 := by decide +kernel

example : first.sample.im = (4 : Fraction.Rational) := by decide +kernel

example : (integralBound (Partition.Continuous.integrateIm source firstRequest).frontier.cells).Contains
    first.sample.im := Partition.Continuous.compiled_im_sample_contains first firstRequest

example : (imaginaryProcess.bound imaginarySaved).Contains singleLeft.sample.im :=
  Cells.Continuous.imaginary_sample_contains singleLeft imaginarySaved

example : (singleReal.bound realSaved).Contains singleLeft.sample.re ∧
    (imaginaryProcess.bound imaginarySaved).Contains singleLeft.sample.im :=
  Cells.Continuous.sample_coordinates_contained singleLeft realSaved imaginarySaved

example : Norm.Basic.normSq
    (Cells.Continuous.midpoint [source] realSaved imaginarySaved -
      Cells.Continuous.midpoint [source] realIndependent imaginaryIndependent) ≤
    ((singleReal.bound realSaved).width + (singleReal.bound realIndependent).width) ^ 2 +
      ((imaginaryProcess.bound imaginarySaved).width + (imaginaryProcess.bound imaginaryIndependent).width) ^ 2 :=
  Cells.Continuous.midpoints_normSq_le singleLeft singleRight realSaved realIndependent
    imaginarySaved imaginaryIndependent

example : Norm.Basic.normSq (singleLeft.sample -
    Cells.Continuous.midpoint [source] realSaved imaginarySaved) ≤
      ((singleReal.bound realSaved).width * (1 / 2)) ^ 2 +
        ((imaginaryProcess.bound imaginarySaved).width * (1 / 2)) ^ 2 :=
  Cells.Continuous.sample_midpoint_normSq_le singleLeft realSaved imaginarySaved

/-- Reversal retains the original nonzero imaginary segment sample with opposite orientation. -/
private def reversedSegment := Segment.CompiledSegment.canonical source.reversed [1 / 3]

example : reversedSegment.sample.im = (-4 : Fraction.Rational) := by decide +kernel

example : (integralBound (Partition.Continuous.integrateIm source.reversed firstRequest).frontier.cells).Contains
    reversedSegment.sample.im := Partition.Continuous.compiled_im_sample_contains reversedSegment firstRequest

/-- A zero-displacement original segment has zero real and imaginary sample. -/
private def stationary : Segment.Basic.PolynomialSegment := ⟨⟨1, 1⟩, ⟨1, 1⟩, source.polynomial⟩
private def stationaryCompiled := Segment.CompiledSegment.canonical stationary []

example : stationaryCompiled.sample.re = 0 ∧ stationaryCompiled.sample.im = 0 := by decide +kernel

example : (integralBound (Partition.Continuous.integrateIm stationary firstRequest).frontier.cells).Contains
    stationaryCompiled.sample.im := Partition.Continuous.compiled_im_sample_contains stationaryCompiled firstRequest

/-- Original real and imaginary source processes for the same oriented segment. -/
private def realSource := integrationProcess (Partition.Continuous.projected source)

/-- The imaginary source retains the same original oriented segment. -/
private def imaginarySource :=
  integrationProcess (Partition.Continuous.projectedIm source)

/-- Independent original coordinate sources for the reversed oriented segment. -/
private def reverseRealSource := integrationProcess (Partition.Continuous.projected source.reversed)
private def reverseImaginarySource := integrationProcess (Partition.Continuous.projectedIm source.reversed)

/-- A tighter finite request forces both original coordinate histories to continue. -/
private def tighter : AccuracyRequest := ⟨1 / 2, by decide⟩

/-- The original pair of coordinate source requests from their retained initial histories. -/
private def coordinateProgram :=
  Observation.computation source realSource.initial imaginarySource.initial tighter tighter

/-- Original source replies for both coordinate histories. -/
private def coordinateOracle := Observation.originalReply source tighter tighter

/-- Different source owners and meshes retain the actual nonreal and reversed segment frontiers. -/
private def comparisonReal := realSource.request realSource.initial tighter.tolerance tighter.positive
private def comparisonImaginary := imaginarySource.request imaginarySource.initial tighter.tolerance tighter.positive
private def independentSegment := Observation.Independent.computation source source.reversed
  comparisonReal reverseRealSource.initial comparisonImaginary reverseImaginarySource.initial none none
private def independentSegmentOracle := Observation.Independent.original source source.reversed

example := Observation.Independent.computation_original source source.reversed
  comparisonReal reverseRealSource.initial comparisonImaginary reverseImaginarySource.initial none none

/-- The original imaginary path process and its retained nonempty history. -/
private def imaginaryPath := Cells.Continuous.imaginaryBoundProcess path
private def savedImaginaryPath :=
  imaginaryPath.request imaginaryPath.initial firstRequest.tolerance firstRequest.positive

/-- Resume both original ordered path processes from their retained histories. -/
private def pathProgram :=
  computation path saved savedImaginaryPath tighter tighter

/-- Original rational replies for the same two source occurrences. -/
private def pathOracle := pathReply path tighter tighter

/-- The original polynomial policy, model runner and ordered path requests. -/
private def policy : PartitionPolicy path := .uniform 1 0
private def retained := Retained.canonical path policy
private def integrationRequest : CertifiedProgram.Request := ⟨0, 1, by decide⟩
private def runnerInput : Runner.Input path policy :=
  ⟨retained, integrationRequest, 2, saved, savedImaginaryPath, tighter, tighter, []⟩
private def runnerProgram := Runner.computation runnerInput
private def runnerOracle := Runner.originalReply runnerInput

/-- An independent original policy and saved path state for the same source. -/
private def otherPolicy : PartitionPolicy path := .uniform 2 1
private def otherRetained := Retained.canonical path otherPolicy
private def otherRunnerInput : Runner.Input path otherPolicy :=
  ⟨otherRetained, integrationRequest, 2, independent, imaginaryPath.initial, tighter, tighter, []⟩

/-- A distinct path pairs a reversed nonreal segment with a stationary segment. -/
private def mismatchedPath : Partition.Source.PolynomialPath := [source.reversed, stationary]
private def mismatchedPolicy : PartitionPolicy mismatchedPath := .uniform 2 1
private def mismatchedRetained := Retained.canonical mismatchedPath mismatchedPolicy
private def mismatchedReal := Cells.Continuous.boundProcess mismatchedPath
private def mismatchedImaginary := Cells.Continuous.imaginaryBoundProcess mismatchedPath
private def mismatchedRunnerInput : Runner.Input mismatchedPath mismatchedPolicy :=
  ⟨mismatchedRetained, integrationRequest, 2, mismatchedReal.initial, mismatchedImaginary.initial, tighter, tighter, []⟩

/-- Explicitly align the two actual source occurrences in their original order. -/
private def independentAlignment : Cells.Continuous.Observation.Independent.Alignment path mismatchedPath :=
  .cons (.cons .nil)
private def independentRunner := Runner.Independent.computation runnerInput mismatchedRunnerInput independentAlignment
private def independentRunnerOracle :=
  Runner.Independent.original runnerInput mismatchedRunnerInput independentAlignment

example (left : Runner.Result runnerInput) (right : Runner.Result otherRunnerInput) :=
  Runner.Result.selected_samples_eq left right

example (left : Runner.Result runnerInput) (right : Runner.Result otherRunnerInput) :=
  Runner.Result.midpoints_normSq_le left right

example := Runner.computation_original runnerInput
example := Runner.computation_replay runnerInput runnerOracle

example (real : Observation.RealState source) (imaginary : Observation.ImaginaryState source) :=
  Observation.computation_original source real imaginary tighter tighter

example (real : Observation.RealState source) (imaginary : Observation.ImaginaryState source) :=
  Observation.computation_replay source real imaginary tighter tighter

example : ((boundProcess (Partition.Continuous.projected source)).bound
      realSource.initial).Contains first.sample.re ∧
    ((boundProcess (Partition.Continuous.projectedIm source)).bound
      imaginarySource.initial).Contains first.sample.im :=
  Observation.sample_coordinates_contained first realSource.initial imaginarySource.initial

example := Observation.sample_midpoint_normSq_le first realSource.initial imaginarySource.initial

/-- Exercise both source owners, replay and typed early rejection for the original nonreal segment. -/
public def run : IO Unit := do
  let execution := coordinateProgram.protocol.run coordinateOracle
  if execution.trace.isEmpty then
    throw (IO.userError "polynomial coordinate request made no source observations")
  let mut realCount := 0
  let mut imaginaryCount := 0
  let mut imaginaryStarted := false
  for exchange in execution.trace do
    match exchange.query with
    | .inl _ =>
        if imaginaryStarted then
          throw (IO.userError "real polynomial request followed an imaginary request")
        realCount := realCount + 1
    | .inr _ =>
        imaginaryStarted := true
        imaginaryCount := imaginaryCount + 1
  unless realCount > 0 && imaginaryCount > 0 do
    throw (IO.userError "polynomial coordinate trace omitted one original source")
  let states ← match execution.value with
    | .ok states => pure states
    | .error _ => throw (IO.userError "original polynomial coordinate replies were rejected")
  let realBound := (boundProcess (Partition.Continuous.projected source)).bound states.1
  let imaginaryBound :=
    (boundProcess (Partition.Continuous.projectedIm source)).bound states.2
  unless decide (realBound.Contains first.sample.re ∧ imaginaryBound.Contains first.sample.im) do
    throw (IO.userError "coordinate enclosures lost the original nonreal segment sample")
  match coordinateProgram.protocol.replayExact execution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "polynomial coordinate source trace did not replay")
  let wrongOwner : Observation.Query source tighter tighter → Observation.Reply source := fun question =>
    match question with
    | .inl _ => .inr (Purelib.Integration.SourceFrontier.Continuous.Observation.Continuation.originalPoint
        (Partition.Continuous.projectedIm source).eval 0)
    | .inr _ => .inl (Purelib.Integration.SourceFrontier.Continuous.Observation.Continuation.originalPoint
        (Partition.Continuous.projected source).eval 0)
  let rejectedOwner := coordinateProgram.protocol.run wrongOwner
  match rejectedOwner.value with
  | .error (.owner _) =>
      unless rejectedOwner.trace.length == 1 do
        throw (IO.userError "wrong polynomial owner did not stop the first source request")
  | _ => throw (IO.userError "wrong polynomial coordinate owner was not rejected")
  let wrongTag : Observation.Query source tighter tighter → Observation.Reply source := fun question =>
    match question with
    | .inl _ => .inl (Purelib.Integration.SourceFrontier.Continuous.Observation.Continuation.originalPoint
        (Partition.Continuous.projected source).eval 2)
    | .inr _ => .inr (Purelib.Integration.SourceFrontier.Continuous.Observation.Continuation.originalPoint
        (Partition.Continuous.projectedIm source).eval 2)
  let rejectedTag := coordinateProgram.protocol.run wrongTag
  match rejectedTag.value with
  | .error (.real _) | .error (.imaginary _) =>
      unless rejectedTag.trace.length == 1 do
        throw (IO.userError "wrong polynomial tag did not stop the first source request")
  | _ => throw (IO.userError "wrong polynomial coordinate tag was not rejected")
  let comparedExecution := independentSegment.protocol.run independentSegmentOracle
  let compared ← match comparedExecution.value with
    | .error _ => throw (IO.userError "independent nonreal segment comparison rejected original replies")
    | .ok result => pure result
  if comparedExecution.trace.isEmpty then
    throw (IO.userError "independent segment comparison omitted its mismatched-mesh source requests")
  let realBudget := (integralBound comparisonReal.1.cells).width +
    (integralBound reverseRealSource.initial.1.cells).width + compared.real.val.pointBudget
  let imaginaryBudget := (integralBound comparisonImaginary.1.cells).width +
    (integralBound reverseImaginarySource.initial.1.cells).width + compared.imaginary.val.pointBudget
  unless decide (Norm.Basic.normSq (first.sample - reversedSegment.sample) ≤ realBudget ^ 2 + imaginaryBudget ^ 2) do
    throw (IO.userError "independent segment point budgets did not pay the nonreal reversed-sample bound")
  match independentSegment.protocol.replayExact comparedExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "independent segment comparison did not replay")
  let cachedSegment := Observation.Independent.computation source source.reversed
    comparisonReal reverseRealSource.initial comparisonImaginary reverseImaginarySource.initial
    (some compared.real) (some compared.imaginary)
  unless (cachedSegment.protocol.run independentSegmentOracle).trace.isEmpty do
    throw (IO.userError "independent segment comparison repeated cached common readings")
  let wrongSegmentOwner : Observation.Independent.Query →
      Observation.Independent.Reply source source.reversed := fun question =>
    match question with
    | .inl question => .inr (SourceFrontier.Comparison.Observation.originalReply
        (Partition.Continuous.projectedIm source).eval (Partition.Continuous.projectedIm source.reversed).eval question)
    | .inr question => .inl (SourceFrontier.Comparison.Observation.originalReply
        (Partition.Continuous.projected source).eval (Partition.Continuous.projected source.reversed).eval question)
  match (independentSegment.protocol.run wrongSegmentOwner).value with
  | .error (.realOwner _) => pure ()
  | _ => throw (IO.userError "independent segment comparison accepted the wrong coordinate owner")
  let independentExecution := independentRunner.protocol.run independentRunnerOracle
  let independentResult ← match independentExecution.value with
    | .ok result => pure result
    | .error _ => throw (IO.userError "independent polynomial runners rejected original replies")
  let realBudget := Cells.Continuous.Observation.Independent.realBudget independentAlignment
    independentResult.left.real independentResult.right.real independentResult.left.imaginary
    independentResult.right.imaginary independentResult.comparison
  let imaginaryBudget := Cells.Continuous.Observation.Independent.imaginaryBudget independentAlignment
    independentResult.left.real independentResult.right.real independentResult.left.imaginary
    independentResult.right.imaginary independentResult.comparison
  let sampleDifference := independentResult.left.recorded.observation.selected.sample -
    independentResult.right.recorded.observation.selected.sample
  unless decide (Norm.Basic.normSq sampleDifference ≤ realBudget ^ 2 + imaginaryBudget ^ 2) do
    throw (IO.userError "independent path point budgets did not pay the actual selected-sample bound")
  unless decide (sampleDifference.im ≠ 0) do
    throw (IO.userError "independent reversed/stationary path regression lost its nonreal difference")
  match independentRunner.protocol.replayExact independentExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "independent polynomial runner comparison did not replay")
  let repeatedComparison := independentResult.recompare.protocol.run
    (fun question => some (Cells.Continuous.Observation.Independent.original independentAlignment question))
  unless repeatedComparison.trace.isEmpty do
    throw (IO.userError "independent runner comparison repeated retained common-point requests")
  match repeatedComparison.value with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "retained independent runner comparison did not replay its cached values")
  let wrongSecond : Runner.Independent.Query runnerInput mismatchedRunnerInput independentAlignment →
      Runner.Independent.Reply runnerInput mismatchedRunnerInput independentAlignment := fun question =>
    match question with
    | .inr (.inr (.inr (.inl _))) => .inl (.inl (Runner.stageReply retained 0))
    | _ => independentRunnerOracle question
  match (independentRunner.protocol.run wrongSecond).value with
  | .error (.comparison _ _ (.inr (head, .inr (.inl (.inr invalid))))) =>
      unless !head.real.val.readings.isEmpty && !head.imaginary.val.readings.isEmpty do
        throw (IO.userError "wrong second segment lost the completed first segment comparison")
      match invalid with
      | .realOuter _ | .imaginaryOuter _ _ => pure ()
      | _ => throw (IO.userError "wrong second segment lost the actual outer-operation failure")
  | _ => throw (IO.userError "wrong second segment did not retain the completed first segment")
  let runnerExecution := runnerProgram.protocol.run runnerOracle
  let runnerResult ← match runnerExecution.value with
    | .error _ => throw (IO.userError "polynomial model runner and ordered path failed")
    | .ok result => pure result
  unless runnerResult.recorded.observation.selected.sample == runnerResult.selected.compiled.sample &&
      runnerResult.selected.compiled.sample == leftPath.sample && !runnerResult.recorded.trace.isEmpty do
    throw (IO.userError "polynomial runner lost its selected compiled partition or original model")
  unless decide ((process.bound runnerResult.real).Contains runnerResult.selected.compiled.sample.re ∧
      (imaginaryPath.bound runnerResult.imaginary).Contains runnerResult.selected.compiled.sample.im) do
    throw (IO.userError "polynomial runner's path bounds lost its selected compiled sample")
  let mut runnerLast := 0
  let mut runnerCounts := #[0, 0, 0, 0]
  let mut pathStarted := false
  for exchange in runnerExecution.trace do
    match exchange.query with
    | .inl _ =>
        if pathStarted then
          throw (IO.userError "polynomial model query followed a path query")
    | .inr question =>
        pathStarted := true
        let current ← match question with
          | .inl (.inl _) => pure 0
          | .inr (.inl (.inl _)) => pure 1
          | .inl (.inr _) => pure 2
          | .inr (.inl (.inr _)) => pure 3
          | .inr (.inr impossible) => nomatch impossible
        if current < runnerLast then
          throw (IO.userError "polynomial runner changed original path source order")
        runnerLast := current
        runnerCounts := runnerCounts.modify current (· + 1)
  unless runnerCounts.all (· > 0) do
    throw (IO.userError "polynomial runner omitted an original path coordinate")
  match runnerProgram.protocol.replayExact runnerExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "polynomial runner and path trace did not replay")
  let continuedInput := runnerResult.continuation integrationRequest 2 tighter tighter
  let continuedProgram := Runner.computation continuedInput
  let continuedExecution := continuedProgram.protocol.run (Runner.originalReply continuedInput)
  let continuedResult ← match continuedExecution.value with
    | .error _ => throw (IO.userError "polynomial runner continuation failed")
    | .ok result => pure result
  unless continuedResult.selected.compiled.sample == runnerResult.selected.compiled.sample &&
      continuedResult.bank.length == runnerResult.bank.length && continuedExecution.trace.isEmpty do
    throw (IO.userError "polynomial runner continuation did not reuse its returned bank and path states")
  match continuedProgram.protocol.replayExact continuedExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "polynomial runner continuation did not replay")
  let otherProgram := Runner.computation otherRunnerInput
  let otherExecution := otherProgram.protocol.run (Runner.originalReply otherRunnerInput)
  let otherResult ← match otherExecution.value with
    | .error _ => throw (IO.userError "independent polynomial runner and path failed")
    | .ok result => pure result
  unless runnerResult.recorded.observation.selected.sample == otherResult.recorded.observation.selected.sample do
    throw (IO.userError "independent polynomial runner stages disagree on their original source sample")
  let leftMidpoint := Cells.Continuous.midpoint path runnerResult.real runnerResult.imaginary
  let rightMidpoint := Cells.Continuous.midpoint path otherResult.real otherResult.imaginary
  unless decide (Norm.Basic.normSq (leftMidpoint - rightMidpoint) ≤
      ((process.bound runnerResult.real).width + (process.bound otherResult.real).width) ^ 2 +
      ((imaginaryPath.bound runnerResult.imaginary).width + (imaginaryPath.bound otherResult.imaginary).width) ^ 2) do
    throw (IO.userError "independent polynomial runner midpoints exceeded their returned width budget")
  match otherProgram.protocol.replayExact otherExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "independent polynomial runner trace did not replay")
  let wrongRunnerOracle (question : Runner.Question runnerInput) :
      Runner.Reply runnerInput :=
    match question with
    | .inl index => .inl (Runner.stageReply retained (index + 1))
    | _ => runnerOracle question
  let rejectedModel := runnerProgram.protocol.run wrongRunnerOracle
  match rejectedModel.value with
  | .error (.modelFailure (.index requested receipt bank _)) =>
      unless receipt.index == requested + 1 && bank.isEmpty && rejectedModel.trace.length == 1 do
        throw (IO.userError "polynomial runner lost its actual wrong-stage failure")
  | _ => throw (IO.userError "polynomial runner accepted a wrong compiled stage")
  let preloaded := Runner.stageReply retained 1000
  let preloadedInput : Runner.Input path policy := { runnerInput with bank := [preloaded] }
  let preloadedProgram := Runner.computation preloadedInput
  let preloadedOracle (question : Runner.Question preloadedInput) : Runner.Reply preloadedInput :=
    match question with
    | .inl index => .inl (Runner.stageReply retained (index + 1))
    | _ => Runner.originalReply preloadedInput question
  let rejectedWithBank := preloadedProgram.protocol.run preloadedOracle
  match rejectedWithBank.value with
  | .error (.modelFailure (.index requested receipt [savedReceipt] _)) =>
      unless receipt.index == requested + 1 && savedReceipt.index == preloaded.index &&
          savedReceipt.compiled.sample == preloaded.compiled.sample do
        throw (IO.userError "wrong polynomial stage discarded its original supplied bank")
  | _ => throw (IO.userError "wrong polynomial stage did not retain its supplied bank")
  let wrongPathOracle (question : Runner.Question runnerInput) :
      Runner.Reply runnerInput :=
    match question with
    | .inr _ => .inl (Runner.stageReply retained 0)
    | _ => runnerOracle question
  let rejectedPath := runnerProgram.protocol.run wrongPathOracle
  match rejectedPath.value with
  | .error (.pathOperation completed observation success _) =>
      let recorded := Runner.completedRecord runnerInput completed observation success
      let selected := Runner.completedSelection runnerInput completed observation success
      let modelMisses := rejectedPath.trace.filter fun exchange => match exchange.query with
        | .inl _ => true
        | .inr _ => false
      let pathAttempts := rejectedPath.trace.filter fun exchange => match exchange.query with
        | .inl _ => false
        | .inr _ => true
      unless !recorded.trace.isEmpty && selected.compiled.sample == runnerResult.selected.compiled.sample &&
          !completed.bank.isEmpty && !modelMisses.isEmpty && pathAttempts.length == 1 do
        throw (IO.userError "polynomial path failure lost its original selected compilation")
  | _ => throw (IO.userError "polynomial runner accepted a wrong path operation")
  let pathExecution := pathProgram.protocol.run pathOracle
  let mut counts := #[0, 0, 0, 0]
  let mut last := 0
  for exchange in pathExecution.trace do
    let current ← match exchange.query with
      | .inl (.inl _) => pure 0
      | .inr (.inl (.inl _)) => pure 1
      | .inl (.inr _) => pure 2
      | .inr (.inl (.inr _)) => pure 3
      | .inr (.inr impossible) => nomatch impossible
    if current < last then
      throw (IO.userError "polynomial path changed source or coordinate order")
    last := current
    counts := counts.modify current (· + 1)
  unless counts.all (· > 0) do
    throw (IO.userError "polynomial path omitted an original segment coordinate")
  let states ← match pathExecution.value with
    | .ok states => pure states
    | .error _ => throw (IO.userError "original polynomial path replies were rejected")
  unless decide ((process.bound states.1).Contains leftPath.sample.re ∧
      (imaginaryPath.bound states.2).Contains leftPath.sample.im) do
    throw (IO.userError "polynomial path enclosures lost the original compiled sample")
  match pathProgram.protocol.replayExact pathExecution.trace with
  | .ok (.ok _) => pure ()
  | _ => throw (IO.userError "polynomial path source trace did not replay")
  let wrongOccurrence : Query path tighter tighter →
      Reply path := fun _ =>
    .inr (.inl (.inl (Purelib.Integration.SourceFrontier.Continuous.Observation.Continuation.originalPoint
      (Partition.Continuous.projected source.reversed).eval 0)))
  let rejectedOccurrence := pathProgram.protocol.run wrongOccurrence
  match rejectedOccurrence.value with
  | .error (.owner _) =>
      unless rejectedOccurrence.trace.length == 1 do
        throw (IO.userError "wrong path occurrence did not stop the first source request")
  | _ => throw (IO.userError "wrong polynomial path occurrence was not rejected")

end TestPurelib.Integration.Polynomial.Gaussian.Partition.Continuous
