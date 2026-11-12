module

public import Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation
public import Purelib.Integration.Cell.Source.Comparison.Observation
import Purelib.Data.Gaussian.Norm.Coordinates
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Independent polynomial segment observations

Two original oriented segments retain their own real and imaginary source
frontiers. Their common-point queries keep the actual coordinate budgets;
no equality between the source owners is assumed.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation.Independent

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Segment.Basic
open Purelib.Integration.SourceFrontier
open Purelib.Integration.SourceFrontier.Comparison

variable (left right : PolynomialSegment) (leftReal : RealState left) (rightReal : RealState right)
  (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right)

/-- Real common readings retain both actual returned source frontiers. -/
abbrev RealCommon := Comparison.Observation.Certified leftReal.1 rightReal.1

/-- Imaginary common readings retain both actual returned source frontiers. -/
abbrev ImaginaryCommon := Comparison.Observation.Certified leftImaginary.1 rightImaginary.1

/-- A real or imaginary common-point source request. -/
abbrev Query := Sum Comparison.Observation.Query Comparison.Observation.Query

/-- A reply retains the original coordinate and source owner. -/
abbrev Reply := Sum (Comparison.Observation.Reply (projected left).eval (projected right).eval)
  (Comparison.Observation.Reply (projectedIm left).eval (projectedIm right).eval)

set_option genInjectivity false in
/-- A wrong coordinate or source reply, retaining completed real work. -/
inductive Failure where
  /-- An enclosing operation did not provide a source reply to the real request. -/ | realOuter
      (question : Comparison.Observation.Query)
  /-- A real request received an imaginary reply. -/ | realOwner (question : Comparison.Observation.Query)
  /-- A real-coordinate common-point reply was rejected. -/ | real (invalid : Comparison.Observation.Failure)
  /-- An enclosing operation did not provide a source reply to the imaginary request. -/ | imaginaryOuter
      (real : RealCommon left right leftReal rightReal) (question : Comparison.Observation.Query)
  /-- An imaginary request received a real reply. -/ | imaginaryOwner
      (real : RealCommon left right leftReal rightReal) (question : Comparison.Observation.Query)
  /-- An imaginary-coordinate common-point reply was rejected. -/ | imaginary
      (real : RealCommon left right leftReal rightReal) (invalid : Comparison.Observation.Failure)

constructive_injectivity Failure

set_option genInjectivity false in
/-- Returned real and imaginary common readings with their actual point budgets. -/
structure Result where
  /-- The returned common real-coordinate readings. -/ real : RealCommon left right leftReal rightReal
  /-- The returned common imaginary-coordinate readings. -/ imaginary :
    ImaginaryCommon left right leftImaginary rightImaginary

constructive_injectivity Result

/-- Reuse an already certified common value or observe the original common-point computation. -/
@[expose] def comparison {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftFrontier : SourceFrontier leftSource) (rightFrontier : SourceFrontier rightSource)
    (cached : Option (Comparison.Observation.Certified leftFrontier rightFrontier)) :
    Program Comparison.Observation.Query (Comparison.Observation.Reply leftSource rightSource)
      (Except Comparison.Observation.Failure (Comparison.Observation.Certified leftFrontier rightFrontier)) :=
  match cached with
  | some saved => .pure (.ok saved)
  | none => Comparison.Observation.certifiedComputation leftFrontier rightFrontier

/-- Original replies return the exact original certified common readings. -/
theorem comparison_original {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftFrontier : SourceFrontier leftSource) (rightFrontier : SourceFrontier rightSource)
    (cached : Option (Comparison.Observation.Certified leftFrontier rightFrontier)) :
    ((comparison leftFrontier rightFrontier cached).protocol.run
      (Comparison.Observation.originalReply leftSource rightSource)).value =
        .ok ⟨commonReadings leftFrontier rightFrontier, rfl⟩ := by
  cases cached with
  | none => exact Comparison.Observation.certified_original leftFrontier rightFrontier
  | some saved =>
      change Except.ok saved = Except.ok ⟨commonReadings leftFrontier rightFrontier, rfl⟩
      apply congrArg Except.ok
      apply Subtype.ext
      exact saved.property

/-- Answer each original coordinate and source owner with its exact finite point. -/
@[expose] def original : Query → Reply left right
  | .inl question =>
      .inl (Comparison.Observation.originalReply (projected left).eval (projected right).eval question)
  | .inr question =>
      .inr (Comparison.Observation.originalReply (projectedIm left).eval (projectedIm right).eval question)

/-- Decode a real-coordinate reply, distinguishing a missing outer reply from the wrong coordinate. -/
@[expose] def realHandlerWith {OuterReply : Type} (decode : OuterReply → Option (Reply left right))
    (question : Comparison.Observation.Query) :
    Program Query OuterReply (Except (Failure left right leftReal rightReal)
      (Comparison.Observation.Reply (projected left).eval (projected right).eval)) :=
  .request (.inl question) fun returned => match decode returned with
    | none => .pure (.error (.realOuter question))
    | some (.inl point) => .pure (.ok point)
    | some (.inr _) => .pure (.error (.realOwner question))

/-- Decode an imaginary reply while retaining the completed real comparison. -/
@[expose] def imaginaryHandlerWith {OuterReply : Type} (decode : OuterReply → Option (Reply left right))
    (real : RealCommon left right leftReal rightReal) (question : Comparison.Observation.Query) :
    Program Query OuterReply (Except (Failure left right leftReal rightReal)
      (Comparison.Observation.Reply (projectedIm left).eval (projectedIm right).eval)) :=
  .request (.inr question) fun returned => match decode returned with
    | none => .pure (.error (.imaginaryOuter real question))
    | some (.inl _) => .pure (.error (.imaginaryOwner real question))
    | some (.inr point) => .pure (.ok point)

/-- Display a real query and reject a reply for the other coordinate. -/
@[expose] def realHandler (question : Comparison.Observation.Query) :=
  realHandlerWith left right leftReal rightReal some question

/-- Display an imaginary query while retaining the completed real comparison. -/
@[expose] def imaginaryHandler (real : RealCommon left right leftReal rightReal)
    (question : Comparison.Observation.Query) :=
  imaginaryHandlerWith left right leftReal rightReal some real question

/-- Compare the original coordinate frontiers using a supplied finite reply decoder.

The decoder only identifies whether an enclosing operation supplied a reply;
the actual common-source decisions and failure branches remain shared. -/
@[expose] def computationWith {OuterReply : Type} (decode : OuterReply → Option (Reply left right))
    (realCache : Option (RealCommon left right leftReal rightReal))
    (imaginaryCache : Option (ImaginaryCommon left right leftImaginary rightImaginary)) :
    Program Query OuterReply (Except (Failure left right leftReal rightReal)
      (Result left right leftReal rightReal leftImaginary rightImaginary)) :=
  ((comparison leftReal.1 rightReal.1 realCache).substituteChecked
    (realHandlerWith left right leftReal rightReal decode)).bind fun first => match first with
    | .error invalid => .pure (.error invalid)
    | .ok execution => match execution.value with
      | .error invalid => .pure (.error (.real invalid))
      | .ok real =>
          ((comparison leftImaginary.1 rightImaginary.1 imaginaryCache).substituteChecked
            (imaginaryHandlerWith left right leftReal rightReal decode real)).map fun result => match result with
              | .error invalid => .error invalid
              | .ok execution => match execution.value with
                | .error invalid => .error (.imaginary real invalid)
                | .ok imaginary => .ok ⟨real, imaginary⟩

/-- Compare the actual independently owned coordinate frontiers through their common-point requests. -/
@[expose] def computation (realCache : Option (RealCommon left right leftReal rightReal))
    (imaginaryCache : Option (ImaginaryCommon left right leftImaginary rightImaginary)) :
    Program Query (Reply left right) (Except (Failure left right leftReal rightReal)
      (Result left right leftReal rightReal leftImaginary rightImaginary)) :=
  computationWith left right leftReal rightReal leftImaginary rightImaginary some realCache imaginaryCache

/-- Observe the same branches when an enclosing operation can return no coordinate reply. -/
@[expose] def computationOptional (realCache : Option (RealCommon left right leftReal rightReal))
    (imaginaryCache : Option (ImaginaryCommon left right leftImaginary rightImaginary)) :
    Program Query (Option (Reply left right)) (Except (Failure left right leftReal rightReal)
      (Result left right leftReal rightReal leftImaginary rightImaginary)) :=
  computationWith left right leftReal rightReal leftImaginary rightImaginary id realCache imaginaryCache

/-- The canonical two-coordinate comparison of the actual original segment frontiers. -/
@[expose] def originalResult : Result left right leftReal rightReal leftImaginary rightImaginary :=
  ⟨⟨commonReadings leftReal.1 rightReal.1, rfl⟩, ⟨commonReadings leftImaginary.1 rightImaginary.1, rfl⟩⟩

/-- Original replies recover both complete original common readings. -/
theorem computation_original (realCache : Option (RealCommon left right leftReal rightReal))
    (imaginaryCache : Option (ImaginaryCommon left right leftImaginary rightImaginary)) :
    ((computation left right leftReal rightReal leftImaginary rightImaginary realCache imaginaryCache).protocol.run
      (original left right)).value =
        .ok (originalResult left right leftReal rightReal leftImaginary rightImaginary) := by
  unfold computation computationWith
  rw [Program.bind_execution, Protocol.bind_run_value]
  have first := Program.substituteChecked_value (realHandlerWith left right leftReal rightReal some)
    (comparison leftReal.1 rightReal.1 realCache) (original left right)
    (Comparison.Observation.originalReply (projected left).eval (projected right).eval) (by intro question; rfl)
  rw [first]
  dsimp only
  rw [comparison_original]
  dsimp only
  rw [Program.map_execution, Protocol.map_run_value]
  have second := Program.substituteChecked_value
    (imaginaryHandlerWith left right leftReal rightReal some ⟨commonReadings leftReal.1 rightReal.1, rfl⟩)
    (comparison leftImaginary.1 rightImaginary.1 imaginaryCache) (original left right)
    (Comparison.Observation.originalReply (projectedIm left).eval (projectedIm right).eval) (by intro question; rfl)
  rw [second]
  dsimp only
  rw [comparison_original]
  rfl

/-- Original optional replies recover the same complete common readings. -/
theorem computationOptional_original (realCache : Option (RealCommon left right leftReal rightReal))
    (imaginaryCache : Option (ImaginaryCommon left right leftImaginary rightImaginary)) :
    let program := computationOptional left right leftReal rightReal leftImaginary rightImaginary
      realCache imaginaryCache
    (program.protocol.run (fun question => some (original left right question))).value =
      .ok (originalResult left right leftReal rightReal leftImaginary rightImaginary) := by
  unfold computationOptional computationWith
  dsimp only
  rw [Program.bind_execution, Protocol.bind_run_value]
  have first := Program.substituteChecked_value (realHandlerWith left right leftReal rightReal id)
    (comparison leftReal.1 rightReal.1 realCache) (fun question => some (original left right question))
    (Comparison.Observation.originalReply (projected left).eval (projected right).eval) (by intro question; rfl)
  rw [first]
  dsimp only
  rw [comparison_original]
  dsimp only
  rw [Program.map_execution, Protocol.map_run_value]
  have second := Program.substituteChecked_value
    (imaginaryHandlerWith left right leftReal rightReal id ⟨commonReadings leftReal.1 rightReal.1, rfl⟩)
    (comparison leftImaginary.1 rightImaginary.1 imaginaryCache) (fun question => some (original left right question))
    (Comparison.Observation.originalReply (projectedIm left).eval (projectedIm right).eval) (by intro question; rfl)
  rw [second]
  dsimp only
  rw [comparison_original]
  rfl

/-- Reusing both certified common comparisons makes no source request. -/
theorem computation_reused (real : RealCommon left right leftReal rightReal)
    (imaginary : ImaginaryCommon left right leftImaginary rightImaginary) (oracle : Query → Reply left right) :
    ((computation left right leftReal rightReal leftImaginary rightImaginary (some real) (some imaginary)).protocol.run
      oracle).trace = [] := rfl

/-- The actual real common readings pay for the two original segment samples. -/
theorem Result.real_difference_le (result : Result left right leftReal rightReal leftImaginary rightImaginary)
    (first : Segment.CompiledSegment left) (second : Segment.CompiledSegment right) :
    Fraction.abs (first.sample.re - second.sample.re) ≤
      (integralBound leftReal.1.cells).width + (integralBound rightReal.1.cells).width + result.real.val.pointBudget :=
  result.real.val.answers_difference_le first.sample.re second.sample.re
    (Partition.Continuous.compiled_state_contains first leftReal)
    (Partition.Continuous.compiled_state_contains second rightReal)

/-- The actual imaginary common readings pay for the two original segment samples. -/
theorem Result.imaginary_difference_le (result : Result left right leftReal rightReal leftImaginary rightImaginary)
    (first : Segment.CompiledSegment left) (second : Segment.CompiledSegment right) :
    Fraction.abs (first.sample.im - second.sample.im) ≤
      (integralBound leftImaginary.1.cells).width + (integralBound rightImaginary.1.cells).width +
        result.imaginary.val.pointBudget :=
  result.imaginary.val.answers_difference_le first.sample.im second.sample.im
    (Partition.Continuous.compiled_im_state_contains first leftImaginary)
    (Partition.Continuous.compiled_im_state_contains second rightImaginary)

/-- Coordinate widths and point budgets bound the original segment samples' squared difference. -/
theorem Result.samples_normSq_le (result : Result left right leftReal rightReal leftImaginary rightImaginary)
    (first : Segment.CompiledSegment left) (second : Segment.CompiledSegment right) :
    Norm.Basic.normSq (first.sample - second.sample) ≤
      ((integralBound leftReal.1.cells).width + (integralBound rightReal.1.cells).width +
        result.real.val.pointBudget) ^ 2 +
      ((integralBound leftImaginary.1.cells).width + (integralBound rightImaginary.1.cells).width +
        result.imaginary.val.pointBudget) ^ 2 := by
  exact Norm.Coordinates.sub_normSq_le first.sample second.sample _ _
    (Result.real_difference_le left right leftReal rightReal leftImaginary rightImaginary result first second)
    (Result.imaginary_difference_le left right leftReal rightReal leftImaginary rightImaginary result first second)

/-- Replay preserves both returned common readings and any typed failure. -/
theorem replay (realCache : Option (RealCommon left right leftReal rightReal))
    (imaginaryCache : Option (ImaginaryCommon left right leftImaginary rightImaginary))
    (oracle : Query → Reply left right) :
    let program := computation left right leftReal rightReal leftImaginary rightImaginary realCache imaginaryCache
    program.protocol.replayExact (program.protocol.run oracle).trace = .ok (program.protocol.run oracle).value := by
  let program := computation left right leftReal rightReal leftImaginary rightImaginary realCache imaginaryCache
  exact program.protocol.replayExact_run oracle

/-- Replies outside the actual coordinate requests preserve the complete result and ordered trace. -/
theorem payload_erasure (realCache : Option (RealCommon left right leftReal rightReal))
    (imaginaryCache : Option (ImaginaryCommon left right leftImaginary rightImaginary)) {Payload : Type}
    (payload : Payload) (outside : Payload → Query → Reply left right) :
    let program := computation left right leftReal rightReal leftImaginary rightImaginary realCache imaginaryCache
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run (original left right)).trace (outside payload)) =
      program.protocol.run (original left right) := by
  let program := computation left right leftReal rightReal leftImaginary rightImaginary realCache imaginaryCache
  exact program.protocol.annotation_erasure (original left right) payload outside

end Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation.Independent

end
