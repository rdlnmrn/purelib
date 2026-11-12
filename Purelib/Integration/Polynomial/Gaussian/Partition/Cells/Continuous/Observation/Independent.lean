module

public import Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation
public import Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation.Independent
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Coordinates
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Independent ordered polynomial path comparisons

An explicit positional alignment retains the two original source paths.
Each corresponding segment compares its actual returned real and imaginary
frontiers and retains both original common-point budgets.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation.Independent

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Partition.Continuous.Observation.Independent renaming
  Query → SegmentIndependent.Query, Reply → SegmentIndependent.Reply,
  RealCommon → SegmentIndependent.RealCommon, ImaginaryCommon → SegmentIndependent.ImaginaryCommon,
  Result → SegmentIndependent.Result, Failure → SegmentIndependent.Failure,
  original → SegmentIndependent.original, originalResult → SegmentIndependent.originalResult,
  computation → SegmentIndependent.computation, computationOptional → SegmentIndependent.computationOptional,
  computation_original → SegmentIndependent.computation_original,
  computationOptional_original → SegmentIndependent.computationOptional_original
open Purelib.Integration.Polynomial.Gaussian.Segment.Basic

set_option genInjectivity false in
/-- A positional correspondence between two original ordered source paths. -/
inductive Alignment : Source.PolynomialPath → Source.PolynomialPath → Type where
  /-- The two empty paths correspond. -/ | nil : Alignment [] []
  /-- The two original head occurrences correspond, followed by the supplied tail correspondence. -/ | cons
      {left right : PolynomialSegment} {leftTail rightTail : Source.PolynomialPath}
      (tail : Alignment leftTail rightTail) : Alignment (left :: leftTail) (right :: rightTail)

constructive_injectivity Alignment

/-- A common-point question retains its original aligned segment occurrence. -/
@[expose] def Query : {left right : Source.PolynomialPath} → Alignment left right → Type
  | _, _, .nil => Empty
  | _, _, .cons tail => Sum SegmentIndependent.Query (Query tail)

/-- Replies retain both original source owners at each aligned occurrence. -/
@[expose] def Reply : {left right : Source.PolynomialPath} → Alignment left right → Type
  | _, _, .nil => Empty
  | _, _, @Alignment.cons left right _ _ tail =>
      Sum (SegmentIndependent.Reply left right) (Reply tail)

/-- Path-question equality uses the finite retained segment correspondence. -/
@[expose] def queryDecidableEq : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right),
    DecidableEq (Query alignment)
  | _, _, .nil => fun question => nomatch question
  | _, _, .cons tail => by
      change DecidableEq (Sum SegmentIndependent.Query (Query tail))
      letI := queryDecidableEq tail
      infer_instance

/-- Original aligned path questions have executable equality. -/
instance {left right : Source.PolynomialPath} (alignment : Alignment left right) : DecidableEq (Query alignment) :=
  queryDecidableEq alignment

/-- Optional original common-reading certificates for every aligned source occurrence. -/
@[expose] def Cache : ∀ {left right : Source.PolynomialPath} (_alignment : Alignment left right),
    RealState left → RealState right → ImaginaryState left → ImaginaryState right → Type
  | _, _, .nil, _, _, _, _ => Unit
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary =>
      Option (SegmentIndependent.RealCommon left right leftReal.1 rightReal.1) ×
      Option (SegmentIndependent.ImaginaryCommon left right
        leftImaginary.1 rightImaginary.1) ×
        Cache tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2

/-- An empty common-reading cache at every aligned original segment occurrence. -/
@[expose] def emptyCache : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right),
    Cache alignment leftReal rightReal leftImaginary rightImaginary
  | _, _, .nil, _, _, _, _ => ()
  | _, _, .cons tail, leftReal, rightReal, leftImaginary, rightImaginary =>
      (none, none, emptyCache tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2)

/-- Actual ordered segment comparisons, each retaining its two original frontier owners. -/
@[expose] def Result : ∀ {left right : Source.PolynomialPath} (_alignment : Alignment left right),
    RealState left → RealState right → ImaginaryState left → ImaginaryState right → Type
  | _, _, .nil, _, _, _, _ => Unit
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary =>
      SegmentIndependent.Result left right leftReal.1 rightReal.1
        leftImaginary.1 rightImaginary.1 × Result tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2

/-- A wrong occurrence or segment failure retains all earlier completed segment comparisons. -/
@[expose] def Failure : ∀ {left right : Source.PolynomialPath} (_alignment : Alignment left right),
    RealState left → RealState right → ImaginaryState left → ImaginaryState right → Type
  | _, _, .nil, _, _, _, _ => Empty
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary =>
      Sum (Sum SegmentIndependent.Query
          (SegmentIndependent.Failure left right leftReal.1 rightReal.1))
        (SegmentIndependent.Result left right leftReal.1 rightReal.1
          leftImaginary.1 rightImaginary.1 × Sum (Query tail)
            (Failure tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2))

/-- Original replies preserve both source owners and the retained segment occurrence. -/
@[expose] def original : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right),
    Query alignment → Reply alignment
  | _, _, .nil => fun question => nomatch question
  | _, _, @Alignment.cons left right _ _ tail => by
      change Sum SegmentIndependent.Query (Query tail) →
        Sum (SegmentIndependent.Reply left right) (Reply tail)
      intro question
      cases question with
      | inl question => exact .inl (SegmentIndependent.original left right question)
      | inr question => exact .inr (original tail question)

/-- Forward one aligned head request while retaining both original source owners. -/
@[expose] def headHandler {left right : PolynomialSegment} {leftTail rightTail : Source.PolynomialPath}
    (tail : Alignment leftTail rightTail) (leftReal : RealState (left :: leftTail))
    (rightReal : RealState (right :: rightTail)) (leftImaginary : ImaginaryState (left :: leftTail))
    (rightImaginary : ImaginaryState (right :: rightTail))
    (question : SegmentIndependent.Query) :
    Program (Query (@Alignment.cons left right leftTail rightTail tail))
      (Reply (@Alignment.cons left right leftTail rightTail tail))
      (Except (Failure (@Alignment.cons left right leftTail rightTail tail)
        leftReal rightReal leftImaginary rightImaginary)
        (SegmentIndependent.Reply left right)) := by
  change Program (Sum SegmentIndependent.Query (Query tail))
    (Sum (SegmentIndependent.Reply left right) (Reply tail)) _
  exact .request (.inl question) fun reply => match reply with
    | .inl value => .pure (.ok value)
    | .inr _ => .pure (.error (.inl (.inl question)))

/-- Forward one aligned tail request while retaining the completed head comparison. -/
@[expose] def tailHandler {left right : PolynomialSegment} {leftTail rightTail : Source.PolynomialPath}
    (tail : Alignment leftTail rightTail) (leftReal : RealState (left :: leftTail))
    (rightReal : RealState (right :: rightTail)) (leftImaginary : ImaginaryState (left :: leftTail))
    (rightImaginary : ImaginaryState (right :: rightTail))
    (head : SegmentIndependent.Result left right leftReal.1 rightReal.1
      leftImaginary.1 rightImaginary.1) (question : Query tail) :
    Program (Query (@Alignment.cons left right leftTail rightTail tail))
      (Reply (@Alignment.cons left right leftTail rightTail tail))
      (Except (Failure (@Alignment.cons left right leftTail rightTail tail)
        leftReal rightReal leftImaginary rightImaginary) (Reply tail)) := by
  change Program (Sum SegmentIndependent.Query (Query tail))
    (Sum (SegmentIndependent.Reply left right) (Reply tail)) _
  exact .request (.inr question) fun reply => match reply with
    | .inl _ => .pure (.error (.inr (head, .inl question)))
    | .inr value => .pure (.ok value)

/-- Forward an aligned head request and pass a missing outer reply to the segment computation. -/
@[expose] def optionalHeadHandler {left right : PolynomialSegment} {leftTail rightTail : Source.PolynomialPath}
    (tail : Alignment leftTail rightTail) (leftReal : RealState (left :: leftTail))
    (rightReal : RealState (right :: rightTail)) (leftImaginary : ImaginaryState (left :: leftTail))
    (rightImaginary : ImaginaryState (right :: rightTail))
    (question : SegmentIndependent.Query) :
    Program (Query (@Alignment.cons left right leftTail rightTail tail))
      (Option (Reply (@Alignment.cons left right leftTail rightTail tail)))
      (Except (Failure (@Alignment.cons left right leftTail rightTail tail)
        leftReal rightReal leftImaginary rightImaginary)
        (Option (SegmentIndependent.Reply left right))) := by
  change Program (Sum SegmentIndependent.Query (Query tail))
    (Option (Sum (SegmentIndependent.Reply left right) (Reply tail))) _
  exact .request (.inl question) fun returned => match returned with
    | none => .pure (.ok none)
    | some (.inl value) => .pure (.ok (some value))
    | some (.inr _) => .pure (.error (.inl (.inl question)))

/-- Forward an aligned tail request while retaining the completed head and missing outer replies. -/
@[expose] def optionalTailHandler {left right : PolynomialSegment} {leftTail rightTail : Source.PolynomialPath}
    (tail : Alignment leftTail rightTail) (leftReal : RealState (left :: leftTail))
    (rightReal : RealState (right :: rightTail)) (leftImaginary : ImaginaryState (left :: leftTail))
    (rightImaginary : ImaginaryState (right :: rightTail))
    (head : SegmentIndependent.Result left right leftReal.1 rightReal.1
      leftImaginary.1 rightImaginary.1) (question : Query tail) :
    Program (Query (@Alignment.cons left right leftTail rightTail tail))
      (Option (Reply (@Alignment.cons left right leftTail rightTail tail)))
      (Except (Failure (@Alignment.cons left right leftTail rightTail tail)
        leftReal rightReal leftImaginary rightImaginary) (Option (Reply tail))) := by
  change Program (Sum SegmentIndependent.Query (Query tail))
    (Option (Sum (SegmentIndependent.Reply left right) (Reply tail))) _
  exact .request (.inr question) fun returned => match returned with
    | none => .pure (.ok none)
    | some (.inl _) => .pure (.error (.inr (head, .inl question)))
    | some (.inr value) => .pure (.ok (some value))


/-- The actual checked head execution before continuing the remaining aligned path. -/
abbrev HeadExecution {left right : PolynomialSegment} {leftTail rightTail : Source.PolynomialPath}
    (leftReal : RealState (left :: leftTail)) (rightReal : RealState (right :: rightTail))
    (leftImaginary : ImaginaryState (left :: leftTail)) (rightImaginary : ImaginaryState (right :: rightTail))
    (HeadReply : Type) :=
  Basic.Execution SegmentIndependent.Query HeadReply
    (Except (SegmentIndependent.Failure left right leftReal.1 rightReal.1)
      (SegmentIndependent.Result left right leftReal.1 rightReal.1
        leftImaginary.1 rightImaginary.1))

/-- Continue the actual retained head execution with the supplied tail program. -/
@[expose] def afterHeadWith {left right : PolynomialSegment} {leftTail rightTail : Source.PolynomialPath}
    {HeadReply TailReply OuterReply : Type}
    (tail : Alignment leftTail rightTail) (leftReal : RealState (left :: leftTail))
    (rightReal : RealState (right :: rightTail)) (leftImaginary : ImaginaryState (left :: leftTail))
    (rightImaginary : ImaginaryState (right :: rightTail))
    (tailProgram : Program (Query tail) TailReply
      (Except (Failure tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2)
        (Result tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2)))
    (forwardTail : SegmentIndependent.Result left right leftReal.1 rightReal.1
      leftImaginary.1 rightImaginary.1 → Query tail →
        Program (Query (@Alignment.cons left right leftTail rightTail tail)) OuterReply
          (Except (Failure (@Alignment.cons left right leftTail rightTail tail)
            leftReal rightReal leftImaginary rightImaginary) TailReply))
    (returned : Except (Failure (@Alignment.cons left right leftTail rightTail tail)
      leftReal rightReal leftImaginary rightImaginary)
        (HeadExecution leftReal rightReal leftImaginary rightImaginary HeadReply)) :
    Program (Query (@Alignment.cons left right leftTail rightTail tail)) OuterReply
      (Except (Failure (@Alignment.cons left right leftTail rightTail tail)
        leftReal rightReal leftImaginary rightImaginary)
        (Result (@Alignment.cons left right leftTail rightTail tail)
          leftReal rightReal leftImaginary rightImaginary)) :=
  match returned with
  | .error invalid => .pure (.error invalid)
  | .ok execution => match execution.value with
    | .error invalid => .pure (.error (.inl (.inr invalid)))
    | .ok head => (tailProgram.substituteChecked (forwardTail head)).map fun returned =>
          match returned with
          | .error invalid => .error invalid
          | .ok execution => match execution.value with
            | .error invalid => .error (.inr (head, .inr invalid))
            | .ok result => .ok (head, result)


/-- Compare each aligned segment in original order using its actual source states and cached readings. -/
@[expose] def computation : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right),
    Cache alignment leftReal rightReal leftImaginary rightImaginary →
      Program (Query alignment) (Reply alignment)
        (Except (Failure alignment leftReal rightReal leftImaginary rightImaginary)
          (Result alignment leftReal rightReal leftImaginary rightImaginary))
  | _, _, .nil, _, _, _, _, _ => .pure (.ok ())
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary, cached =>
      ((SegmentIndependent.computation left right leftReal.1 rightReal.1
          leftImaginary.1 rightImaginary.1 cached.1 cached.2.1).substituteChecked
            (headHandler tail leftReal rightReal leftImaginary rightImaginary)).bind
              (afterHeadWith tail leftReal rightReal leftImaginary rightImaginary
                (computation tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 cached.2.2)
                (tailHandler tail leftReal rightReal leftImaginary rightImaginary))

/-- Compare aligned segments while retaining a missing enclosing-operation reply as a local failure.

The same source and completed-head branches are used by `computation`; missing
outer replies reach the actual segment operation and preserve prior comparisons. -/
@[expose] def computationOptional : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right),
    Cache alignment leftReal rightReal leftImaginary rightImaginary →
      Program (Query alignment) (Option (Reply alignment))
        (Except (Failure alignment leftReal rightReal leftImaginary rightImaginary)
          (Result alignment leftReal rightReal leftImaginary rightImaginary))
  | _, _, .nil, _, _, _, _, _ => .pure (.ok ())
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary, cached =>
      ((SegmentIndependent.computationOptional left right leftReal.1 rightReal.1
          leftImaginary.1 rightImaginary.1 cached.1 cached.2.1).substituteChecked
            (optionalHeadHandler tail leftReal rightReal leftImaginary rightImaginary)).bind
              (afterHeadWith tail leftReal rightReal leftImaginary rightImaginary
                (computationOptional tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 cached.2.2)
                (optionalTailHandler tail leftReal rightReal leftImaginary rightImaginary))


/-- Canonical common readings for every original aligned segment occurrence. -/
@[expose] def originalResult : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right),
    Result alignment leftReal rightReal leftImaginary rightImaginary
  | _, _, .nil, _, _, _, _ => ()
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary =>
      ⟨SegmentIndependent.originalResult left right leftReal.1 rightReal.1
        leftImaginary.1 rightImaginary.1,
        originalResult tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2⟩

/-- Retain every actual returned segment comparison for another request on these exact frontiers. -/
@[expose] def cacheOf : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right),
    Result alignment leftReal rightReal leftImaginary rightImaginary →
      Cache alignment leftReal rightReal leftImaginary rightImaginary
  | _, _, .nil, _, _, _, _, _ => ()
  | _, _, .cons tail, leftReal, rightReal, leftImaginary, rightImaginary, result =>
      (some result.1.real, some result.1.imaginary,
        cacheOf tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 result.2)

/-- A repeated optional comparison with every actual retained common value makes no source request. -/
theorem computationOptional_reused : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right)
    (result : Result alignment leftReal rightReal leftImaginary rightImaginary),
    computationOptional alignment leftReal rightReal leftImaginary rightImaginary
        (cacheOf alignment leftReal rightReal leftImaginary rightImaginary result) = .pure (.ok result)
  | _, _, .nil, _, _, _, _, result => by cases result; rfl
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary, result => by
      cases result with
      | mk head rest =>
        cases head with
        | mk real imaginary =>
          change (((SegmentIndependent.computationOptional left right leftReal.1 rightReal.1
              leftImaginary.1 rightImaginary.1 (some real) (some imaginary)).substituteChecked
                (optionalHeadHandler tail leftReal rightReal leftImaginary rightImaginary)).bind
                  (afterHeadWith tail leftReal rightReal leftImaginary rightImaginary
                    (computationOptional tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2
                      (cacheOf tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 rest))
                    (optionalTailHandler tail leftReal rightReal leftImaginary rightImaginary))) = _
          rw [computationOptional_reused tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 rest]
          rfl

/-- Original source replies return the complete ordered comparisons of both original paths. -/
theorem computation_original : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right)
    (cached : Cache alignment leftReal rightReal leftImaginary rightImaginary),
    ((computation alignment leftReal rightReal leftImaginary rightImaginary cached).protocol.run
      (original alignment)).value = .ok (originalResult alignment leftReal rightReal leftImaginary rightImaginary)
  | _, _, .nil, _, _, _, _, _ => rfl
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary, cached => by
      change ((((SegmentIndependent.computation left right leftReal.1 rightReal.1
          leftImaginary.1 rightImaginary.1 cached.1 cached.2.1).substituteChecked
            (headHandler tail leftReal rightReal leftImaginary rightImaginary)).bind
              (afterHeadWith tail leftReal rightReal leftImaginary rightImaginary
                (computation tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 cached.2.2)
                (tailHandler tail leftReal rightReal leftImaginary rightImaginary))).protocol.run
                  (original (@Alignment.cons left right _ _ tail))).value = _
      rw [Program.bind_execution, Protocol.bind_run_value]
      have head := Program.substituteChecked_value (headHandler tail leftReal rightReal leftImaginary rightImaginary)
        (SegmentIndependent.computation left right leftReal.1 rightReal.1
          leftImaginary.1 rightImaginary.1 cached.1 cached.2.1)
        (original (@Alignment.cons left right _ _ tail))
        (SegmentIndependent.original left right) (by intro; rfl)
      rw [head]
      dsimp only [afterHeadWith]
      rw [SegmentIndependent.computation_original]
      dsimp only
      rw [Program.map_execution, Protocol.map_run_value]
      have rest := Program.substituteChecked_value
        (tailHandler tail leftReal rightReal leftImaginary rightImaginary
          (SegmentIndependent.originalResult left right leftReal.1 rightReal.1
            leftImaginary.1 rightImaginary.1))
        (computation tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 cached.2.2)
        (original (@Alignment.cons left right _ _ tail)) (original tail) (by intro; rfl)
      rw [rest]
      dsimp only
      rw [computation_original tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 cached.2.2]
      rfl

/-- Original optional source replies return both complete ordered path comparisons. -/
theorem computationOptional_original : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right)
    (cached : Cache alignment leftReal rightReal leftImaginary rightImaginary),
    ((computationOptional alignment leftReal rightReal leftImaginary rightImaginary cached).protocol.run
      (fun question => some (original alignment question))).value =
        .ok (originalResult alignment leftReal rightReal leftImaginary rightImaginary)
  | _, _, .nil, _, _, _, _, _ => rfl
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary, cached => by
      change ((((SegmentIndependent.computationOptional left right leftReal.1 rightReal.1
          leftImaginary.1 rightImaginary.1 cached.1 cached.2.1).substituteChecked
            (optionalHeadHandler tail leftReal rightReal leftImaginary rightImaginary)).bind
              (afterHeadWith tail leftReal rightReal leftImaginary rightImaginary
                (computationOptional tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 cached.2.2)
                (optionalTailHandler tail leftReal rightReal leftImaginary rightImaginary))).protocol.run
                  (fun question => some (original (@Alignment.cons left right _ _ tail) question))).value = _
      rw [Program.bind_execution, Protocol.bind_run_value]
      have head := Program.substituteChecked_value
        (optionalHeadHandler tail leftReal rightReal leftImaginary rightImaginary)
        (SegmentIndependent.computationOptional left right leftReal.1 rightReal.1
          leftImaginary.1 rightImaginary.1 cached.1 cached.2.1)
        (fun question => some (original (@Alignment.cons left right _ _ tail) question))
        (fun question => some (SegmentIndependent.original left right question))
        (by intro; rfl)
      rw [head]
      dsimp only [afterHeadWith]
      rw [SegmentIndependent.computationOptional_original]
      dsimp only
      rw [Program.map_execution, Protocol.map_run_value]
      have rest := Program.substituteChecked_value
        (optionalTailHandler tail leftReal rightReal leftImaginary rightImaginary
          (SegmentIndependent.originalResult left right leftReal.1 rightReal.1
            leftImaginary.1 rightImaginary.1))
        (computationOptional tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 cached.2.2)
        (fun question => some (original (@Alignment.cons left right _ _ tail) question))
        (fun question => some (original tail question)) (by intro; rfl)
      rw [rest]
      dsimp only
      rw [computationOptional_original tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 cached.2.2]
      rfl


/-- Original replies outside the actual common-point trace preserve the complete execution. -/
theorem payload_erasure {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right)
    (cached : Cache alignment leftReal rightReal leftImaginary rightImaginary) {Payload : Type}
    (oracle : Query alignment → Reply alignment)
    (payload : Payload) (outside : Payload → Query alignment → Reply alignment) :
    let program := computation alignment leftReal rightReal leftImaginary rightImaginary cached
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle := by
  let program := computation alignment leftReal rightReal leftImaginary rightImaginary cached
  exact program.protocol.annotation_erasure oracle payload outside

/-- Exact replay preserves all actual aligned occurrences, common readings and typed failures. -/
theorem replay {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right)
    (cached : Cache alignment leftReal rightReal leftImaginary rightImaginary)
    (oracle : Query alignment → Reply alignment) :
    let program := computation alignment leftReal rightReal leftImaginary rightImaginary cached
    program.protocol.replayExact (program.protocol.run oracle).trace = .ok (program.protocol.run oracle).value := by
  let program := computation alignment leftReal rightReal leftImaginary rightImaginary cached
  exact program.protocol.replayExact_run oracle

/-- Sum the actual real-coordinate widths and common-point budgets in aligned path order. -/
@[expose] def realBudget : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right),
    Result alignment leftReal rightReal leftImaginary rightImaginary → Purelib.Data.Rat.Fraction.Rational
  | _, _, .nil, _, _, _, _, _ => 0
  | _, _, .cons tail, leftReal, rightReal, leftImaginary, rightImaginary, result =>
      (integralBound leftReal.1.1.cells).width + (integralBound rightReal.1.1.cells).width +
        result.1.real.val.pointBudget + realBudget tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 result.2

/-- Sum the actual imaginary-coordinate widths and common-point budgets in aligned path order. -/
@[expose] def imaginaryBudget : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right),
    Result alignment leftReal rightReal leftImaginary rightImaginary → Purelib.Data.Rat.Fraction.Rational
  | _, _, .nil, _, _, _, _, _ => 0
  | _, _, .cons tail, leftReal, rightReal, leftImaginary, rightImaginary, result =>
      (integralBound leftImaginary.1.1.cells).width + (integralBound rightImaginary.1.1.cells).width +
        result.1.imaginary.val.pointBudget +
          imaginaryBudget tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2 result.2

/-- Actual aligned real common-point budgets pay for the difference of the two original path samples. -/
theorem real_difference_le : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right)
    (result : Result alignment leftReal rightReal leftImaginary rightImaginary)
    (first : CompiledCells left) (second : CompiledCells right),
    Fraction.abs (first.sample.re - second.sample.re) ≤
      realBudget alignment leftReal rightReal leftImaginary rightImaginary result
  | _, _, .nil, _, _, _, _, _, .nil, .nil => by
      change Fraction.abs ((0 : Fraction.Rational) - 0) ≤ 0
      decide
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary, result,
      .cons first firstTail, .cons second secondTail => by
      have head := SegmentIndependent.Result.real_difference_le left right
        leftReal.1 rightReal.1 leftImaginary.1 rightImaginary.1 result.1 first second
      have rest := real_difference_le tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2
        result.2 firstTail secondTail
      change Fraction.abs ((first.sample + firstTail.sample).re - (second.sample + secondTail.sample).re) ≤ _
      rw [Basic.add_re, Basic.add_re]
      have split : first.sample.re + firstTail.sample.re - (second.sample.re + secondTail.sample.re) =
          (first.sample.re - second.sample.re) + (firstTail.sample.re - secondTail.sample.re) := by ring1
      rw [split]
      exact (Bounds.Abs.abs_add_le_direct _ _).trans (Fraction.Order.Arithmetic.add_le_add_direct head rest)

/-- Actual aligned imaginary common-point budgets pay for the difference of the two original path samples. -/
theorem imaginary_difference_le : ∀ {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right)
    (result : Result alignment leftReal rightReal leftImaginary rightImaginary)
    (first : CompiledCells left) (second : CompiledCells right),
    Fraction.abs (first.sample.im - second.sample.im) ≤
      imaginaryBudget alignment leftReal rightReal leftImaginary rightImaginary result
  | _, _, .nil, _, _, _, _, _, .nil, .nil => by
      change Fraction.abs ((0 : Fraction.Rational) - 0) ≤ 0
      decide
  | _, _, @Alignment.cons left right _ _ tail, leftReal, rightReal, leftImaginary, rightImaginary, result,
      .cons first firstTail, .cons second secondTail => by
      have head := SegmentIndependent.Result.imaginary_difference_le left right
        leftReal.1 rightReal.1 leftImaginary.1 rightImaginary.1 result.1 first second
      have rest := imaginary_difference_le tail leftReal.2 rightReal.2 leftImaginary.2 rightImaginary.2
        result.2 firstTail secondTail
      change Fraction.abs ((first.sample + firstTail.sample).im - (second.sample + secondTail.sample).im) ≤ _
      rw [Basic.add_im, Basic.add_im]
      have split : first.sample.im + firstTail.sample.im - (second.sample.im + secondTail.sample.im) =
          (first.sample.im - second.sample.im) + (firstTail.sample.im - secondTail.sample.im) := by ring1
      rw [split]
      exact (Bounds.Abs.abs_add_le_direct _ _).trans (Fraction.Order.Arithmetic.add_le_add_direct head rest)

/-- Both actual aligned coordinate budgets pay for the two original Gaussian path samples. -/
theorem samples_normSq_le {left right : Source.PolynomialPath} (alignment : Alignment left right)
    (leftReal : RealState left) (rightReal : RealState right)
    (leftImaginary : ImaginaryState left) (rightImaginary : ImaginaryState right)
    (result : Result alignment leftReal rightReal leftImaginary rightImaginary)
    (first : CompiledCells left) (second : CompiledCells right) :
    Norm.Basic.normSq (first.sample - second.sample) ≤
      (realBudget alignment leftReal rightReal leftImaginary rightImaginary result) ^ 2 +
      (imaginaryBudget alignment leftReal rightReal leftImaginary rightImaginary result) ^ 2 :=
  Norm.Coordinates.sub_normSq_le first.sample second.sample _ _
    (real_difference_le alignment leftReal rightReal leftImaginary rightImaginary result first second)
    (imaginary_difference_le alignment leftReal rightReal leftImaginary rightImaginary result first second)

end Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation.Independent

end
