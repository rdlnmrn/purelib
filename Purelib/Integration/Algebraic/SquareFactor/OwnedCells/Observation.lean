module

public import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
public import Purelib.Polynomial.Dense.Gaussian.Evaluation.Observation
public import Purelib.Computation.Query.Program
import Purelib.Computation.Query.Boundary
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Data.Gaussian.Field

/-!
# Original cell models from displayed root and polynomial requests

The retained edge already owns its prepared source, path and sheet.
Model construction requests its exact starting root witness and both
coefficient values. Assembly consumes these replies through the original
named constructors; it invokes no root process or polynomial evaluator.
The root certificate remains symbolic and is retained by its original owner.
-/

public section

namespace Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Edge

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Polynomial.Dense.Gaussian.Evaluation (Reading)
open Purelib.Computation.Query

namespace Observation

set_option genInjectivity false in
/-- One original root-witness, numerator or denominator request at the retained edge start. -/
inductive Question where
  /-- Read the original transported root's exact initial witness. -/ | root
  /-- Read the original numerator at the exact edge-start parameter. -/ | numerator
  /-- Read the original denominator at the exact edge-start parameter. -/ | denominator
  deriving @[expose] DecidableEq

variable {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
  {prepared : SquareFactor.Prepared polynomial request} {segment : PathInput.Segment}
  {data : PathInput.Data prepared segment} {safe : data.Safe}

set_option genInjectivity false in
/-- The complete cached root or polynomial reading with its original edge and polynomial ownership. -/
inductive Reply (edge : OwnedCells.Edge safe) where
  /-- Retain the exact original root certificate and its same witness. -/ | root (cached : StartReading edge)
  /-- Retain the original numerator's certified polynomial value. -/ | numerator
      (reading : Reading prepared.weight.numerator)
  /-- Retain the original denominator's certified polynomial value. -/ | denominator
      (reading : Reading prepared.weight.denominator)

set_option genInjectivity false in
/-- A supplied cell reply violates its requested operation or its original evaluation point. -/
inductive Invalidity where
  /-- The reply names a different original operation from the requested one. -/ | operation
      (expected reported : Question) (different : reported ≠ expected)
  /-- The polynomial reading names a different point from this retained edge start. -/ | point
      (mismatch : Reading.Mismatch)

/-- The exact original model, retaining its identity certificate for direct compiled-cell assembly. -/
abbrev Realization (edge : OwnedCells.Edge safe) :=
  {model : CellModels.Model data edge.span // model = edge.model}

/-- A successful realization retains precisely the original model and its same defining identity. -/
private theorem realization_eq {edge : OwnedCells.Edge safe} (actual : Realization edge) :
    actual = ⟨edge.model, rfl⟩ := by
  cases actual with
  | mk model modelEq =>
      cases modelEq
      rfl

/-- Read the original root witness or cached path-bound polynomial value at the edge's actual start. -/
@[expose] def answer (edge : OwnedCells.Edge safe) : Question → Reply edge
  | .root => .root (StartReading.ofEdge edge)
  | .numerator => .numerator (Reading.ofValue prepared.weight.numerator
      (segment.point edge.span.interval.lower) (data.numerator.value edge.span.interval.lower)
      (data.numerator.value_eq edge.span.interval.lower).symm)
  | .denominator => .denominator (Reading.ofValue prepared.weight.denominator
      (segment.point edge.span.interval.lower) (data.denominator.value edge.span.interval.lower)
      (data.denominator.value_eq edge.span.interval.lower).symm)

/-- Assemble the same original model after validating the actual retained numerator and denominator replies. -/
private def assemble (edge : OwnedCells.Edge safe) (cached : StartReading edge)
    (numerator : Reading prepared.weight.numerator) (denominator : Reading prepared.weight.denominator) :
    Except Invalidity (Realization edge) :=
  if numeratorPoint : numerator.point = segment.point edge.span.interval.lower then
    if denominatorPoint : denominator.point = segment.point edge.span.interval.lower then
      let center := numerator.value / denominator.value / cached.reading.val
      have numeratorEq : numerator.value = data.numerator.value edge.span.interval.lower :=
        (numerator.value_eq_at _ numeratorPoint).trans (data.numerator.value_eq edge.span.interval.lower).symm
      have denominatorEq : denominator.value = data.denominator.value edge.span.interval.lower :=
        (denominator.value_eq_at _ denominatorPoint).trans (data.denominator.value_eq edge.span.interval.lower).symm
      have centerEq : center = CoefficientBounds.coefficient data edge.span.interval.lower cached.reading.val :=
        congrArg₂ (fun numerator denominator => numerator / denominator / cached.reading.val)
          numeratorEq denominatorEq
      .ok ⟨edge.modelWithReading cached center centerEq, edge.modelWithReading_eq cached center centerEq⟩
    else .error (.point ⟨segment.point edge.span.interval.lower, denominator.point, denominatorPoint⟩)
  else .error (.point ⟨segment.point edge.span.interval.lower, numerator.point, numeratorPoint⟩)

/-- Retain the original cell's three actual source requests as an expandable query construction. -/
def program (edge : OwnedCells.Edge safe) :
    Computation.Query.Program Question (Reply edge) (Except Invalidity (Realization edge)) :=
  (Computation.Query.Program.query .root).bind fun root =>
    match root with
    | .numerator _ => .pure (.error (.operation .root .numerator (by decide)))
    | .denominator _ => .pure (.error (.operation .root .denominator (by decide)))
    | .root cached => (Computation.Query.Program.query .numerator).bind fun numerator =>
        match numerator with
        | .root _ => .pure (.error (.operation .numerator .root (by decide)))
        | .denominator _ => .pure (.error (.operation .numerator .denominator (by decide)))
        | .numerator numerator => (Computation.Query.Program.query .denominator).map fun denominator =>
            match denominator with
            | .root _ => .error (.operation .denominator .root (by decide))
            | .numerator _ => .error (.operation .denominator .numerator (by decide))
            | .denominator denominator => assemble edge cached numerator denominator

/-- Compile the original cell model with its root witness and both polynomial evaluations explicitly requested. -/
def model (edge : OwnedCells.Edge safe) :
    Protocol Question (Reply edge) (Except Invalidity (Realization edge)) := (program edge).protocol

/-- Expanding the retained construction preserves the complete original cell-model execution and its source log. -/
theorem expand_value {Question Reply : Type}
    (edge : OwnedCells.Edge safe) (handlers : Observation.Question → Protocol Question Reply (Observation.Reply edge))
    (oracle : Question → Reply) :
    (((program edge).expand handlers).run oracle).value =
      (model edge).run (fun question => ((handlers question).run oracle).value) :=
  Computation.Query.Program.expand_value handlers (program edge) oracle

/-- The displayed canonical replies reconstruct exactly the original retained edge model. -/
theorem model_value (edge : OwnedCells.Edge safe) :
    ((model edge).run (answer edge)).value = .ok ⟨edge.model, rfl⟩ := by
  change assemble edge (StartReading.ofEdge edge)
    (Reading.ofValue prepared.weight.numerator (segment.point edge.span.interval.lower)
      (data.numerator.value edge.span.interval.lower) _)
    (Reading.ofValue prepared.weight.denominator (segment.point edge.span.interval.lower)
      (data.denominator.value edge.span.interval.lower) _) = _
  unfold assemble
  rewrite [dif_pos (show (Reading.ofValue prepared.weight.numerator
    (segment.point edge.span.interval.lower) (data.numerator.value edge.span.interval.lower) _).point =
      segment.point edge.span.interval.lower from rfl)]
  rewrite [dif_pos (show (Reading.ofValue prepared.weight.denominator
    (segment.point edge.span.interval.lower) (data.denominator.value edge.span.interval.lower) _).point =
      segment.point edge.span.interval.lower from rfl)]
  exact congrArg Except.ok (realization_eq _)

/-- The retained query construction returns the same certified original model under its original source replies. -/
theorem program_value (edge : OwnedCells.Edge safe) :
    ((program edge).protocol.run (answer edge)).value = .ok ⟨edge.model, rfl⟩ := model_value edge

/-- The complete model construction has the original model and exactly its three original source replies in order. -/
theorem model_execution (edge : OwnedCells.Edge safe) :
    (model edge).run (answer edge) =
      ⟨.ok ⟨edge.model, rfl⟩, [⟨.root, answer edge .root⟩, ⟨.numerator, answer edge .numerator⟩,
        ⟨.denominator, answer edge .denominator⟩]⟩ :=
  Basic.Execution.ext (model_value edge) rfl

/-- Replay of the retained root and polynomial replies gives the same original model without those source callbacks. -/
theorem model_replay (edge : OwnedCells.Edge safe) :
    (model edge).replayExact ((model edge).run (answer edge)).trace = .ok (.ok ⟨edge.model, rfl⟩) :=
  ((model edge).replayExact_run (answer edge)).trans (congrArg Except.ok (model_value edge))

/-- Outside-request payload changes preserve the original model and every retained root and coefficient reply. -/
theorem payload_erasure {Payload : Type} (edge : OwnedCells.Edge safe) (payload : Payload)
    (outside : Payload → Question → Reply edge) :
    (model edge).run (Boundary.Trace.overlay ((model edge).run (answer edge)).trace (outside payload)) =
      (model edge).run (answer edge) :=
  Protocol.annotation_erasure (model edge) (answer edge) payload outside

end Observation

end Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Edge
