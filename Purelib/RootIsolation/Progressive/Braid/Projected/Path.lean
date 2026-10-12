module
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Fin.Bijection.Iteration
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
public import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.Topology.Knot.Braid.Word.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
public import Purelib.Topology.Knot.Closure.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.RootIsolation.Progressive.Braid.Projected.Frame (ProjectedFrame)
open Purelib.RootIsolation.Progressive.Braid.Projected.Overlap (ProjectedOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Topology.Knot.Braid (Word)

open Purelib

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Certified projected crossings of finite root paths

An Artin generator acts on the left-to-right positions of a chosen planar
projection, whereas finite monodromy transports the persistent owner indices
of root boxes.  Those numberings need not coincide.  This file records their
finite relabelling explicitly and folds atomic projected chamber overlaps into
an executable braid word.

A crossing chart contains only rational root boxes, a signed adjacent
generator, an exact owner-matching law, and a strict height separation of the
two crossing strands.  It is therefore finite certificate data: no completed
root track or configuration space is introduced.  The extraction theorem
proves that evaluating the resulting word gives exactly the chamber-path
transport, expressed in the endpoint projection orders.
-/

namespace Purelib.RootIsolation.Progressive.Braid.Projected.Path

/-! ## Paths and extraction -/

set_option genInjectivity false in
/-- A finite chamber path whose every subdivision cell has a certified
atomic projected event.  Adjacent cells share the same projected frame, so
no endpoint relabelling is hidden between their certificates. -/
inductive ProjectedPath {strands : Nat} :
    (start finish : ProjectedFrame strands) → Type 2
  /-- The empty projected path at one original frame. -/ | nil (frame : ProjectedFrame
    strands) : ProjectedPath frame frame
  /-- An original projected overlap followed by a path sharing its exact finishing frame. -/ | cons {start middle finish
    : ProjectedFrame strands}
      (step : ProjectedOverlap start middle)
      (remaining : ProjectedPath middle finish) :
      ProjectedPath start finish

constructive_injectivity ProjectedPath

namespace ProjectedPath

/-- Read the original chamber path underlying the retained projected events. -/
def chamberPath {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      Progressive.Braid.Projected.Path.ProjectedPath start finish →
        ChamberPath start.chamber finish.chamber
  | _, _, .nil frame => .nil frame.chamber
  | _, _, .cons step remaining =>
      .cons step.chamberOverlap remaining.chamberPath

/-- Concatenate the braid words of the original projected events in path order. -/
def word {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      Progressive.Braid.Projected.Path.ProjectedPath start finish → Word strands
  | _, _, .nil _ => []
  | _, _, .cons step remaining => step.word ++ remaining.word

/-- Count the actual retained projected event steps. -/
def stepCount {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      Progressive.Braid.Projected.Path.ProjectedPath start finish → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ remaining => remaining.stepCount + 1

/-- Join projected paths at their exact shared projected frame. -/
def append {strands : Nat}
    {start middle finish : ProjectedFrame strands}
    (first : Progressive.Braid.Projected.Path.ProjectedPath start middle)
    (second : Progressive.Braid.Projected.Path.ProjectedPath middle finish) :
      Progressive.Braid.Projected.Path.ProjectedPath start finish :=
  match first with
  | .nil _ => second
  | .cons step remaining => .cons step (remaining.append second)

/-- Reverse the original projected path and each of its certified signed events. -/
def reverse {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      Progressive.Braid.Projected.Path.ProjectedPath start finish → Progressive.Braid.Projected.Path.ProjectedPath
        finish start
  | _, _, .nil frame => .nil frame
  | _, _, .cons (start := start) step remaining =>
      remaining.reverse.append (.cons step.reverse (.nil start))

/-- Reading chamber paths commutes with joining the original projected paths. -/
@[simp] theorem chamberPath_append {strands
  : Nat}
    {start middle finish : ProjectedFrame strands}
    (first : Progressive.Braid.Projected.Path.ProjectedPath start middle)
    (second : Progressive.Braid.Projected.Path.ProjectedPath middle finish) :
    (first.append second).chamberPath =
      first.chamberPath.append second.chamberPath := by
  induction first with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [Progressive.Braid.Projected.Path.ProjectedPath.append,
        Progressive.Braid.Projected.Path.ProjectedPath.chamberPath,
        ChamberPath.append, -eq_self, -iff_self]
      rewrite [inductionHypothesis]
      rfl

/-- Joining projected paths concatenates their retained braid words in order. -/
@[simp] theorem word_append {strands : Nat}
    {start middle finish : ProjectedFrame strands}
    (first : Progressive.Braid.Projected.Path.ProjectedPath start middle)
    (second : Progressive.Braid.Projected.Path.ProjectedPath middle finish) :
    (first.append second).word = first.word ++ second.word := by
  induction first with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [Progressive.Braid.Projected.Path.ProjectedPath.append,
        Progressive.Braid.Projected.Path.ProjectedPath.word, -eq_self, -iff_self]
      rewrite [inductionHypothesis]
      exact (Data.List.Append.append_assoc _ _ _).symm

/-- Reversing a projected path reverses its original underlying chamber path. -/
@[simp] theorem chamberPath_reverse {strands
  : Nat}
    {start finish : ProjectedFrame strands}
    (path : Progressive.Braid.Projected.Path.ProjectedPath start finish) :
    path.reverse.chamberPath = path.chamberPath.reverse := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [Progressive.Braid.Projected.Path.ProjectedPath.reverse,
        Progressive.Braid.Projected.Path.ProjectedPath.chamberPath_append,
        Progressive.Braid.Projected.Path.ProjectedPath.chamberPath,
        inductionHypothesis, ProjectedOverlap.reverse_chamberOverlap,
        ChamberPath.reverse, -eq_self, -iff_self]
      rfl

/-- Reversing a projected path gives the inverse of its retained original braid word. -/
@[simp] theorem word_reverse {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : Progressive.Braid.Projected.Path.ProjectedPath start finish) :
    path.reverse.word = path.word.inverse := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [Progressive.Braid.Projected.Path.ProjectedPath.reverse,
        Progressive.Braid.Projected.Path.ProjectedPath.word_append, Progressive.Braid.Projected.Path.ProjectedPath.word,
        inductionHypothesis,
        ProjectedOverlap.reverse_word,
        Word.inverse_append,
        Data.List.Append.append_nil, -eq_self, -iff_self]
      rfl

/-- Joining projected paths adds their original step counts. -/
@[simp] theorem stepCount_append {strands :
  Nat}
    {start middle finish : ProjectedFrame strands}
    (first : Progressive.Braid.Projected.Path.ProjectedPath start middle)
    (second : Progressive.Braid.Projected.Path.ProjectedPath middle finish) :
    (first.append second).stepCount = first.stepCount + second.stepCount := by
  induction first with
  | nil frame => exact (Nat.zero_add _).symm
  | cons step remaining inductionHypothesis =>
      simp only [Progressive.Braid.Projected.Path.ProjectedPath.append,
        Progressive.Braid.Projected.Path.ProjectedPath.stepCount, -eq_self, -iff_self]
      rewrite [inductionHypothesis]
      omega0

/-- The underlying chamber path has exactly the original projected path's step count. -/
@[simp] theorem chamberPath_stepCount
  {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : Progressive.Braid.Projected.Path.ProjectedPath start finish) :
    path.chamberPath.stepCount = path.stepCount := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [Progressive.Braid.Projected.Path.ProjectedPath.chamberPath,
        ChamberPath.stepCount,
        Progressive.Braid.Projected.Path.ProjectedPath.stepCount, -eq_self, -iff_self]
      exact congrArg Nat.succ inductionHypothesis

/-- Evaluation of the extracted word agrees exactly with owner transport,
after applying the independently certified projection order at each endpoint.
This is the central finite braid-extraction theorem. -/
theorem transport_agrees {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : Progressive.Braid.Projected.Path.ProjectedPath start finish) (position : Fin strands) :
    path.chamberPath.transport.forward (start.ownerIndex position) =
      finish.ownerIndex (path.word.permutation.forward position) := by
  induction path generalizing position with
  | nil frame => rfl
  | @cons start middle finish step remaining inductionHypothesis =>
      calc
        (Progressive.Braid.Projected.Path.ProjectedPath.cons step remaining).chamberPath.transport.forward
            (start.ownerIndex position) =
          remaining.chamberPath.transport.forward
            (step.chamberOverlap.matching.forward
              (start.ownerIndex position)) := rfl
        _ = remaining.chamberPath.transport.forward
            (middle.ownerIndex
              (step.event.permutation.forward position)) := by
          rw [step.matching_order position]
        _ = finish.ownerIndex
            (remaining.word.permutation.forward
              (step.event.permutation.forward position)) :=
          inductionHypothesis (step.event.permutation.forward position)
        _ = finish.ownerIndex
            ((step.word ++ remaining.word).permutation.forward position) := by
          rw [Word.permutation_append]
          rfl

/-- Finite iteration of owner monodromy agrees with the retained braid permutation through the original projection-order
bijection. -/
theorem iterate_agrees {strands : Nat}
  (frame : ProjectedFrame strands)
    (loop : Progressive.Braid.Projected.Path.ProjectedPath frame frame) (steps : Nat)
    (position : Fin strands) :
    Data.Fin.Bijection.iterateForward
        loop.chamberPath.monodromy steps (frame.ownerIndex position) =
      frame.ownerIndex
        (Data.Fin.Bijection.iterateForward
          loop.word.permutation steps position) := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [Data.Fin.Bijection.iterateForward_succ,
        Data.Fin.Bijection.iterateForward_succ,
        inductionHypothesis]
      exact loop.transport_agrees
        (Data.Fin.Bijection.iterateForward
          loop.word.permutation steps position)

/-- The finite combinatorial closure extracted from a closed projected root
path. -/
def closure {strands : Nat} (frame :
  ProjectedFrame strands)
    (loop : Progressive.Braid.Projected.Path.ProjectedPath frame frame) : Topology.Knot.Braid.Closure where
  strands := strands
  word := loop.word

/-- A one-cycle owner monodromy remains one cycle after the explicit
projection-order conjugacy.  Thus the extracted finite closure detects knots
independently of the chamber's internal numbering of its owners. -/
theorem
  closure_isKnot_of_monodromy_isSingleCycle
  {strands : Nat}
    (frame : ProjectedFrame strands) (loop :
      Progressive.Braid.Projected.Path.ProjectedPath frame frame)
    (single : Data.Fin.Bijection.IsSingleCycle
      loop.chamberPath.monodromy) :
    (Progressive.Braid.Projected.Path.ProjectedPath.closure frame loop).IsKnot := by
  change Data.Fin.Bijection.IsSingleCycle
    loop.word.permutation
  refine
    { return_at_count := ?_
      no_early_return := ?_ }
  · intro position
    apply frame.ownerIndex_injective
    have returns :
        Data.Fin.Bijection.iterateForward
            loop.chamberPath.monodromy strands
              (frame.ownerIndex position) = frame.ownerIndex position := by
      simpa only [frame.degree_eq] using
        single.return_at_count (frame.ownerIndex position)
    rw [Progressive.Braid.Projected.Path.ProjectedPath.iterate_agrees frame loop strands position] at returns
    exact returns
  · intro position steps positive small returned
    apply single.no_early_return (frame.ownerIndex position) steps positive
    · simpa only [frame.degree_eq] using small
    · rw [Progressive.Braid.Projected.Path.ProjectedPath.iterate_agrees frame loop steps position]
      exact congrArg frame.ownerIndex returned

end ProjectedPath

end Purelib.RootIsolation.Progressive.Braid.Projected.Path

end
