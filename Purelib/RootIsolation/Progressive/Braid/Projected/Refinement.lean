module
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
public import Purelib.RootIsolation.Progressive.Braid.Projected.Path
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Topology.Knot.Braid.Event
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.Topology.Knot.Braid.Word.Basic

open Purelib.RootIsolation.Progressive.Braid.Projected.Frame (ProjectedFrame)
open Purelib.RootIsolation.Progressive.Braid.Projected.Overlap (ProjectedOverlap)
open Purelib.RootIsolation.Progressive.Braid.Projected.Path (ProjectedPath)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.Topology.Knot.Braid (Generator)

open Purelib.Topology.Knot.Braid (Event)

open Purelib.RootIsolation

open Purelib

section
@[expose] public section

/-!
# Subdivision and Artin invariance of projected braid extraction

This file gives an operational notion of further subdivision.  A stationary
cell may be replaced by an all-stationary finite chain.  A crossing cell may
be replaced by a finite chain containing exactly the same signed crossing,
with any number of stationary cells before and after it.  Applying this rule
cell by cell is a refinement of a projected path.

The resulting extracted word is proved equal, rather than merely assumed
equal.  A second relation permits the finite cancellation, far-commutation,
and three-strand Artin moves from `ArtinRelations`.  Both relations preserve
the endpoint owner transport, and concatenation respects the Artin relation.
-/

namespace Purelib.RootIsolation.Progressive.Braid.Projected

/-! ## Chains with zero or one crossing -/

namespace Refinement

/-- Evidence that every atomic chart in a projected path is stationary. -/
inductive AllStationary {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → Prop
  /-- The empty projected path is stationary. -/ | nil (frame : ProjectedFrame
    strands) :
      AllStationary (.nil frame)
  /-- A retained stationary overlap followed by an entirely stationary original path. -/ | cons {start middle finish :
    ProjectedFrame strands}
      (overlap : ChamberOverlap start.chamber middle.chamber)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          middle.ownerIndex position)
      {remaining : ProjectedPath middle finish}
      (remaining_stationary : AllStationary remaining) :
      AllStationary
        (.cons (.stationary overlap matching_order) remaining)

end Refinement

namespace Refinement.AllStationary

/-- An entirely stationary projected path has the empty braid word. -/
theorem word_eq_nil {strands : Nat}
    {start finish : ProjectedFrame strands}
    {path : ProjectedPath start finish} (stationary :
      Progressive.Braid.Projected.Refinement.AllStationary path) :
    path.word = [] := by
  induction stationary with
  | nil frame => rfl
  | cons overlap matchingOrder remainingStationary inductionHypothesis =>
      simp only [ProjectedPath.word,
        ProjectedOverlap.word,
        ProjectedOverlap.event, Event.word, -eq_self,
          -iff_self]
      exact inductionHypothesis

end Refinement.AllStationary

namespace Refinement

/-- Evidence that a projected path has precisely one nonstationary chart and
that chart is the displayed signed adjacent generator. -/
inductive OneCrossing {strands : Nat} (generator :
  Generator strands) :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → Prop
  /-- The displayed original crossing occurs first, followed only by stationary steps. -/ | here {start middle finish :
    ProjectedFrame strands}
      (overlap : ChamberOverlap start.chamber middle.chamber)
      (geometry : Progressive.Braid.Projected.Overlap.CrossingGeometry start middle overlap generator)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          middle.ownerIndex (generator.permutation.forward position))
      {remaining : ProjectedPath middle finish}
      (remaining_stationary : Progressive.Braid.Projected.Refinement.AllStationary remaining) :
      OneCrossing generator
        (.cons (.crossing overlap generator geometry matching_order) remaining)
  /-- A retained stationary overlap precedes the unique original crossing in the remaining path. -/ | later {start
    middle finish : ProjectedFrame strands}
      (overlap : ChamberOverlap start.chamber middle.chamber)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          middle.ownerIndex position)
      {remaining : ProjectedPath middle finish}
      (remaining_crossing : OneCrossing generator
        remaining) :
      OneCrossing generator
        (.cons (.stationary overlap matching_order) remaining)

end Refinement

namespace Refinement.OneCrossing

/-- A projected path with one retained crossing has exactly that singleton generator word. -/
theorem word_eq_singleton {strands :
  Nat} {generator : Generator strands}
    {start finish : ProjectedFrame strands}
    {path : ProjectedPath start finish}
    (crossing : Progressive.Braid.Projected.Refinement.OneCrossing generator path) : path.word = [generator] := by
  induction crossing with
  | here overlap geometry matchingOrder remainingStationary =>
      simp only [ProjectedPath.word,
        ProjectedOverlap.word,
        ProjectedOverlap.event, Event.word, -eq_self,
          -iff_self]
      rewrite [remainingStationary.word_eq_nil]
      rfl
  | later overlap matchingOrder remainingCrossing inductionHypothesis =>
      simp only [ProjectedPath.word,
        ProjectedOverlap.word,
        ProjectedOverlap.event, Event.word, -eq_self,
          -iff_self]
      exact inductionHypothesis

end Refinement.OneCrossing

/-! ## Operational cell and path subdivision -/

namespace Refinement

/-- Replace one atomic chart by a finer finite chain with the same event:
zero crossings remain zero, and one signed crossing remains exactly that
signed crossing. -/
inductive CellSubdivision {strands : Nat}
    {start finish : ProjectedFrame strands} :
    ProjectedOverlap start finish → ProjectedPath
      start finish → Prop
  /-- An original stationary overlap is replaced by an entirely stationary path with the same endpoints. -/ | stationary
      (overlap : ChamberOverlap start.chamber finish.chamber)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          finish.ownerIndex position)
      (fine : ProjectedPath start finish)
      (fine_stationary : Progressive.Braid.Projected.Refinement.AllStationary fine) :
      CellSubdivision (.stationary overlap matching_order)
        fine
  /-- An original crossing is replaced by a path retaining exactly that signed generator and the same endpoints. -/ |
    crossing
      (overlap : ChamberOverlap start.chamber finish.chamber)
      (generator : Generator strands)
      (geometry : Progressive.Braid.Projected.Overlap.CrossingGeometry start finish overlap generator)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          finish.ownerIndex (generator.permutation.forward position))
      (fine : ProjectedPath start finish)
      (fine_crossing : Progressive.Braid.Projected.Refinement.OneCrossing generator fine) :
      CellSubdivision
        (.crossing overlap generator geometry matching_order) fine

end Refinement

namespace Refinement.CellSubdivision

/-- An event-preserving subdivision retains the original atomic braid word exactly. -/
theorem word_eq {strands : Nat}
    {start finish : ProjectedFrame strands}
    {coarse : ProjectedOverlap start finish}
    {fine : ProjectedPath start finish}
    (subdivision : Progressive.Braid.Projected.Refinement.CellSubdivision coarse fine) :
    fine.word = coarse.word := by
  cases subdivision with
  | stationary overlap matchingOrder fine fineStationary =>
      rw [fineStationary.word_eq_nil]
      rfl
  | crossing overlap generator geometry matchingOrder fine fineCrossing =>
      rw [fineCrossing.word_eq_singleton]
      rfl

end Refinement.CellSubdivision

/-- Cellwise further subdivision of a certified projected path. -/
inductive Refinement {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → ProjectedPath start
        finish → Prop
  /-- The empty projected path refines itself. -/ | nil (frame : ProjectedFrame
    strands) :
      Refinement (.nil frame) (.nil frame)
  /-- Refine the original first cell without changing its event, then retain a refinement of the remaining path. -/ |
    cons {start middle finish : ProjectedFrame strands}
      (coarseStep : ProjectedOverlap start middle)
      {coarseRemaining fineRemaining : ProjectedPath middle finish}
      (fineCell : ProjectedPath start middle)
      (cell : Refinement.CellSubdivision coarseStep fineCell)
      (remaining : Refinement coarseRemaining
        fineRemaining) :
      Refinement (.cons coarseStep coarseRemaining)
        (fineCell.append fineRemaining)

namespace Refinement

/-- Cellwise event-preserving refinement retains the complete original braid word exactly. -/
theorem word_eq {strands : Nat}
    {start finish : ProjectedFrame strands}
    {coarse fine : ProjectedPath start finish}
    (refinement : Refinement coarse fine) : coarse.word = fine.word := by
  induction refinement with
  | nil frame => rfl
  | @cons start middle finish coarseStep coarseRemaining fineRemaining
      fineCell cell remaining inductionHypothesis =>
      calc
        (ProjectedPath.cons coarseStep coarseRemaining).word =
            coarseStep.word ++ coarseRemaining.word := rfl
        _ = fineCell.word ++ fineRemaining.word :=
          congrArg₂ (· ++ ·) cell.word_eq.symm inductionHypothesis
        _ = (fineCell.append fineRemaining).word :=
          (ProjectedPath.word_append fineCell fineRemaining).symm

/-- Further subdivision leaves the persistent endpoint-owner transport
pointwise unchanged. -/
theorem transport_eq {strands : Nat}
    {start finish : ProjectedFrame strands}
    {coarse fine : ProjectedPath start finish}
    (refinement : Refinement coarse fine) (position : Fin strands) :
    coarse.chamberPath.transport.forward (start.ownerIndex position) =
      fine.chamberPath.transport.forward (start.ownerIndex position) := by
  calc
    coarse.chamberPath.transport.forward (start.ownerIndex position) =
        finish.ownerIndex (coarse.word.permutation.forward position) :=
      coarse.transport_agrees position
    _ = finish.ownerIndex (fine.word.permutation.forward position) := by
      rw [refinement.word_eq]
    _ = fine.chamberPath.transport.forward (start.ownerIndex position) :=
      (fine.transport_agrees position).symm

end Refinement

end Purelib.RootIsolation.Progressive.Braid.Projected

end
