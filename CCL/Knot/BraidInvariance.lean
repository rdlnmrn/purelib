import CCL.Knot.ProjectedCrossings
import CCL.Knot.ArtinRelations

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

namespace CCL.Knot.BraidInvariance

open CCL.Knot.FiniteBraid
open CCL.Knot.ProjectedCrossings

abbrev ChamberOverlap := CCL.FiniteMonodromy.ChamberOverlap

/-! ## Chains with zero or one crossing -/

/-- Evidence that every atomic chart in a projected path is stationary. -/
inductive AllStationary {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → Prop
  | nil (frame : ProjectedFrame strands) :
      AllStationary (.nil frame)
  | cons {start middle finish : ProjectedFrame strands}
      (overlap : ChamberOverlap start.chamber middle.chamber)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          middle.ownerIndex position)
      {remaining : ProjectedPath middle finish}
      (remaining_stationary : AllStationary remaining) :
      AllStationary
        (.cons (.stationary overlap matching_order) remaining)

namespace AllStationary

theorem word_eq_nil {strands : Nat}
    {start finish : ProjectedFrame strands}
    {path : ProjectedPath start finish} (stationary : AllStationary path) :
    path.word = [] := by
  induction stationary with
  | nil frame => rfl
  | cons overlap matchingOrder remainingStationary inductionHypothesis =>
      simp only [ProjectedPath.word, ProjectedOverlap.word,
        ProjectedOverlap.event, Event.word, List.nil_append,
        inductionHypothesis]

end AllStationary

/-- Evidence that a projected path has precisely one nonstationary chart and
that chart is the displayed signed adjacent generator. -/
inductive OneCrossing {strands : Nat} (generator : Generator strands) :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → Prop
  | here {start middle finish : ProjectedFrame strands}
      (overlap : ChamberOverlap start.chamber middle.chamber)
      (geometry : CrossingGeometry start middle overlap generator)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          middle.ownerIndex (generator.permutation.forward position))
      {remaining : ProjectedPath middle finish}
      (remaining_stationary : AllStationary remaining) :
      OneCrossing generator
        (.cons (.crossing overlap generator geometry matching_order) remaining)
  | later {start middle finish : ProjectedFrame strands}
      (overlap : ChamberOverlap start.chamber middle.chamber)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          middle.ownerIndex position)
      {remaining : ProjectedPath middle finish}
      (remaining_crossing : OneCrossing generator remaining) :
      OneCrossing generator
        (.cons (.stationary overlap matching_order) remaining)

namespace OneCrossing

theorem word_eq_singleton {strands : Nat} {generator : Generator strands}
    {start finish : ProjectedFrame strands}
    {path : ProjectedPath start finish}
    (crossing : OneCrossing generator path) : path.word = [generator] := by
  induction crossing with
  | here overlap geometry matchingOrder remainingStationary =>
      simp only [ProjectedPath.word, ProjectedOverlap.word,
        ProjectedOverlap.event, Event.word,
        remainingStationary.word_eq_nil, List.append_nil]
  | later overlap matchingOrder remainingCrossing inductionHypothesis =>
      simp only [ProjectedPath.word, ProjectedOverlap.word,
        ProjectedOverlap.event, Event.word, List.nil_append,
        inductionHypothesis]

end OneCrossing

/-! ## Operational cell and path subdivision -/

/-- Replace one atomic chart by a finer finite chain with the same event:
zero crossings remain zero, and one signed crossing remains exactly that
signed crossing. -/
inductive CellSubdivision {strands : Nat}
    {start finish : ProjectedFrame strands} :
    ProjectedOverlap start finish → ProjectedPath start finish → Prop
  | stationary
      (overlap : ChamberOverlap start.chamber finish.chamber)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          finish.ownerIndex position)
      (fine : ProjectedPath start finish)
      (fine_stationary : AllStationary fine) :
      CellSubdivision (.stationary overlap matching_order) fine
  | crossing
      (overlap : ChamberOverlap start.chamber finish.chamber)
      (generator : Generator strands)
      (geometry : CrossingGeometry start finish overlap generator)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          finish.ownerIndex (generator.permutation.forward position))
      (fine : ProjectedPath start finish)
      (fine_crossing : OneCrossing generator fine) :
      CellSubdivision
        (.crossing overlap generator geometry matching_order) fine

namespace CellSubdivision

theorem word_eq {strands : Nat}
    {start finish : ProjectedFrame strands}
    {coarse : ProjectedOverlap start finish}
    {fine : ProjectedPath start finish}
    (subdivision : CellSubdivision coarse fine) :
    fine.word = coarse.word := by
  cases subdivision with
  | stationary overlap matchingOrder fine fineStationary =>
      rw [fineStationary.word_eq_nil]
      rfl
  | crossing overlap generator geometry matchingOrder fine fineCrossing =>
      rw [fineCrossing.word_eq_singleton]
      rfl

end CellSubdivision

/-- Cellwise further subdivision of a certified projected path. -/
inductive Refinement {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → ProjectedPath start finish → Prop
  | nil (frame : ProjectedFrame strands) :
      Refinement (.nil frame) (.nil frame)
  | cons {start middle finish : ProjectedFrame strands}
      (coarseStep : ProjectedOverlap start middle)
      {coarseRemaining fineRemaining : ProjectedPath middle finish}
      (fineCell : ProjectedPath start middle)
      (cell : CellSubdivision coarseStep fineCell)
      (remaining : Refinement coarseRemaining fineRemaining) :
      Refinement (.cons coarseStep coarseRemaining)
        (fineCell.append fineRemaining)

namespace Refinement

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

/-! ## Artin-equivalent projected paths -/

/-- Two certified projected paths represent the same braid class when their
extracted words are joined by a finite proof made from the Artin rewrites. -/
def BraidClassSame {strands : Nat}
    {start finish : ProjectedFrame strands}
    (left right : ProjectedPath start finish) : Prop :=
  CCL.Knot.ArtinRelations.Equivalent left.word right.word

namespace BraidClassSame

theorem refl {strands : Nat} {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) : BraidClassSame path path :=
  CCL.Knot.ArtinRelations.Equivalent.refl path.word

theorem symm {strands : Nat} {start finish : ProjectedFrame strands}
    {left right : ProjectedPath start finish}
    (same : BraidClassSame left right) : BraidClassSame right left :=
  CCL.Knot.ArtinRelations.Equivalent.symm same

theorem trans {strands : Nat} {start finish : ProjectedFrame strands}
    {first second third : ProjectedPath start finish}
    (firstSecond : BraidClassSame first second)
    (secondThird : BraidClassSame second third) :
    BraidClassSame first third :=
  CCL.Knot.ArtinRelations.Equivalent.trans firstSecond secondThird

theorem of_refinement {strands : Nat}
    {start finish : ProjectedFrame strands}
    {coarse fine : ProjectedPath start finish}
    (refinement : Refinement coarse fine) : BraidClassSame coarse fine := by
  unfold BraidClassSame
  rw [refinement.word_eq]
  exact CCL.Knot.ArtinRelations.Equivalent.refl _

theorem append {strands : Nat}
    {start middle finish : ProjectedFrame strands}
    {firstLeft firstRight : ProjectedPath start middle}
    {secondLeft secondRight : ProjectedPath middle finish}
    (first : BraidClassSame firstLeft firstRight)
    (second : BraidClassSame secondLeft secondRight) :
    BraidClassSame (firstLeft.append secondLeft)
      (firstRight.append secondRight) := by
  unfold BraidClassSame
  rw [ProjectedPath.word_append, ProjectedPath.word_append]
  exact CCL.Knot.ArtinRelations.Equivalent.append first second

/-- Artin-equivalent extractions have the same endpoint owner transport. -/
theorem transport_eq {strands : Nat}
    {start finish : ProjectedFrame strands}
    {left right : ProjectedPath start finish}
    (same : BraidClassSame left right) (position : Fin strands) :
    left.chamberPath.transport.forward (start.ownerIndex position) =
      right.chamberPath.transport.forward (start.ownerIndex position) := by
  calc
    left.chamberPath.transport.forward (start.ownerIndex position) =
        finish.ownerIndex (left.word.permutation.forward position) :=
      left.transport_agrees position
    _ = finish.ownerIndex (right.word.permutation.forward position) :=
      congrArg finish.ownerIndex (same.permutationSame position)
    _ = right.chamberPath.transport.forward (start.ownerIndex position) :=
      (right.transport_agrees position).symm

theorem writhe_eq {strands : Nat}
    {start finish : ProjectedFrame strands}
    {left right : ProjectedPath start finish}
    (same : BraidClassSame left right) :
    left.word.writhe = right.word.writhe :=
  CCL.Knot.ArtinRelations.Equivalent.writhe_eq same

end BraidClassSame

end CCL.Knot.BraidInvariance
