module

public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Path
public import Purelib.RootIsolation.Progressive.Power.Frame.Preparation
public import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap.Preparation
public import Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap.Preparation

/-! # Original unit-power paths consuming their retained complete target frame -/

public section

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Path.Preparation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)

/-- Build the exact original three-overlap path with its saved independently isolated target frame.

All original overlap matchings and bridge selectors remain their original
complete records, transported only along the retained whole-frame equality.
The explicit body lets owner-cache construction follow these same three
original cons cells without materializing the canonical target isolation.
-/
@[expose] def fromFrame {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (prepared : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo) :
    { value : ChamberPath
      (Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo)
      (Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo) //
      value = unitSmallMovePath sourceUnit targetUnit degree degreeTwo small } :=
  let second : ChamberOverlap (Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small)
      prepared.frame := prepared.frame_eq.symm ▸
    Rebase.Overlap.unitRebaseOverlap sourceUnit targetUnit degree degreeTwo small
  let third : ChamberOverlap prepared.frame
      (Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo) :=
    (Frame.Overlap.Preparation.fromFrame
      (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo prepared).val
  let path := ChamberPath.cons (Overlap.unitMoveOverlap sourceUnit targetUnit degree degreeTwo small)
    (.cons second (.cons third (.nil _)))
  ⟨path, by
    rcases prepared with ⟨frame, same, _, _, _, _, _, _⟩
    cases same
    rfl⟩

/-- The retained path has exactly the original three overlap occurrences. -/
theorem fromFrame_stepCount {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (prepared : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo) :
    (fromFrame sourceUnit targetUnit degree degreeTwo small prepared).val.stepCount = 3 := rfl

/-- Build three original endpoint overlaps using the actual retained middle assignment.

The first move and final robust rebase remain original overlaps. Only the
selected middle bridge uses the supplied certified refinement; its cached
matching preserves original owner indices pointwise, without identifying
this path with the canonical path's different numerical bridges.
-/
@[expose] def fromAssignment {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (prepared : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (assignment : Rebase.Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)) :
    ChamberPath
      (Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo)
      (Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo) :=
  let second : ChamberOverlap (Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small)
      prepared.frame := prepared.frame_eq.symm ▸ Rebase.Overlap.Preparation.overlapFromAssignment assignment
  let third := (Frame.Overlap.Preparation.fromFrame
    (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo prepared).val
  .cons (Overlap.unitMoveOverlap sourceUnit targetUnit degree degreeTwo small)
    (.cons second (.cons third (.nil _)))

/-- The actual assignment path retains all three ordered overlap occurrences. -/
theorem fromAssignment_stepCount {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (prepared : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (assignment : Rebase.Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)) :
    (fromAssignment sourceUnit targetUnit degree degreeTwo small index prepared assignment).stepCount = 3 := rfl

/-- The final occurrence reads the actual assignment's cached selected index. -/
theorem fromAssignment_finalIndex {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (prepared : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (assignment : Rebase.Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)) :
    (fromAssignment sourceUnit targetUnit degree degreeTwo small index prepared assignment).finalIndex index =
      Fin.cast (Frame.Overlap.isolationRobustCountEq (nonzero_of_normSq_eq_one targetUnit)
        targetUnit degree degreeTwo) assignment.selected := by
  rcases prepared with ⟨frame, same, _, _, _, _, _, _⟩
  cases same
  unfold fromAssignment
  simp only [ChamberPath.finalIndex_cons, ChamberPath.finalIndex_nil,
    Overlap.unitMoveOverlap, Frame.Overlap.Preparation.fromFrame, Purelib.Data.Fin.Bijection.cast_forward]
  apply Fin.ext
  exact congrArg Fin.val (Rebase.Overlap.Preparation.overlapFromAssignment_forward assignment)

/-- Pointwise matching preserves the original final occurrence without a whole-path equality. -/
theorem fromAssignment_finalIndex_eq {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (prepared : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (assignment : Rebase.Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)) :
    (fromAssignment sourceUnit targetUnit degree degreeTwo small index prepared assignment).finalIndex index =
      (unitSmallMovePath sourceUnit targetUnit degree degreeTwo small).finalIndex index := by
  rewrite [fromAssignment_finalIndex]
  have original := congrArg Fin.val
    (unitSmallMovePath_finalIndex_degree sourceUnit targetUnit degree degreeTwo small index)
  apply Fin.ext
  exact (congrArg Fin.val assignment.selected_eq).trans original.symm

end Purelib.RootIsolation.Progressive.Power.Unit.Move.Path.Preparation

end
