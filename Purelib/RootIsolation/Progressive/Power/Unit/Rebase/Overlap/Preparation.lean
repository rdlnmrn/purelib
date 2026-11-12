module

public import Purelib.RootIsolation.Owner.Bridge.Interpolation
public import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap
public import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching.Preparation
import Purelib.RootIsolation.Power.Unit.Source.Preparation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Data.Fin.Bijection.Cache

/-! # Original rebase bridges consuming the retained matching refinement -/

public section

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap.Preparation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.Polynomial.Power.Gaussian.Progressive
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)

variable {source target : Canonical} {sourceUnit : normSq source = 1} {targetUnit : normSq target = 1}
    {degree : RootDegree} {degreeTwo : 2 ≤ degree.value}
    {small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo}
    {index : Fin (Coefficients.coefficientTable target degree).degree}

/-- Build the original same-polynomial bridge from the matching's actual saved state.

The complete selection retains the original assignment-radius refinement.
Both endpoint clearance certificates and the shared box consume that same
state, without refining or selecting an occurrence again.
-/
def fromSelection (selection : Matching.Preparation.Selection sourceUnit targetUnit degree degreeTwo small index) :
    { value : OwnerBridge
      (Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).polynomial
      (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).polynomial //
      value = unitRebaseBridge sourceUnit targetUnit degree degreeTwo small index } :=
  let state := selection.val.refined
  let owner : Owner.Local.Basic.LocalOwner (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree) :=
    { box := state.box, proper := state.proper, clearance := state.clearance,
      rawWindingFour := state.rawWindingFour }
  let bridge := (OwnerBridge.reflexive owner).cast
    (Move.Frame.unitTransportedFrame_polynomial sourceUnit targetUnit degree degreeTwo small).symm
    (Frame.Basic.chamberFrame_polynomial (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).symm
  ⟨bridge, by
    have same : state = unitRebaseRefinedState sourceUnit targetUnit degree degreeTwo small index :=
      selection.val.refined_eq
    let build := fun current : Power.Unit.Source.Preparation.State target degree =>
      let localOwner : Owner.Local.Basic.LocalOwner (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree) :=
        { box := current.box, proper := current.proper, clearance := current.clearance,
          rawWindingFour := current.rawWindingFour }
      (OwnerBridge.reflexive localOwner).cast
        (Move.Frame.unitTransportedFrame_polynomial sourceUnit targetUnit degree degreeTwo small).symm
        (Frame.Basic.chamberFrame_polynomial (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).symm
    exact congrArg build same⟩

/-- The rebase bridge uses the actual state already retained in the complete matching. -/
theorem fromSelection_box
    (selection : Matching.Preparation.Selection sourceUnit targetUnit degree degreeTwo small index) :
    (fromSelection selection).val.box = selection.val.refined.box := by
  unfold fromSelection
  rewrite [OwnerBridge.cast_box]
  rfl

/-- Both rebase endpoint certificates reuse the actual retained state clearance bound. -/
theorem fromSelection_bounds
    (selection : Matching.Preparation.Selection sourceUnit targetUnit degree degreeTwo small index) :
    (fromSelection selection).val.leftClearance.bound = selection.val.refined.clearance.bound ∧
      (fromSelection selection).val.rightClearance.bound = selection.val.refined.clearance.bound := by
  constructor
  · unfold fromSelection
    rewrite [OwnerBridge.cast_leftClearance_bound]
    rfl
  · unfold fromSelection
    rewrite [OwnerBridge.cast_rightClearance_bound]
    rfl

/-- Build a same-polynomial bridge from the actual certified assignment state.

Both endpoint clearances and winding certificates read the same retained
state. The bridge is indexed by the original endpoint polynomials, without
asserting equality to the canonical refinement's different bridge box.
-/
@[expose] def fromAssignment
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    OwnerBridge
      (Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).polynomial
      (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).polynomial :=
  let state := assignment.refinement.state
  let owner : Owner.Local.Basic.LocalOwner (Polynomial.Power.Gaussian.rootPolynomial target degree) :=
    { box := state.box, proper := state.proper, clearance := state.clearance,
      rawWindingFour := state.rawWindingFour }
  (OwnerBridge.reflexive owner).cast
    (Move.Frame.unitTransportedFrame_polynomial sourceUnit targetUnit degree degreeTwo small).symm
    (Frame.Basic.chamberFrame_polynomial (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).symm

/-- Every parameter of the actual rebase bridge reads the same original target polynomial. -/
theorem fromAssignment_polynomialAt
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index)
    (time : Data.Rat.Fraction.Rational) :
    (fromAssignment assignment).connection.polynomialAt time =
      Polynomial.Power.Gaussian.rootPolynomial target degree := by
  unfold fromAssignment
  rewrite [OwnerBridge.cast_polynomialAt]
  rfl

/-- The actual bridge retains the exact supplied assignment state box. -/
theorem fromAssignment_box
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    (fromAssignment assignment).box = assignment.refinement.state.box := by
  unfold fromAssignment
  rewrite [OwnerBridge.cast_box]
  rfl

/-- Both endpoint clearances retain the actual assignment state's same numerical bound. -/
theorem fromAssignment_bounds
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    (fromAssignment assignment).leftClearance.bound = assignment.refinement.state.clearance.bound ∧
      (fromAssignment assignment).rightClearance.bound = assignment.refinement.state.clearance.bound := by
  constructor
  · unfold fromAssignment
    rewrite [OwnerBridge.cast_leftClearance_bound]
    rfl
  · unfold fromAssignment
    rewrite [OwnerBridge.cast_rightClearance_bound]
    rfl

/-- Actual source strictness places the new bridge inside its original transported owner. -/
theorem fromAssignment_refines_transported
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    (fromAssignment assignment).box.Refines
      ((Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner index).box := by
  rewrite [fromAssignment_box]
  have contained := Geometry.Rational.Box.Refinement.StrictInterior.refines assignment.refinement.strict
  rewrite [Move.Track.Preparation.raw_box sourceUnit targetUnit degree degreeTwo small index] at contained
  exact contained

/-- Actual selected-cell strictness places the new bridge inside the retained original target occurrence. -/
theorem fromAssignment_refines_target
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    (fromAssignment assignment).box.Refines
      ((Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).owner
        assignment.selected).box := by
  rewrite [fromAssignment_box]
  have same := Matching.unitTargetTrack_get_box_eq_chamber_owner targetUnit degree degreeTwo assignment.owner
  exact (congrArg (fun box => assignment.refinement.state.box.Refines box) same).mp
    (Geometry.Rational.Box.Refinement.StrictInterior.refines assignment.strict)

/-- Replace the selected rebase bridge using an actual assignment and its computed original owner.

The original endpoint frames and complete matching are retained pointwise.
The selected source and target map queries read the cached pair, and the new
bridge consumes the actual supplied state rather than a canonical recomputation.
-/
@[expose] def overlapFromAssignment
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    ChamberOverlap
      (Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small)
      (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo) :=
  let original := unitRebaseOverlap sourceUnit targetUnit degree degreeTwo small
  let selected := assignment.selected
  have same : selected = original.matching.forward index :=
    assignment.selected_eq.trans
      (Matching.unitRebaseMatching_forward sourceUnit targetUnit degree degreeTwo small index).symm
  original.withBridge index selected same (fromAssignment assignment)
    (fromAssignment_refines_transported assignment) (fromAssignment_refines_target assignment)

/-- The selected source reads the actual supplied bridge from the new overlap. -/
theorem overlapFromAssignment_bridge
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    (overlapFromAssignment assignment).bridge index = fromAssignment assignment := by
  unfold overlapFromAssignment
  exact ChamberOverlap.withBridge_bridge_source _ _ _ _ _ _ _

/-- The new overlap preserves the complete original matching pointwise. -/
theorem overlapFromAssignment_matching_same
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    Data.Fin.Bijection.Same (overlapFromAssignment assignment).matching
      (unitRebaseOverlap sourceUnit targetUnit degree degreeTwo small).matching := by
  unfold overlapFromAssignment
  exact ChamberOverlap.withBridge_matching_same _ _ _ _ _ _ _

/-- The selected forward query returns the retained target without repeating canonical owner selection. -/
theorem overlapFromAssignment_forward
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    (overlapFromAssignment assignment).matching.forward index = assignment.selected := by
  unfold overlapFromAssignment
  exact Data.Fin.Bijection.cache_forward_source
    (unitRebaseOverlap sourceUnit targetUnit degree degreeTwo small).matching index assignment.selected
    (assignment.selected_eq.trans
      (Matching.unitRebaseMatching_forward sourceUnit targetUnit degree degreeTwo small index).symm)

/-- The selected backward query returns the retained source without repeating finite preimage search. -/
theorem overlapFromAssignment_backward
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    (overlapFromAssignment assignment).matching.backward assignment.selected = index := by
  unfold overlapFromAssignment
  exact Data.Fin.Bijection.cache_backward_target
    (unitRebaseOverlap sourceUnit targetUnit degree degreeTwo small).matching index assignment.selected
    (assignment.selected_eq.trans
      (Matching.unitRebaseMatching_forward sourceUnit targetUnit degree degreeTwo small index).symm)

/-- The selected overlap bridge uses the exact retained assignment-state box. -/
theorem overlapFromAssignment_box
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    ((overlapFromAssignment assignment).bridge index).box = assignment.refinement.state.box := by
  rewrite [overlapFromAssignment_bridge]
  exact fromAssignment_box assignment

/-- Both selected overlap endpoint clearances use the same retained assignment-state bound. -/
theorem overlapFromAssignment_bounds
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) :
    ((overlapFromAssignment assignment).bridge index).leftClearance.bound =
        assignment.refinement.state.clearance.bound ∧
      ((overlapFromAssignment assignment).bridge index).rightClearance.bound =
        assignment.refinement.state.clearance.bound := by
  rewrite [overlapFromAssignment_bridge]
  exact fromAssignment_bounds assignment

end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap.Preparation

end
