module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Preparation
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Path.Preparation
public import Purelib.RootIsolation.Progressive.Power.Frame.Preparation
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame.Preparation
public import Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap
import Purelib.Data.Fin.Bijection.Search
import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

public import Purelib.RootIsolation.Progressive.Power.Unit.Owner.Preparation
import Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.RootIsolation.Power.Unit.Source.Refinement
import Purelib.RootIsolation.Track.Transport

/-! # Cached numerical occurrences along the original three-overlap unit-power path -/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Power

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation
open Purelib.RootIsolation.Progressive.Power
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Factorization
open Purelib.Polynomial.Dense.Gaussian.Coprime

/-- Compare one original isolated target cache with the same indexed robust endpoint through its retained source state.

The original globally supported source state lies inside both owners. A
single common root starts at that supplied state; the original nested and
constant-cofactor comparisons retain both independent numerical channels.
Only the displayed finite index equality and original prepared readbacks
identify the endpoint occurrence.
-/
def robustEndpointEquivalent {parameter : Canonical} (nonzero : parameter ≠ 0)
    (unit : normSq parameter = 1) (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (frame : Frame.Preparation.Prepared nonzero degree degreeTwo) (index : Fin degree.value)
    {isolatedTrack : WindingOneTrack (Polynomial.Power.Gaussian.rootPolynomial parameter degree)
      (Polynomial.Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        (Polynomial.Power.Gaussian.rootPolynomial parameter degree))}
    (isolatedRoot : CertifiedName isolatedTrack) (sameTrack : isolatedTrack = (frame.track index).val)
    (robust : Unit.Owner.Preparation.Prepared nonzero unit degree degreeTwo index)
    {endpointIndex : (Unit.Frame.robustChamberFrame nonzero unit degree degreeTwo).Index}
    (endpoint : Root (Unit.Frame.robustChamberFrame nonzero unit degree degreeTwo) endpointIndex)
    (sameIndex : Fin.cast (Unit.Frame.robustChamberFrame_degree nonzero unit degree degreeTwo)
      endpointIndex = index) :
    Approximation.Gaussian.Equivalence.NamedEquivalent isolatedRoot.value.name endpoint.certificate.value.name := by
  let track := isolatedTrack
  let current := robust.source.val
  let common := certifiedName (track.atState current) frame.input.degreePositive
  have strict : current.box.StrictInterior track.initial.box := by
    change robust.source.val.box.StrictInterior isolatedTrack.initial.box
    rewrite [sameTrack, robust.source.property, (frame.track index).property]
    exact (Power.Isolation.Track.isolatedTrack nonzero degree degreeTwo index).strict _ _ _
  let isolatedCommon := isolatedRoot.equivalent_nested frame.input common strict
  let polynomial := Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let one : GaussianPolynomial := DensePolynomial.constant 1
  have factorization : Identity.ProductIdentity polynomial polynomial one :=
    Identity.factorizationOfCandidateEvals polynomial polynomial one
      (by
        intro point _
        rewrite [DensePolynomial.eval_constant]
        exact (Data.Gaussian.Basic.mul_one _).symm)
  let coprime := Operations.CoprimeCertificate.constantRight frame.input.nonzero
  let localOne : FactorRegion.LocalCofactor one (track.atState current).initial.box :=
    .inl ⟨1, by decide, by decide⟩
  let region := FactorRegion.ofRoot common polynomial one frame.input.nonzero factorization coprime 0 (some localOne)
  have sourceInside : current.box.Refines endpoint.track.initial.box := by
    rewrite [endpoint.initial_box, Unit.Frame.robustChamberFrame_owner_box, sameIndex]
    change robust.source.val.box.Refines _
    rewrite [robust.source.property]
    exact Power.Unit.Source.Refinement.unitRobustSourceState_refinesBox nonzero unit degree degreeTwo index
  have nested : region.current.box.Refines endpoint.track.initial.box := by
    rewrite [region.current_eq, common.stateAt_eq]
    exact (state_refines_of_le (track.atState current) (Nat.zero_le region.index)).trans sourceInside
  let endpointCommon := region.compare_of_eq
    (Unit.Frame.robustChamberFrame_polynomial nonzero unit degree degreeTwo).symm
    (Progressive.Chamber.Frame.ChamberFrame.input _) endpoint.certificate (.inl ⟨nested⟩)
  exact isolatedCommon.trans (endpoint.certificate.named_equivalent common endpointCommon).symm

/-- Retain every original occurrence of the unit-power path using its actual cached owners and selected index.

The first occurrence is the original same-index Rouché transport, the second
uses the retained original finite target assignment, and the third uses the
original same-polynomial robust rebase. All three original overlaps and both
intermediate occurrences are preserved by the numerical owner trace.
-/
@[expose] def owners {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (moved : Owner.Local.Preparation.Prepared
      ((Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner
        (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)))
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (selected : (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).Index)
    (selected_eq : selected = Unit.Rebase.Matching.unitRebaseMap sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index))
    (robust : Owner.Local.Preparation.Prepared
      ((Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).owner
        (Fin.cast (Unit.Frame.Overlap.isolationRobustCountEq (nonzero_of_normSq_eq_one targetUnit)
          targetUnit degree degreeTwo) selected))) :
    Trace.Owners (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index :=
  let path := Unit.Move.Path.Preparation.fromFrame sourceUnit targetUnit degree degreeTwo small targetFrame
  let targetIndex : targetFrame.frame.Index :=
    Fin.cast (congrArg ChamberFrame.degree targetFrame.frame_eq.symm) selected
  let targetOwner : Owner.Local.Preparation.Prepared (targetFrame.frame.owner targetIndex) :=
    ⟨targetFrame.frame.owner targetIndex, rfl⟩
  let retained : Trace.Owners path.val index :=
    .cons (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)
      (Data.Fin.Bijection.cast_forward
        (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index).symm moved
      (.cons targetIndex (by
        rcases targetFrame with ⟨frame, same, _, _, _, _, _, _⟩
        cases same
        exact selected_eq) targetOwner
        (.cons (Fin.cast (Unit.Frame.Overlap.isolationRobustCountEq (nonzero_of_normSq_eq_one targetUnit)
          targetUnit degree degreeTwo) selected) (by
          rcases targetFrame with ⟨frame, same, _, _, _, _, _, _⟩
          cases same
          apply Fin.ext
          rfl) robust (.nil _ _)))
  retained.castPath path.property

/-- Build the numerical trace of the original complete unit move from all three exact retained owner occurrences. -/
@[expose] def fromOwners {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (original : Root (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo) index)
    (moved : Owner.Local.Preparation.Prepared
      ((Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner
        (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)))
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (selected : (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).Index)
    (selected_eq : selected = Unit.Rebase.Matching.unitRebaseMap sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index))
    (robust : Owner.Local.Preparation.Prepared
      ((Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).owner
        (Fin.cast (Unit.Frame.Overlap.isolationRobustCountEq (nonzero_of_normSq_eq_one targetUnit)
          targetUnit degree degreeTwo) selected))) :
    Trace (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original :=
  Trace.ofPreparedOwners original (owners sourceUnit targetUnit degree degreeTwo small index moved
    targetFrame selected selected_eq robust)

/-- Exact retained owners and matching give the complete original deterministic three-overlap numerical trace. -/
theorem fromOwners_eq {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (original : Root (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo) index)
    (moved : Owner.Local.Preparation.Prepared
      ((Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner
        (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)))
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (selected : (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).Index)
    (selected_eq : selected = Unit.Rebase.Matching.unitRebaseMap sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index))
    (robust : Owner.Local.Preparation.Prepared
      ((Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).owner
        (Fin.cast (Unit.Frame.Overlap.isolationRobustCountEq (nonzero_of_normSq_eq_one targetUnit)
          targetUnit degree degreeTwo) selected))) :
    fromOwners sourceUnit targetUnit degree degreeTwo small index original moved targetFrame
      selected selected_eq robust =
      Trace.build (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original :=
  Trace.ofPreparedOwners_eq original _

/-- Retain all three actual numerical owner occurrences on the assignment-based path.

The moved, independently isolated target and robust target owners are supplied
caches. The middle step reads the assignment's retained selected index and
actual bridge; no canonical refinement or owner selection is rerun.
-/
@[expose] def ownersFromAssignment
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (moved : Owner.Local.Preparation.Prepared
      ((Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner
        (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)))
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (assignment : Unit.Rebase.Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index))
    (targetOwner : Owner.Local.Preparation.Prepared
      (targetFrame.frame.owner (Fin.cast (congrArg ChamberFrame.degree targetFrame.frame_eq.symm)
        assignment.selected)))
    (robust : Owner.Local.Preparation.Prepared
      ((Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).owner
        (Fin.cast (Unit.Frame.Overlap.isolationRobustCountEq (nonzero_of_normSq_eq_one targetUnit)
          targetUnit degree degreeTwo) assignment.selected))) :
    Trace.Owners (Unit.Move.Path.Preparation.fromAssignment sourceUnit targetUnit degree degreeTwo small index
      targetFrame assignment) index :=
  let targetIndex : targetFrame.frame.Index :=
    Fin.cast (congrArg ChamberFrame.degree targetFrame.frame_eq.symm) assignment.selected
  .cons (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)
    (Data.Fin.Bijection.cast_forward
      (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index).symm moved
    (.cons targetIndex (by
      rcases targetFrame with ⟨frame, same, _, _, _, _, _, _⟩
      cases same
      exact (Unit.Rebase.Overlap.Preparation.overlapFromAssignment_forward assignment).symm) targetOwner
      (.cons (Fin.cast (Unit.Frame.Overlap.isolationRobustCountEq (nonzero_of_normSq_eq_one targetUnit)
        targetUnit degree degreeTwo) assignment.selected) (by
        rcases targetFrame with ⟨frame, same, _, _, _, _, _, _⟩
        cases same
        apply Fin.ext
        rfl) robust (.nil _ _)))

/-- Build a numerical trace on the actual assignment path from its three retained owner caches.

The source root remains the original root. Each occurrence consumes its
supplied cache through the generic prepared-owner constructor, preserving
the new middle bridge rather than asserting canonical-path equality.
-/
@[expose] def fromAssignment
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (original : Root (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo) index)
    (moved : Owner.Local.Preparation.Prepared
      ((Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner
        (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)))
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (assignment : Unit.Rebase.Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index))
    (targetOwner : Owner.Local.Preparation.Prepared
      (targetFrame.frame.owner (Fin.cast (congrArg ChamberFrame.degree targetFrame.frame_eq.symm)
        assignment.selected)))
    (robust : Owner.Local.Preparation.Prepared
      ((Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).owner
        (Fin.cast (Unit.Frame.Overlap.isolationRobustCountEq (nonzero_of_normSq_eq_one targetUnit)
          targetUnit degree degreeTwo) assignment.selected))) :
    Trace (Unit.Move.Path.Preparation.fromAssignment sourceUnit targetUnit degree degreeTwo small index
      targetFrame assignment) index original :=
  Trace.ofPreparedOwners original (ownersFromAssignment sourceUnit targetUnit degree degreeTwo small
    index moved targetFrame assignment targetOwner robust)

/-- Retained owner caches give the deterministic numerical trace on this same actual path. -/
theorem fromAssignment_eq
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (original : Root (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo) index)
    (moved : Owner.Local.Preparation.Prepared
      ((Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner
        (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index)))
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (assignment : Unit.Rebase.Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index))
    (targetOwner : Owner.Local.Preparation.Prepared
      (targetFrame.frame.owner (Fin.cast (congrArg ChamberFrame.degree targetFrame.frame_eq.symm)
        assignment.selected)))
    (robust : Owner.Local.Preparation.Prepared
      ((Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).owner
        (Fin.cast (Unit.Frame.Overlap.isolationRobustCountEq (nonzero_of_normSq_eq_one targetUnit)
          targetUnit degree degreeTwo) assignment.selected))) :
    fromAssignment sourceUnit targetUnit degree degreeTwo small index original moved targetFrame
      assignment targetOwner robust =
      Trace.build (Unit.Move.Path.Preparation.fromAssignment sourceUnit targetUnit degree degreeTwo small index
      targetFrame assignment) index original :=
  Trace.ofPreparedOwners_eq original _

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Power

end
