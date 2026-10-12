module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.RootIsolation.Exact.Ownership.Radius
import Purelib.RootIsolation.Owner.Bridge.Basic
public import Purelib.RootIsolation.Owner.Bridge.Transport
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Power.Unit.Move.Budget
public import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Track
public import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

open Purelib.Data.Gaussian

/-- Refine the original transported track at its retained owner-assignment radius. -/
def unitRebaseRefinedState
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    State.WindingOne.Basic.WindingOneState (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
  let output :=
    (Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).boxes.isolation
  let track := Progressive.Power.Unit.Move.Track.unitTransportedFrameTrack sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  track.refine track.initial
    (Exact.Ownership.Radius.assignmentRadius (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree))
        output)
    (Exact.Ownership.Radius.assignmentRadius_pos (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree))
        output)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

open Purelib.Data.Gaussian

/-- Package the refined transported state as the bridge to its assigned independent target owner. -/
def unitRebaseBridge
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    OwnerBridge
      (Progressive.Power.Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small).polynomial
      (Progressive.Power.Frame.Basic.chamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).polynomial := by
  let state := unitRebaseRefinedState sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  let owner : Owner.Local.Basic.LocalOwner
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree) :=
    { box := state.box
      proper := state.proper
      clearance := state.clearance
      rawWindingFour := state.rawWindingFour }
  exact (OwnerBridge.reflexive owner).cast
    (Progressive.Power.Unit.Move.Frame.unitTransportedFrame_polynomial sourceUnit targetUnit degree
      degreeAtLeastTwo small).symm
    (Progressive.Power.Frame.Basic.chamberFrame_polynomial (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit)
      degree
      degreeAtLeastTwo).symm
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

open Purelib.Data.Gaussian

/-- The rebase bridge retains the exact refined transported state box. -/
@[simp] theorem unitRebaseBridge_box
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (unitRebaseBridge sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box =
      (unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo
        small index).box := by
  unfold unitRebaseBridge
  rw [OwnerBridge.cast_box]
  rfl
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

open Purelib.Data.Gaussian

/-- The rebase bridge refines the original transported chamber owner. -/
theorem unitRebaseBridge_refines_transported
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (unitRebaseBridge sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.Refines
      ((Progressive.Power.Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small).owner index).box := by
  rw [unitRebaseBridge_box]
  exact ((Progressive.Power.Unit.Move.Track.unitTransportedFrameTrack sourceUnit targetUnit degree
    degreeAtLeastTwo small index).nested _ _ _).trans
      (Progressive.Power.Unit.Move.Track.unitTransportedFrameTrack_initial_refines sourceUnit targetUnit degree
        degreeAtLeastTwo small index)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

open Purelib.Data.Gaussian

/-- The selected target box equals the chamber owner selected by the original rebase map. -/
theorem unitSelectedTargetBox_eq_rebaseMap_owner
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    ((Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks.get
      (Progressive.Power.Unit.Rebase.Matching.unitTransportedOwnerSelection sourceUnit targetUnit degree
        degreeAtLeastTwo small index).owner).initial.box =
      ((Progressive.Power.Frame.Basic.chamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).owner
        (Progressive.Power.Unit.Rebase.Matching.unitRebaseMap sourceUnit targetUnit degree degreeAtLeastTwo small
          index)).box :=
  Progressive.Power.Unit.Rebase.Matching.unitTargetTrack_get_box_eq_chamber_owner targetUnit degree degreeAtLeastTwo _
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

open Purelib.Data.Gaussian

/-- The rebase bridge refines its assigned independent target owner. -/
theorem unitRebaseBridge_refines_target
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (unitRebaseBridge sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.Refines
      ((Progressive.Power.Frame.Basic.chamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).owner
        ((Progressive.Power.Unit.Rebase.Matching.unitRebaseMatching sourceUnit targetUnit degree degreeAtLeastTwo
          small).forward index)).box := by
  have refined :=
    Geometry.Rational.Box.Refinement.StrictInterior.refines
      (Progressive.Power.Unit.Rebase.Matching.unitTransportedOwnerSelection sourceUnit targetUnit degree
        degreeAtLeastTwo
        small index).strict
  rw [unitRebaseBridge_box,
    Progressive.Power.Unit.Rebase.Matching.unitRebaseMatching_forward]
  rw [← unitSelectedTargetBox_eq_rebaseMap_owner sourceUnit targetUnit degree
    degreeAtLeastTwo small index]
  exact refined
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

open Purelib.Data.Gaussian

/-- Build the rebase overlap using the retained finite matching and original refinement bridges. -/
def unitRebaseOverlap
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    Progressive.Chamber.Overlap.ChamberOverlap
      (Progressive.Power.Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo small)
      (Progressive.Power.Frame.Basic.chamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo) where
  matching := Progressive.Power.Unit.Rebase.Matching.unitRebaseMatching sourceUnit targetUnit degree degreeAtLeastTwo
    small
  bridge := unitRebaseBridge sourceUnit targetUnit degree degreeAtLeastTwo small
  bridge_refines_left := unitRebaseBridge_refines_transported sourceUnit
    targetUnit degree degreeAtLeastTwo small
  bridge_refines_right := unitRebaseBridge_refines_target sourceUnit targetUnit
    degree degreeAtLeastTwo small
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap

end
