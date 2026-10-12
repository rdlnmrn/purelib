module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
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
public import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget
import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame
import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track
public import Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
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
open Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget (GlobalMoveSmall)

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

open Purelib.Data.Gaussian

/-- The common refined target-polynomial state used as the actual bridge
box between the transported frame and the independent target isolation. -/
def rebaseRefinedState
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    State.WindingOne.Basic.WindingOneState (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
  let output :=
    (Power.Isolation.isolationResult targetNonzero degree degreeAtLeastTwo).boxes.isolation
  let track := Progressive.Power.EqualNorm.Move.Track.transportedFrameTrack sourceNonzero targetNonzero equalNorm
    degree degreeAtLeastTwo small index
  track.refine track.initial
    (Exact.Ownership.Radius.assignmentRadius (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree))
        output)
    (Exact.Ownership.Radius.assignmentRadius_pos
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree))
        output)
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

open Purelib.Data.Gaussian

/-- Same-polynomial bridge on the common refined owner box. -/
def rebaseBridge
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    OwnerBridge
      (Progressive.Power.EqualNorm.Move.Frame.transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall).polynomial
      (Progressive.Power.Frame.Basic.chamberFrame targetNonzero degree degreeAtLeastTwo).polynomial := by
  let state := rebaseRefinedState sourceNonzero targetNonzero equalNorm
    degree
    degreeAtLeastTwo small index
  let owner : Owner.Local.Basic.LocalOwner
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree) :=
    { box := state.box
      proper := state.proper
      clearance := state.clearance
      rawWindingFour := state.rawWindingFour }
  exact (OwnerBridge.reflexive owner).cast
    (Progressive.Power.EqualNorm.Move.Frame.transportedFrame_polynomial sourceNonzero targetNonzero degree
      degreeAtLeastTwo small.toMoveSmall).symm
    (Progressive.Power.Frame.Basic.chamberFrame_polynomial targetNonzero degree degreeAtLeastTwo).symm
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

open Purelib.Data.Gaussian

/-- The overlap bridge keeps exactly the common refined target-polynomial state box. -/
@[simp] theorem rebaseBridge_box
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (rebaseBridge sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).box =
      (rebaseRefinedState sourceNonzero targetNonzero equalNorm degree
        degreeAtLeastTwo small index).box := by
  rw [rebaseBridge]
  rw [OwnerBridge.cast_box]
  rfl
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

open Purelib.Data.Gaussian

/-- The common bridge box refines its retained owner in the transported frame. -/
theorem rebaseBridge_refines_transported
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (rebaseBridge sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo
      small index).box.Refines
      ((Progressive.Power.EqualNorm.Move.Frame.transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall).owner index).box := by
  rw [rebaseBridge_box]
  exact ((Progressive.Power.EqualNorm.Move.Track.transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small index).nested _ _ _).trans
      (Progressive.Power.EqualNorm.Move.Track.transportedFrameTrack_initial_refines sourceNonzero targetNonzero
        equalNorm degree degreeAtLeastTwo small index)
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

open Purelib.Data.Gaussian

/-- The selected target-isolation box equals the independent chamber owner box at the retained rebase-map index. -/
theorem selectedTargetBox_eq_rebaseMap_owner
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    ((Power.Isolation.isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks.get
      (Progressive.Power.EqualNorm.Rebase.Matching.transportedOwnerSelection sourceNonzero targetNonzero equalNorm
        degree
        degreeAtLeastTwo small index).owner).initial.box =
      ((Progressive.Power.Frame.Basic.chamberFrame targetNonzero degree degreeAtLeastTwo).owner
        (Progressive.Power.EqualNorm.Rebase.Matching.rebaseMap sourceNonzero targetNonzero equalNorm degree
          degreeAtLeastTwo small index)).box := by
  exact Progressive.Power.EqualNorm.Rebase.Matching.targetTrack_get_box_eq_chamber_owner targetNonzero degree
    degreeAtLeastTwo _
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

open Purelib.Data.Gaussian

/-- The common bridge box refines the target chamber owner selected by the original matching. -/
theorem rebaseBridge_refines_target
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (rebaseBridge sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo
      small index).box.Refines
      ((Progressive.Power.Frame.Basic.chamberFrame targetNonzero degree degreeAtLeastTwo).owner
        ((Progressive.Power.EqualNorm.Rebase.Matching.rebaseMatching sourceNonzero targetNonzero equalNorm degree
          degreeAtLeastTwo small).forward index)).box := by
  have strict :=
    (Progressive.Power.EqualNorm.Rebase.Matching.transportedOwnerSelection sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).strict
  have refined := (Geometry.Rational.Box.Refinement.StrictInterior.refines strict)
  rw [rebaseBridge_box,
    Progressive.Power.EqualNorm.Rebase.Matching.rebaseMatching_forward]
  rw [← selectedTargetBox_eq_rebaseMap_owner sourceNonzero targetNonzero
    equalNorm degree degreeAtLeastTwo small index]
  exact refined
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

open Purelib.Data.Gaussian

/-- Complete same-polynomial overlap which rebases the moved owners to the
independently computed target frame. -/
def rebaseOverlap
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    Progressive.Chamber.Overlap.ChamberOverlap
      (Progressive.Power.EqualNorm.Move.Frame.transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall)
      (Progressive.Power.Frame.Basic.chamberFrame targetNonzero degree degreeAtLeastTwo) where
  matching := Progressive.Power.EqualNorm.Rebase.Matching.rebaseMatching sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small
  bridge := rebaseBridge sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small
  bridge_refines_left := rebaseBridge_refines_transported sourceNonzero
    targetNonzero equalNorm degree degreeAtLeastTwo small
  bridge_refines_right := rebaseBridge_refines_target sourceNonzero
    targetNonzero equalNorm degree degreeAtLeastTwo small
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap

end
