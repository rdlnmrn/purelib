module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.Newton.Band.Build
import Purelib.RootIsolation.Power.Bounds
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Power.Owner.Transport
import Purelib.RootIsolation.Progressive.Power.Unit.Frame
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame
import Purelib.RootIsolation.Progressive.Power.Unit.Owner
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.Owner.Local.Basic
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Budget

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- Source robust-frame index normalized to `Fin d` for the numerical
transport program. -/
def unitMoveSourceDegreeIndex
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) : Fin degree.value :=
  Fin.cast
    (Progressive.Power.Unit.Frame.robustChamberFrame_degree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit
      degree degreeAtLeastTwo)
    (Progressive.Power.Unit.Move.Frame.unitMoveSourceIndex sourceUnit targetUnit degree degreeAtLeastTwo index)
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- The moved robust owner as a raw target-polynomial state in the common
unit-parameter global square. -/
def unitTransportedRawState
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    State.Raw.RawWindingState (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
        by
  let sourceOwner := Progressive.Power.Unit.Owner.unitRobustOwner (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
    sourceUnit)
    sourceUnit degree degreeAtLeastTwo index
  let targetOwner := Progressive.Power.Owner.Transport.transportedOwner degree sourceOwner (small.owner index)
  exact
    { box := sourceOwner.box
      refinesAmbient := by
        rw [← Power.Bounds.largeSquareBox_polynomial_eq_of_normSq_eq
          (sourceUnit.trans targetUnit.symm) degree]
        exact Power.Unit.Box.unitRobustBox_refinesAmbient
          (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
          degreeAtLeastTwo index
      proper := targetOwner.proper
      clearance := targetOwner.clearance
      rawWinding_ne := by
        intro zero
        have fourZero : (4 : Int) = 0 := by
          rw [← targetOwner.rawWindingFour]
          exact zero
        exact (by decide : (4 : Int) ≠ 0) fourZero }
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- Extract the retained transported root state with the fixed positive extraction tolerance one. -/
def unitTransportedExtraction
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :=
  Newton.Band.Build.extract
    (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degreeAtLeastTwo)
    (Power.Gaussian.Squarefree.squarefree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree)
    (Power.Isolation.isolationInput (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).elimination
    (unitTransportedRawState sourceUnit targetUnit degree degreeAtLeastTwo
      small index) (epsilon := (1 : Fraction.Rational)) (by decide)
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- Read the exact isolated state of the transported extraction. -/
def unitTransportedIsolatedState
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    State.WindingOne.Basic.WindingOneState (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
        by
  let extracted := unitTransportedExtraction sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  exact
    { box := extracted.box
      refinesAmbient := extracted.refinesAmbient
      proper := extracted.proper
      clearance := extracted.clearance
      rawWindingFour := extracted.rawWindingFour
      ambientLeftClearance := extracted.ambientLeftClearance
      ambientRightClearance := extracted.ambientRightClearance
      ambientBottomClearance := extracted.ambientBottomClearance
      ambientTopClearance := extracted.ambientTopClearance }
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- Start the transported isolated track with its original four boundary-clearance certificates. -/
def unitTransportedIsolatedTrack
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    Track.Basic.WindingOneTrack (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
  Track.Newton.Build.ofInitial
    (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degreeAtLeastTwo)
    (Power.Gaussian.Squarefree.squarefree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree)
    (Power.Isolation.isolationInput (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).elimination
    (unitTransportedIsolatedState sourceUnit targetUnit degree degreeAtLeastTwo
      small index)
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- Globally supported transported track corresponding to one intermediate
frame index. -/
def unitTransportedFrameTrack
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    Track.Basic.WindingOneTrack (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
  unitTransportedIsolatedTrack sourceUnit targetUnit degree degreeAtLeastTwo
    small (unitMoveSourceDegreeIndex sourceUnit targetUnit degree
      degreeAtLeastTwo index)
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- Every transported chamber track remains supported in its exact original owner box. -/
theorem unitTransportedFrameTrack_supported
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
      small index).initial.box.Refines
      (Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.support := by
  change (unitTransportedFrameTrack sourceUnit targetUnit degree
    degreeAtLeastTwo small index).initial.box.Refines
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree))
  exact (unitTransportedFrameTrack sourceUnit targetUnit degree
    degreeAtLeastTwo small index).initial.refinesAmbient
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- The transported raw state retains exactly the source robust box. -/
@[simp] theorem unitTransportedRawState_box
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    (unitTransportedRawState sourceUnit targetUnit degree degreeAtLeastTwo
      small index).box =
      Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
        degreeAtLeastTwo index := rfl
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- The extracted transported state refines its original same-box raw state. -/
theorem unitTransportedIsolatedState_refines
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    (unitTransportedIsolatedState sourceUnit targetUnit degree degreeAtLeastTwo
      small index).box.Refines
        (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
          degreeAtLeastTwo index) := by
  change (unitTransportedExtraction sourceUnit targetUnit degree
    degreeAtLeastTwo small index).box.Refines _
  rw [← unitTransportedRawState_box sourceUnit targetUnit degree
    degreeAtLeastTwo small index]
  exact Geometry.Rational.Box.Refinement.StrictInterior.refines
      (unitTransportedExtraction
    sourceUnit targetUnit degree
    degreeAtLeastTwo small index).strictCurrent
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- The initial transported chamber track state refines its original raw root state. -/
theorem unitTransportedFrameTrack_initial_refines
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
      small index).initial.box.Refines
      ((Progressive.Power.Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small).owner index).box := by
  let sourceIndex := Progressive.Power.Unit.Move.Frame.unitMoveSourceIndex sourceUnit targetUnit degree
    degreeAtLeastTwo index
  let degreeIndex := unitMoveSourceDegreeIndex sourceUnit targetUnit degree
    degreeAtLeastTwo index
  have targetIndex :
      Fin.cast (Progressive.Power.Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeAtLeastTwo)
          sourceIndex = index := by
    apply Fin.ext
    rfl
  have transportedBox :
      ((Progressive.Power.Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small).owner index).box =
        ((Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
          sourceUnit
          degree degreeAtLeastTwo).owner sourceIndex).box := by
    rw [← targetIndex]
    exact Progressive.Power.Unit.Move.Frame.unitTransportedFrame_owner_box sourceUnit targetUnit degree
      degreeAtLeastTwo small sourceIndex
  have sourceRobustBox :
      ((Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit
        degree degreeAtLeastTwo).owner sourceIndex).box =
        Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
          degreeAtLeastTwo degreeIndex := by
    exact Progressive.Power.Unit.Frame.robustChamberFrame_owner_box (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo sourceIndex
  rw [transportedBox, sourceRobustBox]
  exact unitTransportedIsolatedState_refines sourceUnit targetUnit degree
    degreeAtLeastTwo small degreeIndex
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

open Purelib.Data.Gaussian

/-- Distinct transported owner tracks retain pairwise disjoint original owner boxes. -/
theorem unitTransportedFrameTracks_pairwise
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (left right : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree)
    (different : left ≠ right) :
    (unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
      small left).initial.box.Separated
      (unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
        small right).initial.box :=
  Box.Separated.of_refines
    (Progressive.Chamber.Frame.ChamberFrame.pairwiseSeparated
      (Progressive.Power.Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo small)
      left right different)
      (unitTransportedFrameTrack_initial_refines sourceUnit targetUnit degree
        degreeAtLeastTwo small left)
      (unitTransportedFrameTrack_initial_refines sourceUnit targetUnit degree
        degreeAtLeastTwo small right)
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Track

end
