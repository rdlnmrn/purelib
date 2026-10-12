module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
public import Purelib.RootIsolation.Power.EqualNorm.Transport.Track
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Power.Isolation.Track
import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget
public import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget (GlobalMoveSmall)

open Purelib.Data

open Purelib

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

open Purelib.Data.Gaussian

/-- The independently computed power-polynomial isolation is supported on its coefficient-derived global square. -/
theorem isolationResult_support
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Power.Isolation.isolationResult parameterNonzero degree degreeAtLeastTwo).boxes.isolation.support =
      Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        degree)
        := rfl
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

open Purelib.Data.Gaussian

/-! ## Same-polynomial rebasing at the target vertex -/

/-- The source owner index represented by one index of the intermediate
target frame, normalized to `Fin d`. -/
def transportedSourceDegreeIndex
    {source : Canonical} (sourceNonzero : source ≠ 0)
    (target : Canonical) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    Fin degree.value :=
  Fin.cast (Progressive.Power.Frame.Basic.chamberFrame_degree sourceNonzero degree degreeAtLeastTwo)
    (Progressive.Power.EqualNorm.Move.Frame.moveSourceIndex sourceNonzero target degree degreeAtLeastTwo index)
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

open Purelib.Data.Gaussian

/-- The globally supported transported track corresponding to an owner of
the intermediate target frame. -/
def transportedFrameTrack
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : Gaussian.Norm.Basic.normSq source = Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    Track.Basic.WindingOneTrack (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
  Power.EqualNorm.Transport.Track.transportedIsolatedTrack sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small
      (transportedSourceDegreeIndex sourceNonzero target degree
        degreeAtLeastTwo index)
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

open Purelib.Data.Gaussian

/-- The transported track's initial box refines its exact owner in the intermediate target frame. -/
theorem transportedFrameTrack_initial_refines
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : Gaussian.Norm.Basic.normSq source = Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).initial.box.Refines
      ((Progressive.Power.EqualNorm.Move.Frame.transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall).owner index).box := by
  let sourceIndex :=
    Progressive.Power.EqualNorm.Move.Frame.moveSourceIndex sourceNonzero target degree degreeAtLeastTwo index
  have sourceBox := Power.Isolation.Track.isolatedTrack_initial_box_eq_chamber_owner
    sourceNonzero degree degreeAtLeastTwo sourceIndex
  have transportedBox := Progressive.Power.EqualNorm.Move.Frame.transportedFrame_owner_box sourceNonzero
    targetNonzero degree degreeAtLeastTwo small.toMoveSmall sourceIndex
  have targetIndex :
      Fin.cast (Progressive.Power.EqualNorm.Move.Frame.moveCountEq sourceNonzero target degree degreeAtLeastTwo)
          sourceIndex = index := by
    apply Fin.ext
    rfl
  have transportedBoxAtIndex :
      ((Progressive.Power.EqualNorm.Move.Frame.transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall).owner index).box =
        ((Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).owner
          sourceIndex).box := by
    rw [← targetIndex]
    exact transportedBox
  calc
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
        degreeAtLeastTwo small index).initial.box.Refines
        (Power.Isolation.Track.isolatedTrack sourceNonzero degree degreeAtLeastTwo
          (Fin.cast
            (Progressive.Power.Frame.Basic.chamberFrame_degree sourceNonzero degree degreeAtLeastTwo)
            sourceIndex)).initial.box := by
      exact Power.EqualNorm.Transport.Track.transportedIsolatedTrack_initial_refines sourceNonzero targetNonzero
        equalNorm degree degreeAtLeastTwo small _
    _ = ((Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).owner
          sourceIndex).box := sourceBox
    _ = ((Progressive.Power.EqualNorm.Move.Frame.transportedFrame sourceNonzero targetNonzero degree
          degreeAtLeastTwo small.toMoveSmall).owner index).box :=
      transportedBoxAtIndex.symm
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

open Purelib.Data.Gaussian

/-- The transported track's initial box lies in the independently computed target isolation's support. -/
theorem transportedFrameTrack_supported
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : Gaussian.Norm.Basic.normSq source = Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).initial.box.Refines
      (Power.Isolation.isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.support := by
  rw [isolationResult_support]
  exact (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small index).initial.refinesAmbient
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

open Purelib.Data.Gaussian

/-- Distinct transported-frame tracks have pairwise separated initial boxes. -/
theorem transportedFrameTracks_pairwise
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : Gaussian.Norm.Basic.normSq source = Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (left right : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree)
    (different : left ≠ right) :
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small left).initial.box.Separated
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small right).initial.box := by
  exact ((Progressive.Power.EqualNorm.Move.Frame.transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
    small.toMoveSmall).pairwiseSeparated left right different).of_refines
      (transportedFrameTrack_initial_refines sourceNonzero targetNonzero
        equalNorm degree degreeAtLeastTwo small left)
      (transportedFrameTrack_initial_refines sourceNonzero targetNonzero
        equalNorm degree degreeAtLeastTwo small right)
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track

end
