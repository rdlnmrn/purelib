module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.Polynomial.Power.Gaussian.Squarefree
import all Purelib.RootIsolation.Isolation.Owner.Region.Uniqueness

import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Power.Isolation.Track
import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.RootIsolation.Power.Unit.Source
import Purelib.RootIsolation.Power.Unit.Source.Refinement
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
import Purelib.RootIsolation.Progressive.Power.Unit.Frame
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame
import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching
public import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.Nat.Positive (RootDegree)
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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- Transport the source frame index to its original power-degree index. -/
def unitMoveSourceDegreeIndexFromFrame
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (_targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) : Fin degree.value :=
  Fin.cast (Progressive.Power.Unit.Frame.robustChamberFrame_degree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
    sourceUnit)
    sourceUnit degree degreeAtLeastTwo) index
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- Degree-normalized target owner reached by the same-polynomial rebase in
one small unit move. -/
def unitMoveTargetDegreeIndex
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) : Fin degree.value :=
  Fin.cast
    (Progressive.Power.Frame.Basic.chamberFrame_degree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit)
      degree
      degreeAtLeastTwo)
    ((Progressive.Power.Unit.Rebase.Matching.unitRebaseMatching sourceUnit targetUnit degree degreeAtLeastTwo
      small).forward
      index)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- Index of a source robust owner in the intermediate target-parameter
frame of one small move. -/
def unitMoveTransportedIndex
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree :=
  Fin.cast (Progressive.Power.Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeAtLeastTwo) index
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- Read the original isolated root state retained by the unit-move overlap bridge. -/
def unitMoveBridgeState
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :=
  Progressive.Power.Unit.Rebase.Overlap.unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
    (unitMoveTransportedIndex sourceUnit targetUnit degree degreeAtLeastTwo
      index)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- The original unit-move bridge state refines its source robust owner. -/
theorem unitMoveBridgeState_refines_sourceOwner
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (unitMoveBridgeState sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.Refines
      ((Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit
        degree degreeAtLeastTwo).owner index).box := by
  have refined := Progressive.Power.Unit.Rebase.Overlap.unitRebaseBridge_refines_transported sourceUnit targetUnit
    degree degreeAtLeastTwo small
    (unitMoveTransportedIndex sourceUnit targetUnit degree degreeAtLeastTwo
      index)
  rw [Progressive.Power.Unit.Rebase.Overlap.unitRebaseBridge_box] at refined
  rw [← Progressive.Power.Unit.Move.Frame.unitTransportedFrame_owner_box sourceUnit targetUnit degree
    degreeAtLeastTwo small index]
  exact refined
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- Read the original target power-degree index selected by the retained move and rebase matchings. -/
def unitMoveTargetDegreeIndexFromSource
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) : Fin degree.value :=
  unitMoveTargetDegreeIndex sourceUnit targetUnit degree degreeAtLeastTwo small
    (unitMoveTransportedIndex sourceUnit targetUnit degree degreeAtLeastTwo
      index)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- Independently isolated target state containing both halves of the robust
rebase. -/
def unitRebaseTargetRegion
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    State.WindingOne.Basic.WindingOneState (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
  (Power.Isolation.Track.isolatedTrack (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
    degreeAtLeastTwo
    (unitMoveTargetDegreeIndex sourceUnit targetUnit degree degreeAtLeastTwo
      small index)).initial
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- The refined transported state lies in its exact assigned original target owner region. -/
theorem unitRebaseRefinedState_refines_targetRegion
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (Progressive.Power.Unit.Rebase.Overlap.unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.Refines
      (unitRebaseTargetRegion sourceUnit targetUnit degree degreeAtLeastTwo
        small index).box := by
  let targetIndex :=
    (Progressive.Power.Unit.Rebase.Matching.unitRebaseMatching sourceUnit targetUnit degree degreeAtLeastTwo
      small).forward
      index
  have regionBox :
      (unitRebaseTargetRegion sourceUnit targetUnit degree degreeAtLeastTwo
        small index).box =
      ((Progressive.Power.Frame.Basic.chamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).owner targetIndex).box := by
    exact Power.Isolation.Track.isolatedTrack_initial_box_eq_chamber_owner
      (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree degreeAtLeastTwo targetIndex
  rw [regionBox]
  have refined := Progressive.Power.Unit.Rebase.Overlap.unitRebaseBridge_refines_target sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  rw [Progressive.Power.Unit.Rebase.Overlap.unitRebaseBridge_box] at refined
  exact refined
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- Source state from which the target robust Newton square was constructed. -/
def unitRebaseTargetSource
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    State.WindingOne.Basic.WindingOneState (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
  Power.Unit.Source.unitRobustSourceState (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) targetUnit degree
    degreeAtLeastTwo
    (unitMoveTargetDegreeIndex sourceUnit targetUnit degree degreeAtLeastTwo
      small index)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

/-- Explicit rational point shared by the rebase bridge and the source state
of its target robust owner. -/
def unitRebaseRobustOverlapPoint
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) : Gaussian :=
  Box.overlapPoint
    (Progressive.Power.Unit.Rebase.Overlap.unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box
    (unitRebaseTargetSource sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

/-- Choose the explicit rational overlap point retained by the original source and assigned target boxes. -/
def unitMoveOverlapPoint
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) : Gaussian :=
  unitRebaseRobustOverlapPoint sourceUnit targetUnit degree degreeAtLeastTwo
    small (unitMoveTransportedIndex sourceUnit targetUnit degree
      degreeAtLeastTwo index)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- The selected target Newton source lies in its original target owner region. -/
theorem unitRebaseTargetSource_refines_targetRegion
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (unitRebaseTargetSource sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.Refines
      (unitRebaseTargetRegion sourceUnit targetUnit degree degreeAtLeastTwo
        small index).box :=
  Power.Unit.Source.Refinement.unitRobustSourceState_refinesInitial
    (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeAtLeastTwo
    (unitMoveTargetDegreeIndex sourceUnit targetUnit degree degreeAtLeastTwo
      small index)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- The two explicitly computed rebase states overlap inside their common
independently isolated target owner. -/
theorem unitRebaseStates_not_separated
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    ¬(Progressive.Power.Unit.Rebase.Overlap.unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box.Separated
      (unitRebaseTargetSource sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box := by
  exact Isolation.Owner.Region.Uniqueness.windingOneStates_not_separated_in_region
    (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degreeAtLeastTwo)
    (Power.Gaussian.Squarefree.squarefree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree)
    (Power.Isolation.isolationInput (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).elimination
    (unitRebaseTargetRegion sourceUnit targetUnit degree degreeAtLeastTwo small
      index)
    (Progressive.Power.Unit.Rebase.Overlap.unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
      index)
    (unitRebaseTargetSource sourceUnit targetUnit degree degreeAtLeastTwo small
      index)
    (unitRebaseRefinedState_refines_targetRegion sourceUnit targetUnit degree
      degreeAtLeastTwo small index)
    (unitRebaseTargetSource_refines_targetRegion sourceUnit targetUnit degree
      degreeAtLeastTwo small index)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- The explicit rebase overlap point lies strictly inside both original retained robust boxes. -/
theorem unitRebaseRobustOverlapPoint_inside
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (Progressive.Power.Unit.Rebase.Overlap.unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box.Contains
        (unitRebaseRobustOverlapPoint sourceUnit targetUnit degree
          degreeAtLeastTwo small index) ∧
      (unitRebaseTargetSource sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box.Contains
        (unitRebaseRobustOverlapPoint sourceUnit targetUnit degree
          degreeAtLeastTwo small index) :=
  Box.contains_overlapPoint_of_not_separated
    (unitRebaseStates_not_separated sourceUnit targetUnit degree
      degreeAtLeastTwo small index)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- The retained move overlap point lies strictly inside its original source owner box. -/
theorem unitMoveOverlapPoint_inside_sourceOwner
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    ((Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit
      degree degreeAtLeastTwo).owner index).box.Contains
      (unitMoveOverlapPoint sourceUnit targetUnit degree degreeAtLeastTwo small
        index) := by
  exact (unitMoveBridgeState_refines_sourceOwner sourceUnit targetUnit degree
    degreeAtLeastTwo small index).contains
      (unitRebaseRobustOverlapPoint_inside sourceUnit targetUnit degree
        degreeAtLeastTwo small
        (unitMoveTransportedIndex sourceUnit targetUnit degree degreeAtLeastTwo
          index)).1
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

open Purelib.Data.Gaussian

/-- The retained move overlap point lies strictly inside its assigned target robust box. -/
theorem unitMoveOverlapPoint_inside_targetRobustBox
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) targetUnit degree
      degreeAtLeastTwo
      (unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
        degreeAtLeastTwo small index)).Contains
      (unitMoveOverlapPoint sourceUnit targetUnit degree degreeAtLeastTwo small
        index) := by
  let transported := unitMoveTransportedIndex sourceUnit targetUnit degree
    degreeAtLeastTwo index
  have overlapInside := (unitRebaseRobustOverlapPoint_inside sourceUnit
    targetUnit degree degreeAtLeastTwo small transported).2
  exact (Power.Unit.Source.Refinement.unitRobustSourceState_refinesBox
    (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeAtLeastTwo
    (unitMoveTargetDegreeIndex sourceUnit targetUnit degree degreeAtLeastTwo
      small transported)).contains overlapInside
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry

end
