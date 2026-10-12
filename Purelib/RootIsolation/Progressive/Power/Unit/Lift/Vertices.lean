module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.RootIsolation.Progressive.Power.Unit.Frame
public import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Geometry.Rational

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

open Purelib.Data.Gaussian

/-- The original move bridge anchor lies strictly inside its source robust box. -/
theorem unitMoveBridgeAnchor_inside_sourceRobustBox
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
      degreeAtLeastTwo
      (Progressive.Power.Unit.Rebase.Geometry.unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit degree
        degreeAtLeastTwo index)).Contains
      (Progressive.Power.Unit.Rebase.Geometry.unitMoveBridgeState sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box.anchor := by
  have inside := (Progressive.Power.Unit.Rebase.Geometry.unitMoveBridgeState_refines_sourceOwner sourceUnit targetUnit
    degree degreeAtLeastTwo small index).contains
      (Progressive.Power.Unit.Rebase.Geometry.unitMoveBridgeState sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box.contains_anchor
  rw [Progressive.Power.Unit.Frame.robustChamberFrame_owner_box] at inside
  exact inside
end Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

/-- Read the exact source robust owner anchor used as the lifted move's base point. -/
def unitMoveLiftBase
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (_targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) : Gaussian :=
  ((Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
    sourceUnit degree
    degreeAtLeastTwo).owner index).box.anchor
end Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

open Purelib.Data.Gaussian

/-- The lifted move's retained base anchor lies strictly inside its source robust box. -/
theorem unitMoveLiftBase_inside_sourceRobustBox
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
      degreeAtLeastTwo
      (Progressive.Power.Unit.Rebase.Geometry.unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit degree
        degreeAtLeastTwo index)).Contains
      (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index) := by
  unfold unitMoveLiftBase
    Progressive.Power.Unit.Rebase.Geometry.unitMoveSourceDegreeIndexFromFrame
  rw [Progressive.Power.Unit.Frame.robustChamberFrame_owner_box]
  exact Box.contains_anchor _
end Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

/-- List the original bridge anchor, overlap point and target anchor in lifted path order. -/
def unitMoveLiftVertices
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) : List Gaussian :=
  [(Progressive.Power.Unit.Rebase.Geometry.unitMoveBridgeState sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.anchor,
    Progressive.Power.Unit.Rebase.Geometry.unitMoveOverlapPoint sourceUnit targetUnit degree degreeAtLeastTwo small
      index,
    (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) targetUnit degree
      degreeAtLeastTwo
      (Progressive.Power.Unit.Rebase.Geometry.unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
        degreeAtLeastTwo small index)).anchor]
end Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

open Purelib.Data.Gaussian

/-- The retained overlap point lies strictly inside the source robust box used by the lifted move. -/
theorem unitMoveOverlapPoint_inside_sourceRobustBox
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
      degreeAtLeastTwo
      (Progressive.Power.Unit.Rebase.Geometry.unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit degree
        degreeAtLeastTwo index)).Contains
      (Progressive.Power.Unit.Rebase.Geometry.unitMoveOverlapPoint sourceUnit targetUnit degree degreeAtLeastTwo small
        index) := by
  have inside := Progressive.Power.Unit.Rebase.Geometry.unitMoveOverlapPoint_inside_sourceOwner sourceUnit targetUnit
    degree degreeAtLeastTwo small index
  rw [Progressive.Power.Unit.Frame.robustChamberFrame_owner_box] at inside
  exact inside
end Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

/-- List the three retained target-parameter vertices paired with the lifted move edges. -/
def unitMoveParameterVertices (target :
  Gaussian.Basic.Canonical) : List Gaussian :=
  [target, target, target]
end Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

open Purelib.Data.Gaussian

/-- The retained target anchor lies strictly inside its assigned target robust box. -/
theorem unitMoveTargetAnchor_inside_targetRobustBox
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) targetUnit degree
      degreeAtLeastTwo
      (Progressive.Power.Unit.Rebase.Geometry.unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
        degreeAtLeastTwo small index)).Contains
      (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) targetUnit degree
        degreeAtLeastTwo
        (Progressive.Power.Unit.Rebase.Geometry.unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
          degreeAtLeastTwo small index)).anchor :=
  Box.contains_anchor _
end Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices

end
