module

import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
public import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.RootIsolation.Progressive.Power.Unit.Frame
public import Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap
public import Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap
import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry
import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame
import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib

open Purelib.Data

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Path

open Purelib.Data.Gaussian

/-- One complete robust move: Rouché transport, finite target ownership, and
the canonical same-polynomial rebase to the target robust frame. -/
def unitSmallMovePath
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    ChamberPath
      (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit degree
        degreeAtLeastTwo)
      (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit)
        targetUnit degree
        degreeAtLeastTwo) :=
  .cons (Progressive.Power.Unit.Move.Overlap.unitMoveOverlap sourceUnit targetUnit degree degreeAtLeastTwo small)
    (.cons (Progressive.Power.Unit.Rebase.Overlap.unitRebaseOverlap sourceUnit targetUnit degree degreeAtLeastTwo
      small)
      (.cons (Progressive.Power.Unit.Frame.Overlap.isolationRobustOverlap
        (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit)
        targetUnit degree degreeAtLeastTwo)
        (.nil (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
          targetUnit)
          targetUnit degree degreeAtLeastTwo))))
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Path

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Path

open Purelib.Data.Gaussian

/-- The final index of the three-overlap move path equals the original selected target power-degree index. -/
theorem unitSmallMovePath_finalIndex_degree
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    Fin.cast
        (Progressive.Power.Unit.Frame.robustChamberFrame_degree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
          targetUnit)
          targetUnit degree degreeAtLeastTwo)
        ((unitSmallMovePath sourceUnit targetUnit degree degreeAtLeastTwo small)
          |>.finalIndex index) =
      Progressive.Power.Unit.Rebase.Geometry.unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
        degreeAtLeastTwo small index := by
  unfold unitSmallMovePath
  simp only [ChamberPath.finalIndex_cons,
    ChamberPath.finalIndex_nil,
    Progressive.Power.Unit.Move.Overlap.unitMoveOverlap, Progressive.Power.Unit.Rebase.Overlap.unitRebaseOverlap,
      Progressive.Power.Unit.Frame.Overlap.isolationRobustOverlap,
    Data.Fin.Bijection.cast_forward]
  apply Fin.ext
  rfl
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Path

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Path

open Purelib.Data.Gaussian

/-- The retained lifted target anchor equals the exact final chamber owner anchor. -/
theorem unitMoveTargetAnchor_eq_finalOwnerAnchor
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) targetUnit degree
      degreeAtLeastTwo
      (Progressive.Power.Unit.Rebase.Geometry.unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
        degreeAtLeastTwo small index)).anchor =
      ((Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit)
        targetUnit
        degree degreeAtLeastTwo).owner
        ((unitSmallMovePath sourceUnit targetUnit degree degreeAtLeastTwo small)
          |>.finalIndex index)).box.anchor := by
  rw [Progressive.Power.Unit.Frame.robustChamberFrame_owner_box]
  rw [unitSmallMovePath_finalIndex_degree]
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Path

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Path

open Purelib.Data.Gaussian

/-- Following the retained lifted vertices terminates at the exact final chamber owner anchor. -/
theorem unitMoveLift_terminal_eq_finalOwnerAnchor
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    Polygon.Chain.terminal
        (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
        (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftVertices sourceUnit targetUnit degree degreeAtLeastTwo small
          index) =
      ((Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit)
        targetUnit
        degree degreeAtLeastTwo).owner
        ((unitSmallMovePath sourceUnit targetUnit degree degreeAtLeastTwo small)
          |>.finalIndex index)).box.anchor := by
  simp only [Progressive.Power.Unit.Lift.Vertices.unitMoveLiftVertices, Polygon.Chain.terminal]
  exact unitMoveTargetAnchor_eq_finalOwnerAnchor sourceUnit targetUnit degree
    degreeAtLeastTwo small index
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Path

end
