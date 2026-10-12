module

import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Bridge.Rouche
import Purelib.RootIsolation.Owner.Bridge.Transport
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Progressive.Chamber.Overlap
public import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget
import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame
public import Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Overlap
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
import Purelib.RootIsolation.Progressive.Power.Owner.Transport
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget (GlobalMoveSmall)

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Path

open Purelib.Data.Gaussian

/-! ## One complete small chamber move -/

/-- Construct the original forward Rouché bridge on the indexed source owner box.

Transport its polynomial identities to the source and intermediate target chamber frames while retaining the same box.
-/
def moveBridge
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : (Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).Index) :
    OwnerBridge
      (Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).polynomial
      (Progressive.Power.EqualNorm.Move.Frame.transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall).polynomial := by
  let owner := Owner.Local.Transport.castOwner
    (Progressive.Power.Frame.Basic.chamberFrame_polynomial sourceNonzero degree degreeAtLeastTwo)
    ((Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).owner index)
  let raw := OwnerBridge.ofForward owner
    (Progressive.Power.Owner.Transport.ownerMoveRouche (target := target) degree owner (by
      dsimp only [owner]
      rw [Owner.Local.Transport.castOwner_clearance_bound]
      exact small.toMoveSmall index))
  exact raw.cast
    (Progressive.Power.Frame.Basic.chamberFrame_polynomial sourceNonzero degree degreeAtLeastTwo).symm
    (Progressive.Power.EqualNorm.Move.Frame.transportedFrame_polynomial sourceNonzero targetNonzero degree
      degreeAtLeastTwo small.toMoveSmall).symm
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Path

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Path

open Purelib.Data.Gaussian

/-- The forward move bridge retains exactly the corresponding source chamber owner box. -/
@[simp] theorem moveBridge_box
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : (Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).Index) :
    (moveBridge sourceNonzero targetNonzero degree degreeAtLeastTwo small
      index).box =
      ((Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).owner index).box := by
  rw [moveBridge, OwnerBridge.cast_box]
  change
    (Owner.Local.Transport.castOwner
      (Progressive.Power.Frame.Basic.chamberFrame_polynomial sourceNonzero degree degreeAtLeastTwo)
      ((Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).owner index)).box =
    ((Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).owner index).box
  exact Owner.Local.Transport.castOwner_box _ _
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Path

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Path

open Purelib.Data.Gaussian

/-- Build the chamber overlap from the original same-label matching and forward Rouché bridges. -/
def moveOverlap
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    Progressive.Chamber.Overlap.ChamberOverlap
      (Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo)
      (Progressive.Power.EqualNorm.Move.Frame.transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall) where
  matching := Data.Fin.Bijection.cast
    (Progressive.Power.EqualNorm.Move.Frame.moveCountEq sourceNonzero target degree degreeAtLeastTwo)
  bridge := moveBridge sourceNonzero targetNonzero degree degreeAtLeastTwo small
  bridge_refines_left := by
    intro index
    rw [moveBridge_box]
    exact Box.refines_refl _
  bridge_refines_right := by
    intro index
    rw [moveBridge_box,
      Data.Fin.Bijection.cast_forward]
    rw [Progressive.Power.EqualNorm.Move.Frame.transportedFrame_owner_box]
    exact Box.refines_refl _
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Path

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Path

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- A complete finite chamber step: first carry the old boxes by Rouché,
then rebase through a refined common target-polynomial box. -/
def smallMovePath
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    Progressive.Chamber.Path.Basic.ChamberPath
      (Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo)
      (Progressive.Power.Frame.Basic.chamberFrame targetNonzero degree degreeAtLeastTwo) :=
  .cons (moveOverlap sourceNonzero targetNonzero degree degreeAtLeastTwo small)
    (.cons (Progressive.Power.EqualNorm.Rebase.Overlap.rebaseOverlap sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small)
      (.nil (Progressive.Power.Frame.Basic.chamberFrame targetNonzero degree degreeAtLeastTwo)))
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Path

end
