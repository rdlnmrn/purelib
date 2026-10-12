module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Bridge.Rouche
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Family.Transport
import Purelib.RootIsolation.Owner.Local.Basic
public import Purelib.RootIsolation.Owner.Local.Transport
public import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Target
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
public import Purelib.RootIsolation.Progressive.Power.Owner.Transport
public import Purelib.RootIsolation.Progressive.Power.Unit.Frame
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Budget
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Sum
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Winding.Box.Rouche.Connection
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

open Purelib.Data.Gaussian

/-- A unit move preserves the retained power degree of its source and transported chamber frames. -/
theorem unitMoveCountEq
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (_targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree
      degreeAtLeastTwo).degree = (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree := by
  rw [Progressive.Power.Unit.Frame.robustChamberFrame_degree,
    Power.Gaussian.Progressive.Coefficients.coefficientTable_degree]
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

open Purelib.Data.Gaussian

/-- Transport the source chamber index to the original power-degree index. -/
def unitMoveSourceIndex
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree
      degreeAtLeastTwo).Index :=
  Fin.cast (unitMoveCountEq sourceUnit targetUnit degree degreeAtLeastTwo).symm
    index
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

open Purelib.Data.Gaussian

/-- Target-parameter chamber which retains the robust source boxes after the
finite Rouché comparison. -/
def unitTransportedFrame
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    Progressive.Chamber.Frame.ChamberFrame where
  reference := Power.Gaussian.Progressive.Coefficients.coefficientTable target degree
  chamber := by
    let sourceFrame := Progressive.Power.Unit.Frame.robustChamberFrame
      (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
    let sourceIndex : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree →
        sourceFrame.Index :=
      unitMoveSourceIndex sourceUnit targetUnit degree degreeAtLeastTwo
    let sourceOwner :
        (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) →
          Owner.Local.Basic.LocalOwner
            (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree) := fun index =>
      Owner.Local.Transport.castOwner
        (Progressive.Power.Unit.Frame.robustChamberFrame_polynomial
          (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
          degreeAtLeastTwo)
        (sourceFrame.owner (sourceIndex index))
    let rawOwners : Owner.Family.Basic.OwnerFamily
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree :=
      { owner := fun index => Progressive.Power.Owner.Transport.transportedOwner degree (sourceOwner index) (by
          dsimp only [sourceOwner]
          rw [Owner.Local.Transport.castOwner_clearance_bound]
          have sourceDegreeIndex : Fin degree.value := Fin.cast
            (Progressive.Power.Unit.Frame.robustChamberFrame_degree
              (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
              degreeAtLeastTwo) (sourceIndex index)
          rw [Progressive.Power.Unit.Frame.robustChamberFrame_owner_clearance_bound]
          exact small.owner sourceDegreeIndex)
        pairwiseSeparated := by
          intro left right different
          have sourceDifferent : sourceIndex left ≠ sourceIndex right := by
            intro equal
            apply different
            apply Fin.ext
            have values := congrArg (fun index => index.val) equal
            change left.val = right.val at values
            exact values
          have separated := sourceFrame.pairwiseSeparated
            (sourceIndex left) (sourceIndex right) sourceDifferent
          have leftBox : (sourceOwner left).box =
              (sourceFrame.owner (sourceIndex left)).box :=
            Owner.Local.Transport.castOwner_box _ _
          have rightBox : (sourceOwner right).box =
              (sourceFrame.owner (sourceIndex right)).box :=
            Owner.Local.Transport.castOwner_box _ _
          simpa only [Progressive.Power.Owner.Transport.transportedOwner,
            OwnerBridge.rightOwner,
            OwnerBridge.ofForward,
            leftBox, rightBox] using separated }
    let owners : Owner.Family.Basic.OwnerFamily
        (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).polynomial
        (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree :=
      Owner.Family.Transport.castOwnerFamily
        (Power.Gaussian.Progressive.Coefficients.coefficientTable_polynomial target degree).symm rawOwners
    let targetOriginal :=
      (Progressive.Power.Frame.Basic.chamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).chamber
    exact
      { degreeAtLeastTwo := targetOriginal.degreeAtLeastTwo
        squarefree := targetOriginal.squarefree
        owners := owners
        referenceSmall := Power.Gaussian.Progressive.Coefficients.coefficientTable_allowances_lt target degree
          (Progressive.Chamber.Target.simpleRootChamberTarget_pos
            (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree) targetOriginal.squarefree owners)
        referenceMaximality := targetOriginal.referenceMaximality }
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

open Purelib.Data.Gaussian

/-- The transported chamber frame retains exactly the supplied power degree. -/
@[simp] theorem unitTransportedFrame_degree
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    (unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
      small).degree = degree.value :=
  Power.Gaussian.Progressive.Coefficients.coefficientTable_degree target degree
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

open Purelib.Data.Gaussian

/-- Every transported chamber owner retains the corresponding source robust box. -/
@[simp] theorem unitTransportedFrame_owner_box
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    ((unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
      small).owner
        (Fin.cast (unitMoveCountEq sourceUnit targetUnit degree
          degreeAtLeastTwo) index)).box =
      ((Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit
        degree degreeAtLeastTwo).owner index).box := by
  simp only [Progressive.Chamber.Frame.ChamberFrame.owner, unitTransportedFrame,
    unitMoveSourceIndex, Owner.Family.Transport.castOwnerFamily_owner_box,
    Owner.Local.Transport.castOwner_box, Progressive.Power.Owner.Transport.transportedOwner,
    OwnerBridge.rightOwner,
    OwnerBridge.ofForward]
  congr 1
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

open Purelib.Data.Gaussian

/-- The transported chamber frame represents the original power polynomial at the target unit parameter. -/
@[simp] theorem unitTransportedFrame_polynomial
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    (unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
      small).polynomial = Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree :=
  Power.Gaussian.Progressive.Coefficients.coefficientTable_polynomial target degree
end Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame

end
