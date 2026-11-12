module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Bridge.Rouche
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Family.Transport
import Purelib.RootIsolation.Owner.Local.Basic
public import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Target
public import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
public import Purelib.RootIsolation.Progressive.Power.Owner.Transport
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
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
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Rouche.Connection
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial.Power.Gaussian.Progressive

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget (MoveSmall)

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

open Purelib.Data.Gaussian

/-- The source chamber degree equals the target power-polynomial coefficient-table degree. -/
theorem moveCountEq
    {source : Canonical} (sourceNonzero : source ≠ 0)
    (target : Canonical) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).degree =
      (Coefficients.coefficientTable target degree).degree := by
  rw [Frame.Basic.chamberFrame_degree,
    Coefficients.coefficientTable_degree]
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

open Purelib.Data.Gaussian

/-- Transport the target table's finite index to the same source chamber label. -/
def moveSourceIndex
    {source : Canonical} (sourceNonzero : source ≠ 0)
    (target : Canonical) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin (Coefficients.coefficientTable target degree).degree) :
    (Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).Index :=
  Fin.cast
    (moveCountEq sourceNonzero target degree degreeAtLeastTwo).symm index
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

open Purelib.Data.Gaussian

/-- Intermediate chamber at the target parameter which deliberately keeps
the preceding owner boxes.  It is used only for the Rouché half of a move;
a subsequent same-polynomial overlap rebases to the independently isolated
target frame. -/
def transportedFrame
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : MoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    Chamber.Frame.ChamberFrame where
  reference := Coefficients.coefficientTable target degree
  chamber := by
    let sourceFrame := Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo
    let sourceIndex : Fin (Coefficients.coefficientTable target degree).degree →
        sourceFrame.Index :=
      moveSourceIndex sourceNonzero target degree degreeAtLeastTwo
    let sourceOwner :
        (index : Fin (Coefficients.coefficientTable target degree).degree) →
          Owner.Local.Basic.LocalOwner
            (Power.Gaussian.rootPolynomial source degree) := fun index =>
      Owner.Local.Transport.castOwner
        (Frame.Basic.chamberFrame_polynomial sourceNonzero degree degreeAtLeastTwo)
        (sourceFrame.owner (sourceIndex index))
    let rawOwners : Owner.Family.Basic.OwnerFamily
        (Power.Gaussian.rootPolynomial target degree)
        (Coefficients.coefficientTable target degree).degree :=
      { owner := fun index => Owner.Transport.transportedOwner degree
          (sourceOwner index) (by
            dsimp only [sourceOwner]
            rw [Owner.Local.Transport.castOwner_clearance_bound]
            exact small (sourceIndex index))
        pairwiseSeparated := by
          intro left right different
          have sourceDifferent : sourceIndex left ≠ sourceIndex right := by
            intro equal
            have valueEqual : left.val = right.val := by
              simpa only [sourceIndex, moveSourceIndex,
                Fin.val_cast] using
                congrArg (fun index => index.val) equal
            exact different (Fin.ext valueEqual)
          have separated := sourceFrame.pairwiseSeparated
            (sourceIndex left) (sourceIndex right) sourceDifferent
          have leftBox : (sourceOwner left).box =
              (sourceFrame.owner (sourceIndex left)).box := by
            exact Owner.Local.Transport.castOwner_box _ _
          have rightBox : (sourceOwner right).box =
              (sourceFrame.owner (sourceIndex right)).box := by
            exact Owner.Local.Transport.castOwner_box _ _
          simpa only [Owner.Transport.transportedOwner,
            OwnerBridge.rightOwner,
            OwnerBridge.ofForward,
            leftBox, rightBox] using separated }
    let owners : Owner.Family.Basic.OwnerFamily
        (Coefficients.coefficientTable target degree).polynomial
        (Coefficients.coefficientTable target degree).degree :=
      Owner.Family.Transport.castOwnerFamily
        (Coefficients.coefficientTable_polynomial target degree).symm rawOwners
    let squarefreeCertificate :=
      Coefficients.coefficientTableSquarefree targetNonzero degree
    exact
      { degreeAtLeastTwo := by
          rw [Coefficients.coefficientTable_degree]
          exact degreeAtLeastTwo
        squarefree := squarefreeCertificate
        owners := owners
        referenceSmall := Coefficients.coefficientTable_allowances_lt target degree
          (Chamber.Target.simpleRootChamberTarget_pos
            (Coefficients.coefficientTable target degree) squarefreeCertificate owners)
        referenceMaximality := by
          intro familyCount family pairwise
          let result : FTA.Squarefree.AdapterResult
              (Coefficients.coefficientTable target degree).polynomial := by
            rw [Coefficients.coefficientTable_polynomial]
            exact Power.Isolation.isolationResult targetNonzero degree degreeAtLeastTwo
          have bound := result.boxes.maximality family pairwise
          have tablePolynomialDegree :
              (Coefficients.coefficientTable target degree).polynomial.natDegree =
                (Power.Gaussian.rootPolynomial target degree).natDegree :=
            congrArg Dense.Basic.DensePolynomial.natDegree
              (Coefficients.coefficientTable_polynomial target degree)
          calc
            familyCount ≤
                (Coefficients.coefficientTable target degree).polynomial.natDegree := bound
            _ = (Power.Gaussian.rootPolynomial target degree).natDegree := tablePolynomialDegree
            _ = degree.value := Power.Gaussian.rootPolynomial_degree target degree
            _ = (Coefficients.coefficientTable target degree).degree :=
              (Coefficients.coefficientTable_degree target degree).symm }
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

open Purelib.Data.Gaussian

/-- The transported chamber frame retains the supplied power degree. -/
@[simp] theorem transportedFrame_degree
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : MoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    (transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
      small).degree = degree.value := by
  exact Coefficients.coefficientTable_degree target degree
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

open Purelib.Data.Gaussian

/-- The transported frame keeps exactly the corresponding original source owner box. -/
@[simp] theorem transportedFrame_owner_box
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : MoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : (Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).Index) :
    ((transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
      small).owner
        (Fin.cast
          (moveCountEq sourceNonzero target degree degreeAtLeastTwo) index)).box
            =
      ((Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).owner index).box := by
  simp only [Chamber.Frame.ChamberFrame.owner,
    transportedFrame, moveSourceIndex,
    Owner.Family.Transport.castOwnerFamily_owner_box,
    Owner.Local.Transport.castOwner_box, Owner.Transport.transportedOwner,
    OwnerBridge.rightOwner,
    OwnerBridge.ofForward]
  congr 1
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

open Purelib.Data.Gaussian

/-- The transported frame's polynomial is exactly the power polynomial at the target parameter. -/
@[simp] theorem transportedFrame_polynomial
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : MoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    (transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
      small).polynomial = Power.Gaussian.rootPolynomial target degree := by
  exact Coefficients.coefficientTable_polynomial target degree
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Frame

end
