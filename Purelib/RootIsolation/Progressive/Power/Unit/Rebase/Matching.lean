module

import Purelib.Data.Fin.Bijection.Basic
public import Purelib.Data.Fin.Bijection.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.RootIsolation.Exact.Ownership.Injective
import Purelib.RootIsolation.Exact.Ownership.Prepare
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Owner.Family.FTA
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Track
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib

open Purelib.Data

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

open Purelib.Data.Gaussian

/-- The independently constructed target tracks have the same retained count as the target robust chamber. -/
theorem unitTargetTrackCountEq
    {target : Canonical} (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks.length =
      (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree := by
  calc
    (Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks.length =
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree).natDegree :=
      (Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks_length
    _ = degree.value := Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree target degree
    _ = (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree :=
      (Power.Gaussian.Progressive.Coefficients.coefficientTable_degree target degree).symm
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

open Purelib.Data.Gaussian

/-- The indexed independent target track retains exactly the corresponding robust chamber owner box. -/
@[simp] theorem unitTargetTrack_get_box_eq_chamber_owner
    {target : Canonical} (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin
      (Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks.length) :
    ((Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks.get index).initial.box =
      ((Progressive.Power.Frame.Basic.chamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).owner
        (Fin.cast (unitTargetTrackCountEq targetUnit degree degreeAtLeastTwo)
          index)).box := by
  simp [-eq_self, -iff_self, Progressive.Power.Frame.Basic.chamberFrame, Progressive.Chamber.Frame.ChamberFrame.owner,
    Owner.Family.Basic.OwnerFamily.ofResult,
    FTA.Squarefree.AdapterResult.trackAt, Exact.Basic.Output.trackAt,
    Exact.Basic.Output.trackIndex]
  rfl
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

open Purelib.Data.Gaussian

/-- Select target owners for the original transported tracks using their retained refinement witnesses. -/
@[expose] def unitTransportedOwnerSelection
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    Exact.Ownership.Basic.OwnerSelection
      (Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation
      (Progressive.Power.Unit.Move.Track.unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
        small index) :=
  (Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
    degreeAtLeastTwo).boxes.ownership
      (Progressive.Power.Unit.Move.Track.unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
        small index)
      (Progressive.Power.Unit.Move.Track.unitTransportedFrameTrack_supported sourceUnit targetUnit degree
        degreeAtLeastTwo small index)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

open Purelib.Data.Gaussian

/-- Read the original finite owner-assignment map from transported tracks to independent target owners. -/
@[expose] def unitRebaseMap
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree →
      Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree := fun index =>
  Fin.cast (unitTargetTrackCountEq targetUnit degree degreeAtLeastTwo)
    (unitTransportedOwnerSelection sourceUnit targetUnit degree degreeAtLeastTwo
      small index).owner
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

open Purelib.Data.Gaussian

/-- The original transported-to-target owner assignment is injective. -/
theorem unitRebaseMap_injective
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    Function.Injective
      (unitRebaseMap sourceUnit targetUnit degree degreeAtLeastTwo small) := by
  let output :=
    (Power.Isolation.isolationResult (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).boxes.isolation
  let family : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree →
      Track.Basic.WindingOneTrack (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
          degree))
          :=
    fun index => Progressive.Power.Unit.Move.Track.unitTransportedFrameTrack sourceUnit targetUnit degree
      degreeAtLeastTwo small index
  have rawInjective : Function.Injective (fun index =>
      (unitTransportedOwnerSelection sourceUnit targetUnit degree
        degreeAtLeastTwo small index).owner) := by
    change Function.Injective (fun index =>
      (Exact.Ownership.Prepare.selectOutputOwner
        (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degreeAtLeastTwo)
        (Power.Gaussian.Squarefree.squarefree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree)
        (Power.Isolation.isolationInput (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
          degreeAtLeastTwo).elimination output (family index)
        (Progressive.Power.Unit.Move.Track.unitTransportedFrameTrack_supported sourceUnit targetUnit degree
          degreeAtLeastTwo small index)).owner)
    exact Exact.Ownership.Injective.selectedOwner_injective
      (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degreeAtLeastTwo)
      (Power.Gaussian.Squarefree.squarefree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree)
      (Power.Isolation.isolationInput (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).elimination output family
      (Progressive.Power.Unit.Move.Track.unitTransportedFrameTrack_supported sourceUnit targetUnit degree
        degreeAtLeastTwo small)
      (Progressive.Power.Unit.Move.Track.unitTransportedFrameTracks_pairwise sourceUnit targetUnit degree
        degreeAtLeastTwo small)
  intro left right equal
  apply rawInjective
  apply Fin.ext
  simpa only [-eq_self, -iff_self, unitRebaseMap, Fin.val_cast] using
    congrArg (fun index => index.val) equal
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

open Purelib.Data.Gaussian

/-- Construct the finite bijective matching from the original injective owner assignment. -/
@[expose] def unitRebaseMatching
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    Data.Fin.Bijection
      (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree
      (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree :=
  Data.Fin.Bijection.ofInjectiveEndomap
    (unitRebaseMap sourceUnit targetUnit degree degreeAtLeastTwo small)
    (unitRebaseMap_injective sourceUnit targetUnit degree degreeAtLeastTwo small)
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

open Purelib.Data.Gaussian

/-- The rebase matching's forward map is exactly the original retained owner-assignment map. -/
@[simp] theorem unitRebaseMatching_forward
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (unitRebaseMatching sourceUnit targetUnit degree degreeAtLeastTwo
      small).forward
        index =
      unitRebaseMap sourceUnit targetUnit degree degreeAtLeastTwo small index :=
  rfl
end Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching

end
