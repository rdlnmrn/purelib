module

import Purelib.Data.Fin.Bijection.Basic
public import Purelib.Data.Fin.Bijection.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
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
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget
public import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Track
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget (GlobalMoveSmall)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib

open Purelib.Data

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

open Purelib.Data.Gaussian

/-- The target isolation's raw list length equals the displayed chamber
degree. -/
theorem targetTrackCountEq
    {target : Canonical} (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Power.Isolation.isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks.length =
      (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree := by
  calc
    (Power.Isolation.isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks.length =
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree).natDegree :=
      (Power.Isolation.isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks_length
    _ = degree.value := Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree target degree
    _ = (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree :=
      (Power.Gaussian.Progressive.Coefficients.coefficientTable_degree target degree).symm
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

open Purelib.Data.Gaussian

/-- The selected original target-isolation track starts in exactly the corresponding target chamber owner box. -/
@[simp] theorem
  targetTrack_get_box_eq_chamber_owner
    {target : Canonical} (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin
      (Power.Isolation.isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks.length) :
    ((Power.Isolation.isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks.get index).initial.box =
      ((Progressive.Power.Frame.Basic.chamberFrame targetNonzero degree degreeAtLeastTwo).owner
        (Fin.cast (targetTrackCountEq targetNonzero degree degreeAtLeastTwo)
          index)).box := by
  simp [-eq_self, -iff_self, Progressive.Power.Frame.Basic.chamberFrame,
    Progressive.Chamber.Frame.ChamberFrame.owner,
    Owner.Family.Basic.OwnerFamily.ofResult,
    FTA.Squarefree.AdapterResult.trackAt,
    Exact.Basic.Output.trackAt,
    Exact.Basic.Output.trackIndex]
  rfl
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

open Purelib.Data.Gaussian

/-- Deterministic target-isolation ownership of a transported source track. -/
def transportedOwnerSelection
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    Exact.Ownership.Basic.OwnerSelection
      (Power.Isolation.isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation
      (Progressive.Power.EqualNorm.Move.Track.transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
        degreeAtLeastTwo small index) :=
  (Power.Isolation.isolationResult targetNonzero degree degreeAtLeastTwo).boxes.ownership
    (Progressive.Power.EqualNorm.Move.Track.transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index)
    (Progressive.Power.EqualNorm.Move.Track.transportedFrameTrack_supported sourceNonzero targetNonzero equalNorm
      degree degreeAtLeastTwo small index)
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

open Purelib.Data.Gaussian

/-- The finite owner map from transported-frame indices to independently
isolated target-frame indices. -/
def rebaseMap
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree →
      Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree := fun index =>
  Fin.cast (targetTrackCountEq targetNonzero degree degreeAtLeastTwo)
    (transportedOwnerSelection sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).owner
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

open Purelib.Data.Gaussian

/-- Distinct transported tracks select distinct owners in the independent target isolation. -/
theorem rebaseMap_injective
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    Function.Injective (rebaseMap sourceNonzero targetNonzero equalNorm
      degree
      degreeAtLeastTwo small) := by
  let output :=
    (Power.Isolation.isolationResult targetNonzero degree degreeAtLeastTwo).boxes.isolation
  let family : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree →
      Track.Basic.WindingOneTrack (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
          degree))
          :=
    fun index => Progressive.Power.EqualNorm.Move.Track.transportedFrameTrack sourceNonzero targetNonzero equalNorm
      degree degreeAtLeastTwo small index
  have rawInjective : Function.Injective (fun index =>
      (transportedOwnerSelection sourceNonzero targetNonzero equalNorm
        degree
        degreeAtLeastTwo small index).owner) := by
    change Function.Injective (fun index =>
      (Exact.Ownership.Prepare.selectOutputOwner
        (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degreeAtLeastTwo)
        (Power.Gaussian.Squarefree.squarefree targetNonzero degree)
        (Power.Isolation.isolationInput targetNonzero degree degreeAtLeastTwo).elimination
        output (family index)
        (Progressive.Power.EqualNorm.Move.Track.transportedFrameTrack_supported sourceNonzero targetNonzero equalNorm
          degree degreeAtLeastTwo small index)).owner)
    exact Exact.Ownership.Injective.selectedOwner_injective
      (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degreeAtLeastTwo)
      (Power.Gaussian.Squarefree.squarefree targetNonzero degree)
      (Power.Isolation.isolationInput targetNonzero degree degreeAtLeastTwo).elimination
      output family
      (Progressive.Power.EqualNorm.Move.Track.transportedFrameTrack_supported sourceNonzero targetNonzero equalNorm
        degree degreeAtLeastTwo small)
      (Progressive.Power.EqualNorm.Move.Track.transportedFrameTracks_pairwise sourceNonzero targetNonzero equalNorm
        degree degreeAtLeastTwo small)
  intro left right equal
  apply rawInjective
  apply Fin.ext
  simpa only [rebaseMap, Fin.val_cast] using
    congrArg (fun index => index.val) equal
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

open Purelib.Data.Gaussian

/-- Build the finite bijection from transported labels to independent target labels using the retained injective owner
map. -/
def rebaseMatching
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    Data.Fin.Bijection
      (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree
      (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree :=
  Data.Fin.Bijection.ofInjectiveEndomap
    (rebaseMap sourceNonzero targetNonzero equalNorm degree degreeAtLeastTwo
      small)
    (rebaseMap_injective sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small)
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

open Purelib.Data.Gaussian

/-- The matching's forward function is exactly the original retained owner-selection map. -/
@[simp] theorem rebaseMatching_forward
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree) :
    (rebaseMatching sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small).forward index =
      rebaseMap sourceNonzero targetNonzero equalNorm degree
        degreeAtLeastTwo
        small index := rfl
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Rebase.Matching

end
