module

import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Owner.Bridge.Basic
public import Purelib.RootIsolation.Owner.Bridge.Transport
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Power.Isolation.Track
import Purelib.RootIsolation.Power.Unit.Source
import Purelib.RootIsolation.Power.Unit.Source.Refinement
public import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
public import Purelib.RootIsolation.Progressive.Power.Unit.Frame
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap

open Purelib.Data.Gaussian

/-- Construct the common isolated root state connecting the original isolation owner to its robust Newton refinement. -/
def isolationRobustBridge
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).Index) :
    OwnerBridge
      (Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).polynomial
      (Progressive.Power.Unit.Frame.robustChamberFrame parameterNonzero parameterUnit degree
        degreeAtLeastTwo).polynomial := by
  let degreeIndex : Fin degree.value := Fin.cast
    (Progressive.Power.Frame.Basic.chamberFrame_degree parameterNonzero degree degreeAtLeastTwo) index
  let state := Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo degreeIndex
  let owner : Owner.Local.Basic.LocalOwner
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) :=
    { box := state.box
      proper := state.proper
      clearance := state.clearance
      rawWindingFour := state.rawWindingFour }
  exact (OwnerBridge.reflexive owner).cast
    (Progressive.Power.Frame.Basic.chamberFrame_polynomial parameterNonzero degree degreeAtLeastTwo).symm
    (Progressive.Power.Unit.Frame.robustChamberFrame_polynomial parameterNonzero parameterUnit degree
      degreeAtLeastTwo).symm
end Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap

open Purelib.Data.Gaussian

/-- The isolation-to-robust bridge retains the computed robust box exactly. -/
@[simp] theorem isolationRobustBridge_box
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).Index) :
    (isolationRobustBridge parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box =
      (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
        degreeAtLeastTwo
        (Fin.cast
          (Progressive.Power.Frame.Basic.chamberFrame_degree parameterNonzero degree degreeAtLeastTwo)
          index)).box := by
  unfold isolationRobustBridge
  rw [OwnerBridge.cast_box]
  rfl
end Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap

open Purelib.Data.Gaussian

/-! ## Canonical same-polynomial rebase to the robust frame -/

/-- The original isolated frame and its robust refinement have the same retained power degree. -/
theorem isolationRobustCountEq
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).degree =
      (Progressive.Power.Unit.Frame.robustChamberFrame parameterNonzero parameterUnit degree
        degreeAtLeastTwo).degree := by
  rw [Progressive.Power.Frame.Basic.chamberFrame_degree, Progressive.Power.Unit.Frame.robustChamberFrame_degree]
end Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap

open Purelib.Data.Gaussian

/-- The independently isolated frame and the robust frame have a canonical
identity-labelled overlap through the source state used by the Newton step. -/
def isolationRobustOverlap
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Progressive.Chamber.Overlap.ChamberOverlap
      (Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo)
      (Progressive.Power.Unit.Frame.robustChamberFrame parameterNonzero parameterUnit degree
        degreeAtLeastTwo) where
  matching := Data.Fin.Bijection.cast
    (isolationRobustCountEq parameterNonzero parameterUnit degree
      degreeAtLeastTwo)
  bridge := isolationRobustBridge parameterNonzero parameterUnit degree
    degreeAtLeastTwo
  bridge_refines_left := by
    intro index
    rw [isolationRobustBridge_box]
    let degreeIndex : Fin degree.value := Fin.cast
      (Progressive.Power.Frame.Basic.chamberFrame_degree parameterNonzero degree degreeAtLeastTwo) index
    calc
      (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo degreeIndex).box.Refines
          (Purelib.RootIsolation.Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo
            degreeIndex).initial.box :=
        Purelib.RootIsolation.Power.Unit.Source.Refinement.unitRobustSourceState_refinesInitial parameterNonzero
          parameterUnit
          degree degreeAtLeastTwo degreeIndex
      _ = ((Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).owner
          index).box :=
        Purelib.RootIsolation.Power.Isolation.Track.isolatedTrack_initial_box_eq_chamber_owner parameterNonzero degree
          degreeAtLeastTwo index
  bridge_refines_right := by
    intro index
    rw [isolationRobustBridge_box,
      Data.Fin.Bijection.cast_forward,
      Progressive.Power.Unit.Frame.robustChamberFrame_owner_box]
    exact Purelib.RootIsolation.Power.Unit.Source.Refinement.unitRobustSourceState_refinesBox parameterNonzero
      parameterUnit degree
      degreeAtLeastTwo _
end Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap

end
