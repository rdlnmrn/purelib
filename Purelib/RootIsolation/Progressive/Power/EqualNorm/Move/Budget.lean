module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
public import Purelib.RootIsolation.Power.Isolation.Track
import Purelib.RootIsolation.Progressive.Power.Frame.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)

open Purelib.Data

open Purelib

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget

open Purelib.Data.Gaussian

/-- The single finite clearance needed to move each isolated owner boundary.
Fresh target-polynomial ambient-line clearances are computed after the
Rouché move by the eliminant-driven Newton-band extractor. -/
structure GlobalMoveSmall
    {source : Canonical} (sourceNonzero : source ≠ 0)
    (target : Canonical) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Prop where
  /-- The squared source-to-target distance is below every original isolated owner's boundary clearance. -/ boundary : ∀
    index : Fin degree.value,
    Data.Gaussian.Norm.Basic.normSq (source - target) <
      (Power.Isolation.Track.isolatedTrack sourceNonzero degree degreeAtLeastTwo
        index).initial.clearance.bound
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget

open Purelib.Data.Gaussian

/-- A finite move is small on every currently displayed owner boundary. -/
def MoveSmall
    {source : Canonical} (sourceNonzero : source ≠ 0)
    (target : Canonical) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Prop :=
  ∀ index : (Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).Index,
    Data.Gaussian.Norm.Basic.normSq (source - target) <
      ((Progressive.Power.Frame.Basic.chamberFrame sourceNonzero degree degreeAtLeastTwo).owner
        index).clearance.bound
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget

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

namespace Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget.GlobalMoveSmall

open Purelib.Data.Gaussian

/-- The degree-normalized boundary budget is the local Rouché half-move. -/
theorem toMoveSmall
    {source : Canonical} {sourceNonzero : source ≠ 0}
    {target : Canonical} {degree : RootDegree}
    {degreeAtLeastTwo : 2 ≤ degree.value}
    (small : Progressive.Power.EqualNorm.Move.Budget.GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    Progressive.Power.EqualNorm.Move.Budget.MoveSmall sourceNonzero target degree degreeAtLeastTwo := by
  intro index
  have bound := small.boundary
    (Fin.cast
      (Progressive.Power.Frame.Basic.chamberFrame_degree sourceNonzero degree degreeAtLeastTwo) index)
  rw [Power.Isolation.Track.isolatedTrack_initial_clearance_bound_eq_chamber_owner] at bound
  exact bound
end Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget.GlobalMoveSmall

end
