module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.Newton.Band.Build
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Power.Bounds
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Power.Isolation.Track
public import Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget
public import Purelib.RootIsolation.Progressive.Power.Owner.Transport
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Progressive.Power.EqualNorm.Move.Budget (GlobalMoveSmall)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

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

namespace Purelib.RootIsolation.Power.EqualNorm.Transport.Track

open Purelib.Data.Gaussian

/-- The Rouché-moved local owner, regarded as a raw target-polynomial state
inside the common equal-norm global square. -/
def transportedRawState
    {source target : Canonical}
    (sourceNonzero : source ≠ 0)
    (equalNorm : Data.Gaussian.Norm.Basic.normSq source = Data.Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    State.Raw.RawWindingState (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
        by
  let sourceState :=
    (Power.Isolation.Track.isolatedTrack sourceNonzero degree degreeAtLeastTwo index).initial
  let sourceOwner : Owner.Local.Basic.LocalOwner
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree) :=
    { box := sourceState.box
      proper := sourceState.proper
      clearance := sourceState.clearance
      rawWindingFour := sourceState.rawWindingFour }
  let targetOwner := Progressive.Power.Owner.Transport.transportedOwner degree sourceOwner (small.boundary index)
  exact
    { box := sourceState.box
      refinesAmbient := by
        rw [← Power.Bounds.largeSquareBox_polynomial_eq_of_normSq_eq equalNorm degree]
        exact sourceState.refinesAmbient
      proper := targetOwner.proper
      clearance := targetOwner.clearance
      rawWinding_ne := by
        intro zero
        have fourZero : (4 : Int) = 0 := by
          rw [← targetOwner.rawWindingFour]
          exact zero
        exact (by decide : (4 : Int) ≠ 0) fourZero }
end Purelib.RootIsolation.Power.EqualNorm.Transport.Track

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

namespace Purelib.RootIsolation.Power.EqualNorm.Transport.Track

open Purelib.Data.Gaussian

/-- One target-polynomial Newton-band extraction inside the moved owner. -/
def transportedExtraction
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : Data.Gaussian.Norm.Basic.normSq source = Data.Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :=
  Newton.Band.Build.extract
    (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degreeAtLeastTwo)
    (Power.Gaussian.Squarefree.squarefree targetNonzero degree)
    (Power.Isolation.isolationInput targetNonzero degree degreeAtLeastTwo).elimination
    (transportedRawState sourceNonzero equalNorm degree degreeAtLeastTwo small
      index) (epsilon := (1 : Fraction.Rational)) (by decide)
end Purelib.RootIsolation.Power.EqualNorm.Transport.Track

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

namespace Purelib.RootIsolation.Power.EqualNorm.Transport.Track

open Purelib.Data.Gaussian

/-- Move one source owner by Rouché, then run one target-polynomial
Newton-band extraction inside it.  The extraction computes four fresh safe
full lines in the common equal-norm ambient square, so no ambient-line
clearance has to survive the coefficient move. -/
def transportedIsolatedState
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : Data.Gaussian.Norm.Basic.normSq source = Data.Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    State.WindingOne.Basic.WindingOneState (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
        by
  let extracted := transportedExtraction sourceNonzero targetNonzero equalNorm
    degree degreeAtLeastTwo small index
  exact
    { box := extracted.box
      refinesAmbient := extracted.refinesAmbient
      proper := extracted.proper
      clearance := extracted.clearance
      rawWindingFour := extracted.rawWindingFour
      ambientLeftClearance := extracted.ambientLeftClearance
      ambientRightClearance := extracted.ambientRightClearance
      ambientBottomClearance := extracted.ambientBottomClearance
      ambientTopClearance := extracted.ambientTopClearance }
end Purelib.RootIsolation.Power.EqualNorm.Transport.Track

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

namespace Purelib.RootIsolation.Power.EqualNorm.Transport.Track

open Purelib.Data.Gaussian

/-- The target squarefree extraction program started from a transported
global state. -/
def transportedIsolatedTrack
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : Data.Gaussian.Norm.Basic.normSq source = Data.Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    Track.Basic.WindingOneTrack (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree)) :=
  Track.Newton.Build.ofInitial
    (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degreeAtLeastTwo)
    (Power.Gaussian.Squarefree.squarefree targetNonzero degree)
    (Power.Isolation.isolationInput targetNonzero degree degreeAtLeastTwo).elimination
    (transportedIsolatedState sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index)
end Purelib.RootIsolation.Power.EqualNorm.Transport.Track

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

namespace Purelib.RootIsolation.Power.EqualNorm.Transport.Track

open Purelib.Data.Gaussian

/-- The transported raw state retains exactly the source isolated track's initial box. -/
@[simp] theorem transportedRawState_box
    {source target : Canonical}
    (sourceNonzero : source ≠ 0)
    (equalNorm : Data.Gaussian.Norm.Basic.normSq source = Data.Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    (transportedRawState sourceNonzero equalNorm degree degreeAtLeastTwo small
      index).box =
      (Power.Isolation.Track.isolatedTrack sourceNonzero degree degreeAtLeastTwo
        index).initial.box := rfl
end Purelib.RootIsolation.Power.EqualNorm.Transport.Track

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

namespace Purelib.RootIsolation.Power.EqualNorm.Transport.Track

open Purelib.Data.Gaussian

/-- The target-polynomial extracted state refines the corresponding original source owner box. -/
theorem transportedIsolatedState_refines
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : Data.Gaussian.Norm.Basic.normSq source = Data.Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    (transportedIsolatedState sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).box.Refines
      (Power.Isolation.Track.isolatedTrack sourceNonzero degree degreeAtLeastTwo
        index).initial.box := by
  change (transportedExtraction sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small index).box.Refines _
  rw [← transportedRawState_box sourceNonzero equalNorm degree
    degreeAtLeastTwo small index]
  exact Geometry.Rational.Box.Refinement.StrictInterior.refines
    (transportedExtraction sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).strictCurrent
end Purelib.RootIsolation.Power.EqualNorm.Transport.Track

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

namespace Purelib.RootIsolation.Power.EqualNorm.Transport.Track

open Purelib.Data.Gaussian

/-- The transported target track starts in a box refining the corresponding original source owner box. -/
theorem transportedIsolatedTrack_initial_refines
    {source target : Canonical}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : Data.Gaussian.Norm.Basic.normSq source = Data.Gaussian.Norm.Basic.normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    (transportedIsolatedTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).initial.box.Refines
      (Power.Isolation.Track.isolatedTrack sourceNonzero degree degreeAtLeastTwo
        index).initial.box :=
  transportedIsolatedState_refines sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small index
end Purelib.RootIsolation.Power.EqualNorm.Transport.Track

end
