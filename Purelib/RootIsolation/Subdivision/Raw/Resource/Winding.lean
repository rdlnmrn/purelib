module

import Purelib.Data.Nat.List.Maximum
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Winding.Box.Resource
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.Subdivision.Raw.Grid.Elimination
public import Purelib.RootIsolation.Subdivision.Raw.Iteration
import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Algebra.GroupWithZero.Nat
import Purelib.Polynomial.Clearance.Box.Refinement.Contracting
import Purelib.RootIsolation.Subdivision.Raw.Grid

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.State.Raw (RawWindingState)

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Subdivision.Raw.Resource.Winding

/-- Read the four original child boxes whose winding values are inspected in one safe subdivision round. -/
def roundBoxes {p :
  CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) : List Box :=
  let grid := Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state
  [grid.lowerLeft.box, grid.upperLeft.box,
    grid.lowerRight.box, grid.upperRight.box]
end Purelib.RootIsolation.Subdivision.Raw.Resource.Winding

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Subdivision.Raw.Resource.Winding

/-- Collect the original four-child winding boxes inspected throughout a fixed number of raw refinement rounds. -/
def refinementWindingBoxes
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient)
    (depth : Nat) : List Box :=
  (List.range depth).flatMap fun round =>
    roundBoxes elimination (Subdivision.Raw.Iteration.refineN elimination round state)
end Purelib.RootIsolation.Subdivision.Raw.Resource.Winding

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Subdivision.Raw.Resource.Winding

/-- Take the maximum winding arithmetic magnitude budget over the original finite refinement-box list. -/
def refinementWindingMagnitudeBudget
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient)
    (depth : Nat) : Nat :=
  Data.Nat.List.Maximum.listMaximum ((refinementWindingBoxes elimination state
    depth).map
    (Winding.Box.Resource.boxWindingMagnitudeBudget p))
end Purelib.RootIsolation.Subdivision.Raw.Resource.Winding

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Subdivision.Raw.Resource.Winding

/-- Sum the winding field-operation budgets of all original boxes inspected by the fixed-depth refinement. -/
def refinementWindingStepBudget
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient)
    (depth : Nat) : Nat :=
  ((refinementWindingBoxes elimination state depth).map
    (Winding.Box.Resource.boxWindingFieldOperationBudget p)).sum
end Purelib.RootIsolation.Subdivision.Raw.Resource.Winding

end
