module

public import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Init.Prelude
import Purelib.Data.Fin.Bijection.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry.Path.Gaussian

section
@[expose] public section

/-!
# Finite sheet-aware paths for period integration

A lifted path below is an inductive finite chain.  Every geometric edge
carries an explicit permutation of the labelled sheets and a proof that the
chosen endpoint sheet is the transported start sheet.  A separate inductive
relation verifies that a progressive integration model follows exactly the
same displayed geometric edges.  This separation lets several algebraic
differentials share one persistent lifted cycle while retaining their own
local polynomial integrand models.
-/

namespace Purelib.Geometry.Path.Gaussian.Lifted.Closed

set_option genInjectivity false in
/-- A closed lifted path retains its actual base point and labelled starting sheet rather than identifying endpoints
only propositionally. -/
structure ClosedLiftedPath (sheets : Nat) : Type where
  /-- The displayed geometric point and sheet at which the closed path is based. -/ basepoint : Lifted.Basic.LiftedPoint
    sheets
  /-- The finite lifted path returning to the exact retained basepoint. -/ path : Lifted.Basic.LiftedPath sheets
    basepoint basepoint

constructive_injectivity ClosedLiftedPath

namespace ClosedLiftedPath

/-- Count the cells in the retained closed lifted path. -/
def cellCount {sheets : Nat} (path :
  ClosedLiftedPath sheets) : Nat :=
  path.path.cellCount

/-- The composed sheet transport fixes the retained starting sheet. -/
theorem returns_to_startingSheet {sheets : Nat}
    (path : ClosedLiftedPath sheets) :
    path.path.sheetTransport.forward path.basepoint.sheet =
      path.basepoint.sheet :=
  path.path.sheetTransport_start

end ClosedLiftedPath
end Purelib.Geometry.Path.Gaussian.Lifted.Closed

end

section
@[expose] public section

/-!
# Operational linearity of finite period programs

This module records orientation reversal and path concatenation at the actual
finite `PeriodProgram` layer.  It also exposes the already constructive
cellular-boundary and exact-primitive cancellation theorems through one small
interface used by family transport.

The stronger `CertifiedPeriodProgram` contains local algebraic observations.
Reversing those observations requires a new parameter-reversal certificate;
it is intentionally not inferred merely from reversal of the geometric path.
-/

namespace Purelib.Geometry.Path.Gaussian.Lifted.Refinement.CycleJoin

/-- Concatenate two closed lifted paths with propositionally equal basepoints.

Transport the second basepoint along the supplied equality and retain the first basepoint as the endpoint of the joined
path. -/
public def appendClosed {sheets : Nat}
    (first second : Geometry.Path.Gaussian.Lifted.Closed.ClosedLiftedPath sheets)
    (basepoint_eq : first.basepoint = second.basepoint) :
    Geometry.Path.Gaussian.Lifted.Closed.ClosedLiftedPath sheets := by
  cases first with
  | mk firstBase firstPath =>
      cases second with
      | mk secondBase secondPath =>
          dsimp only at basepoint_eq
          subst secondBase
          exact
            { basepoint := firstBase
              path := firstPath.append secondPath }

end Purelib.Geometry.Path.Gaussian.Lifted.Refinement.CycleJoin

end
