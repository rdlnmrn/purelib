module

public import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Init.Prelude
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry.Path.Gaussian.Lifted

open Purelib.Geometry.Path.Gaussian.Lifted.Refinement

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

namespace Purelib.Geometry.Path.Gaussian.Lifted.Refinement

set_option genInjectivity false in
/-- Persistent finite refinements of one fixed sheet-aware cycle. Every call returns a finite closed lifted path; later
calls need not reuse the same subdivision. -/
structure LiftedCycleRefinement (sheets : Nat) where
  /-- The displayed closed lifted path at each finite refinement index. -/ liftedPath : Nat -> Closed.ClosedLiftedPath
    sheets

constructive_injectivity LiftedCycleRefinement

namespace LiftedCycleRefinement

/-- Reverse every displayed finite representative of a persistent cycle. -/
def reverse {sheets : Nat} (cycle :
  LiftedCycleRefinement sheets) :
    LiftedCycleRefinement sheets where
  liftedPath := fun index =>
    { basepoint := (cycle.liftedPath index).basepoint
      path := (cycle.liftedPath index).path.reverse }

end LiftedCycleRefinement
end Purelib.Geometry.Path.Gaussian.Lifted.Refinement

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

namespace Purelib.Geometry.Path.Gaussian.Lifted.Refinement

/-! ## Concatenation -/

/-- Two persistent cycles whose displayed representatives use the same lifted basepoint at every finite refinement. -/
structure CycleJoin {sheets : Nat}
    (first second : LiftedCycleRefinement sheets) where
  /-- The two retained paths have equal lifted basepoints at every index. -/ basepoint_eq : forall index,
    (first.liftedPath index).basepoint = (second.liftedPath index).basepoint

namespace CycleJoin

/-- Concatenate the two finite closed representatives pointwise. -/
def cycle {sheets : Nat} {first second :
  LiftedCycleRefinement sheets}
    (join : CycleJoin first second) :
      LiftedCycleRefinement sheets where
  liftedPath := fun index =>
    CycleJoin.appendClosed (first.liftedPath index) (second.liftedPath index)
      (join.basepoint_eq index)

end CycleJoin
end Purelib.Geometry.Path.Gaussian.Lifted.Refinement

end
