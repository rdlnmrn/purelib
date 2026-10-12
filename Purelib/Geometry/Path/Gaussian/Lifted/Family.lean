module

public import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Path.Gaussian.Lifted

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

namespace Purelib.Geometry.Path.Gaussian.Lifted.Family

set_option genInjectivity false in
/-- The `2g` common sheet-aware cycle refinements corresponding to a symplectic homology basis. -/
structure PairedCycleRefinements (sheets genus : Nat) where
  /-- The first indexed family of retained cycle refinements. -/ aCycle : Fin genus -> Refinement.LiftedCycleRefinement
    sheets
  /-- The second indexed family of retained cycle refinements. -/ bCycle : Fin genus -> Refinement.LiftedCycleRefinement
    sheets

constructive_injectivity PairedCycleRefinements

end Purelib.Geometry.Path.Gaussian.Lifted.Family

end
