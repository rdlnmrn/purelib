module
public import Purelib.Data.Nat.Positive

@[expose] public section

/-!
The finite degree-two input is shared below square-root sheets and their
quadratic refinement checker.  Keeping it here avoids a dependency cycle
when canonical sheets use that checker.  These are the unchanged degree
declarations, not a new root or sheet-selection convention.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootDegree

open Purelib.Data in
/-- The positive natural degree two with its executable positivity certificate. -/
def degreeTwo : Nat.Positive.RootDegree where
  value := 2
  positive := by decide

/-- The retained square-root degree has value two. -/
@[simp] theorem degreeTwo_value : degreeTwo.value = 2 := rfl

/-- The retained square-root degree satisfies the lower bound two. -/
theorem degreeTwo_atLeastTwo : 2 <= degreeTwo.value := by decide

end Purelib.Riemann.RootContinuation.SquareRootDegree
