module

import Test.NumberTheory.Approximation.Unreserved

/-!
# Execute the joint unreserved sharpness regression

The compiled runner observes the actual reserve and later extension while
the original regression module retains their kernel-checked certificates.
-/

/-- Execute the reserve-extension readbacks and fail if any retained constraint is violated. -/
public def main : IO Unit := Test.NumberTheory.Approximation.Unreserved.run
