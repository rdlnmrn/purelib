module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Exact endpoints of retained affine spatial coordinates

The cached displacement determines the original start and finish at unit
parameters zero and one, including stationary coordinates.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Coordinate

open Purelib.Data.Gaussian.Basic (Canonical)

/-- The original affine coordinate at zero is its exact retained starting endpoint. -/
theorem point_zero {start finish : Canonical} (coordinate : Coordinate start finish) :
    coordinate.point 0 = start := by
  rewrite [coordinate.point_eq]
  change start + 0 * (finish - start) = start
  ring1

/-- The original affine coordinate at one is its exact retained finishing endpoint. -/
theorem point_one {start finish : Canonical} (coordinate : Coordinate start finish) :
    coordinate.point 1 = finish := by
  rewrite [coordinate.point_eq]
  change start + 1 * (finish - start) = finish
  ring1

end Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Coordinate

end
