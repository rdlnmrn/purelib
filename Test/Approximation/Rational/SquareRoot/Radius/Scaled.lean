module
public import Purelib.Approximation.Rational.SquareRoot.Radius.Scaled

public section

namespace Test.Approximation.Rational.SquareRoot.Radius.Scaled

open Purelib.Approximation.Rational.SquareRoot.Radius.Scaled (radius)
/-- Three exact scaled-radius computations for large, unit and small targets.

Kernel evaluation checks the displayed dyadic outputs at 4096, 1/4096 and 1, including the strict undershoot at the
smaller scales. -/
theorem scale_regressions :
    radius 4096 = 32 ∧
      radius (1 / 4096) = 1 / 128 ∧
      radius 1 = 1 / 2 := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Test.Approximation.Rational.SquareRoot.Radius.Scaled

end
