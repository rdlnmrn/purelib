module

public import Purelib.Approximation.Gaussian.Exponential.E
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Examples.Approximation.Gaussian.Exponential.E

open Purelib.Approximation.Gaussian.Exponential

/-- Compare the two e names from distinct starting stages at squared tolerance one. -/
@[expose] public def comparison :=
  E.factorial_equivalent_horner.compare 3 7 1 (by decide)

end Purelib.Examples.Approximation.Gaussian.Exponential.E
