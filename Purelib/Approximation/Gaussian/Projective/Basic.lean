module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Expression.Basic

open Purelib.Approximation

section
@[expose] public section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

namespace Purelib.Approximation.Gaussian.Projective.Basic

set_option genInjectivity false in
/-- A rational-function value represented projectively by its two actual CCL Horner processes. The denominator may
approach or equal zero. -/
structure Pair where
  /-- The certified Gaussian expression retained as the projective numerator. -/ numerator :
    Approximation.Gaussian.Expression
  /-- The certified Gaussian expression retained as the projective denominator, without any nonzero assumption. -/
    denominator : Approximation.Gaussian.Expression

constructive_injectivity Pair

end Purelib.Approximation.Gaussian.Projective.Basic

end
