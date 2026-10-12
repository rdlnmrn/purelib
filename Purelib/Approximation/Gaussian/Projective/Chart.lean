module
import Purelib.Approximation.Gaussian.Expression.Basic
import Purelib.Approximation.Gaussian.Name.Apart
public import Purelib.Approximation.Gaussian.Projective.Basic
import Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Name.Basic

section
@[expose] public section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

namespace Purelib.Approximation.Gaussian.Projective.Basic.Pair
section ProjectiveEvaluation

/-- Enter the ordinary affine chart only from finite denominator apartness. -/
def affine (evaluation : Gaussian.Projective.Basic.Pair)
    (apart : Named.Apart
      evaluation.denominator.output.name) : Approximation.Gaussian.Expression :=
  Approximation.Gaussian.Expression.div
    evaluation.numerator evaluation.denominator apart

/-- Enter the reciprocal affine chart around a pole only from finite numerator apartness. A pole is represented there by
an output near zero, rather than by constructing an affine infinity. -/
def reciprocalAffine (evaluation :
  Gaussian.Projective.Basic.Pair)
    (apart : Named.Apart
      evaluation.numerator.output.name) : Approximation.Gaussian.Expression :=
  Approximation.Gaussian.Expression.div
    evaluation.denominator evaluation.numerator apart
end ProjectiveEvaluation

end Purelib.Approximation.Gaussian.Projective.Basic.Pair

end
