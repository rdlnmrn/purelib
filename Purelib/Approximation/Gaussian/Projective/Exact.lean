module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Projective.Basic
import Purelib.Approximation.Gaussian.Expression.Basic
import Purelib.Approximation.Gaussian.Name.Coherent

namespace Purelib.Approximation.Gaussian.Projective.Exact

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Basic

public section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

set_option genInjectivity false in
/-- Exact rational specialization of both projective coordinates. -/
structure ExactPair
    (evaluation : Gaussian.Projective.Basic.Pair)
    (numeratorValue denominatorValue : Data.Gaussian.Basic.Canonical) where
  /-- The finite operational identity between the retained numerator output and its displayed exact Gaussian value. -/
    numeratorExact : Gaussian.Equivalence.NamedEquivalent evaluation.numerator.output.name
    (Named.exact numeratorValue)
  /-- The finite operational identity between the retained denominator output and its displayed exact Gaussian value. -/
    denominatorExact : Gaussian.Equivalence.NamedEquivalent evaluation.denominator.output.name
    (Named.exact denominatorValue)

constructive_injectivity ExactPair

end

end Purelib.Approximation.Gaussian.Projective.Exact
