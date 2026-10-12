module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Projective.Basic
import Purelib.Approximation.Gaussian.Expression.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.Gaussian.Projective.Basic.Pair

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

section ProjectiveEvaluation

set_option genInjectivity false in
/-- Finite operational pole data: the denominator process is operationally zero while the numerator process is uniformly
apart.

This records the projective infinity chart without adjoining a completed infinity value. -/
structure PoleCertificate (evaluation :
  Gaussian.Projective.Basic.Pair) where
  /-- Uniform whole-ball apartness of the retained numerator output. -/ numeratorApart : Named.Apart
    evaluation.numerator.output.name
  /-- The finite operational identity between the retained denominator output and the exact zero name. -/
    denominatorZero : Gaussian.Equivalence.NamedEquivalent evaluation.denominator.output.name
    (Named.exact 0)

constructive_injectivity PoleCertificate

end ProjectiveEvaluation

end

end Purelib.Approximation.Gaussian.Projective.Basic.Pair
