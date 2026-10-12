module

public import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.GaussianInt.Resource

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.GaussianInt.Fraction.Resource

open Purelib.Data.GaussianInt

/-- Measure a displayed Gaussian fraction by the maximum width of its retained numerator
and denominator. -/
def hurwitzFractionWidth (fraction : Fraction) : Nat :=
  max (Resource.gaussianIntWidth fraction.numerator)
    (Resource.gaussianIntWidth fraction.denominator)
end Purelib.Data.GaussianInt.Fraction.Resource

end
