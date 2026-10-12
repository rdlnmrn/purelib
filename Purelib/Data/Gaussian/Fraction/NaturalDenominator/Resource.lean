module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Resource
import Purelib.Data.Nat.BitWidth

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

namespace Purelib.Data.Gaussian.Fraction.NaturalDenominator.Resource

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Nat in
/-- Compute the larger of the integer numerator width and the natural denominator width. -/
def commonFractionWidth (fraction :
  Basic.Canonical.Fraction.NaturalDenominator) : Nat :=
  max (GaussianInt.Resource.gaussianIntWidth fraction.numerator) (BitWidth.natWidth fraction.denominator)
end Purelib.Data.Gaussian.Fraction.NaturalDenominator.Resource

end
