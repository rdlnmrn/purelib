module
public import Purelib.Data.CCL.Encoding.Encoder.Integral

import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Data.List.Prefix
import Purelib.Data.GaussianInt.Basic

section
@[expose] public section

/-!
# Finite approximation towers for exact CCL names

This module packages the elementary prefix clauses of the manuscript's
finite-name tower without introducing a completed stream or a collection of
all points in a cylinder.
-/

namespace Purelib.Data.CCL.Encoding.Prefix.Tower

open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.List
/-- Require the retained stem to prefix the exact integral encoding of the displayed nonzero-numerator fraction. -/
def Cylinder (stem :
  BinaryPrefix.Basic.SourceEncodingPrefixTowerWordAlias) (fraction :
  GaussianInt.Fraction.Basic.SourceEncodingPrefixTowerFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0) : Prop :=
  stem.IsPrefix
    (Encoder.Integral.encode fraction numeratorNonzero)

/-- The requested finite prefix of a fraction's exact integral encoding belongs to its retained prefix cylinder. -/
theorem prefixAt_cylinder (fraction :
  GaussianInt.Fraction.Basic.SourceEncodingPrefixTowerFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0) (count : Nat) :
    Cylinder
      (Prefix.prefixAt (Encoder.Integral.encode fraction numeratorNonzero)
        count)
      fraction numeratorNonzero :=
  List.take_prefix count
    (Encoder.Integral.encode fraction numeratorNonzero)
end Purelib.Data.CCL.Encoding.Prefix.Tower

end
