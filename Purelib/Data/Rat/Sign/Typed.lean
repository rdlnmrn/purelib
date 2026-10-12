module
public import Purelib.Data.Sign.Basic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction

open Purelib.Data.Sign

section
@[expose] public section

/-!
# Finite signs for the constructive Cauchy-product identity

This module isolates the finite local sign calculation behind multiplication
of two displayed complex paths.  The three signs are split explicitly: there
is no `Fintype` instance, enumeration of a carrier, or choice-based search.
-/

namespace Purelib.Data.Sign
section Sign

open Purelib.Data.Rat in
open _root_.Purelib.Data renaming Sign -> FiniteSign in
/-- Classify a rational as the retained finite negative, zero or positive sign constructor.

The concrete rational comparison and equality decisions select one of the original three finite constructors. This
retains the nominal finite-sign carrier for subsequent compatibility tables. -/
def ofCoordinate (x : Fraction.Rational) : FiniteSign :=
  if x < 0 then negative else if x = 0 then zero else positive
end Sign
end Purelib.Data.Sign

end
