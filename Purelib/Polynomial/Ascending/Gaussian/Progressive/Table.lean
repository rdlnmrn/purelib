module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic
import Purelib.Approximation.Gaussian.Table.Basic
public import Purelib.Approximation.Gaussian.Table.Request
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic.TaylorJet
section

/-- View the jet's exact retained coefficient channels as their shared-request channel table. -/
def table (jet :
  Ascending.Gaussian.Progressive.Basic.TaylorJet) : Table.Basic.ChannelTable := ⟨jet.coefficients⟩

/-- The requested output list retains the displayed finite coefficient
arity. -/
theorem requestNames_length (jet :
  Ascending.Gaussian.Progressive.Basic.TaylorJet) (target : Fraction.Rational)
    (positive : 0 < target) :
    (jet.table.requestNames target positive).length = jet.length :=
  jet.table.requestNames_length target positive
end

end Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic.TaylorJet

end
