module
public import Purelib.Polynomial.Ascending.Gaussian.Progressive.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Progressive.Table
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Table.CCL.Request
import Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic (TaylorJet)

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

/-- Every coefficient of every constructed arithmetic or composition table
answers one common finite accuracy and CCL-bit request. -/
theorem coefficient_bitstream_and_allowance
  (jet : TaylorJet)
    {coefficient : Name.Coherent.CoherentNamed} (member : coefficient ∈ jet.coefficients)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    Table.CCL.Request.RequestContract jet.coefficients coefficient target positive count :=
  jet.table.member_bitstream_and_allowance member target positive count

/-- Truncation transports the complete finite request contract for every
retained coefficient; discarded entries create no hidden obligation. -/
theorem
  truncated_coefficient_bitstream_and_allowance
  (jet : TaylorJet)
    (keep : Nat) {coefficient : Name.Coherent.CoherentNamed}
    (member : coefficient ∈ (TaylorJet.truncate keep jet).coefficients)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    Table.CCL.Request.RequestContract (TaylorJet.truncate keep
      jet).coefficients coefficient target positive
      count :=
  (TaylorJet.truncate keep jet).coefficient_bitstream_and_allowance member target
    positive
    count
end

end Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic.TaylorJet

end
