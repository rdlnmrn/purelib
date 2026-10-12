module
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Neutral
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.Prepare
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Neutral.Prepare

/-- Executable neutral-cell check for the exact raw Cauchy chain. -/
def neutralCauchyCell?
    (R S : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) : Bool :=
  (Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval
    (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain S R)).isSome

/-- A successful neutral-chain check certifies that the doubled Cauchy index on the retained interval is zero. -/
theorem cauchyIndex2_eq_zero_of_neutralCauchyCell
    (R S : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds)
    (checked : neutralCauchyCell? R S interval = true) :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S interval.lower interval.upper = 0 := by
  unfold neutralCauchyCell? at checked
  cases found : Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval
      (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain S R) with
  | none =>
      rw [found] at checked
      cases checked
  | some certificates =>
      exact Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates.cauchyIndex2_eq_zero certificates
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Neutral.Prepare

end
