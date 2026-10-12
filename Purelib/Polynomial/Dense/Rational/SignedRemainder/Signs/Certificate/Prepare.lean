module
public import Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic

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

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate.Prepare

/-- Scan a finite chain for strict-sign certificates on one interval.

Success retains a certificate for every listed polynomial; none means a component classifier or recursive scan was
inconclusive. -/
def chainSignCertificates? (interval
  : Data.Rat.Interval.Bounds) :
    (chain : List Dense.Rational.Basic.CoordinatePolynomial) → Option
      (Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates interval chain)
  | [] => some .nil
  | p :: chain =>
      match Dense.Rational.Sign.Interval.Prepare.certificate? p interval with
      | none => none
      | some head =>
          match chainSignCertificates?
            interval chain with
          | none => none
          | some tail => some (.cons head tail)
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate.Prepare

end
