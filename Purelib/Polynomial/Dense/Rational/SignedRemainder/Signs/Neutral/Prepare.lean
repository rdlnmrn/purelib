module
public import Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step.Prepare
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step

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

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.Prepare

/-- Structural finite scanner for an arbitrary number of disjoint cancelling
events in one signed chain. -/
def neutralChainCertificate? (interval :
  Data.Rat.Interval.Bounds) (head : Dense.Rational.Basic.CoordinatePolynomial) :
    (tail : List Dense.Rational.Basic.CoordinatePolynomial) →
      Option (Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval head tail)
  | [] =>
      match Dense.Rational.Sign.Interval.Prepare.certificate? head interval with
      | none => none
      | some headStable => some (.single headStable)
  | q :: tail =>
      match Dense.Rational.Sign.Interval.Prepare.certificate? head interval with
      | none => none
      | some headStable =>
          match tail with
          | [] =>
              match Dense.Rational.Sign.Interval.Prepare.certificate? q interval with
              | none => none
              | some qStable => some (.stable headStable (.single qStable))
          | r :: suffix =>
              match Dense.Rational.Sign.Interval.Prepare.certificate? q interval with
              | some _ =>
                  match Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificate?
                    interval q (r :: suffix) with
                  | none => none
                  | some rest => some (.stable headStable rest)
              | none =>
                  if nextEq : r = -((Dense.Basic.DensePolynomial.divMod head q).remainder) then
                    match Dense.Rational.SignedRemainder.Signs.Step.Prepare.signedStepCellCertificate? head q interval
                      with
                    | none => none
                    | some step =>
                        match
                          neutralChainCertificate?
                          interval r suffix with
                        | none => none
                        | some rest => some (.event nextEq step rest)
                  else none

/-- Prepare neutral certificates for an entire finite signed chain.

The empty chain succeeds directly; a nonempty chain retains the scanner's stable-sign and cancelling-event evidence, or
returns none when unresolved. -/
def neutralChainCertificates? (interval :
  Data.Rat.Interval.Bounds) :
    (chain : List Dense.Rational.Basic.CoordinatePolynomial) → Option
      (Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates interval chain)
  | [] => some .nil
  | head :: tail =>
      match Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificate? interval head tail with
      | none => none
      | some certificate => some (.cons certificate)
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.Prepare

end
