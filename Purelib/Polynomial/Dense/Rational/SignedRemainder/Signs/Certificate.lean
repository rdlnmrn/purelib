module

public import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.Basic
import Purelib.Data.Rat.Sign.Variation
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Evaluation
import Batteries.Data.List.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Entrywise strict signs of retained polynomial chains

Each certificate retains the displayed polynomial list and interval. Its
strict-sign entries preserve every endpoint sign and therefore the doubled
variation of that exact list.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate

open Purelib
open Purelib.Polynomial

@[expose] public section

set_option genInjectivity false in
/-- A proof-relevant finite list of whole-cell strict-sign certificates.

The empty constructor retains the empty list. Each cons retains the exact
head strict-sign interval certificate and the certificate for its original tail. -/
inductive ChainSignCertificates (interval : Data.Rat.Interval.Bounds) :
    List Dense.Rational.Basic.CoordinatePolynomial → Type
  /-- Certify the empty list of polynomial signs. -/ | nil :
    Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates interval []
  /-- Prepend one strict-sign interval certificate to the retained chain certificates. -/ | cons {p :
    Dense.Rational.Basic.CoordinatePolynomial} {chain : List Dense.Rational.Basic.CoordinatePolynomial}
      (head : Dense.Rational.Sign.Interval.Basic.Certificate p interval)
      (tail : Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates interval chain)
        :
      Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates interval (p :: chain)

constructive_injectivity ChainSignCertificates

end

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates

open Purelib
open Purelib.Polynomial

/-- The certified polynomial list has matching signs entrywise at both endpoints.

Every head certificate gives a positive product of its two endpoint values.
Structural induction retains their sign equalities in the original list order. -/
public theorem endpoint_signs {interval : Data.Rat.Interval.Bounds} {chain : List
  Dense.Rational.Basic.CoordinatePolynomial}
    (certificates : Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates interval chain) :
    List.Forall₂ (fun x y => Data.Rat.Sign.Basic.sign x = Data.Rat.Sign.Basic.sign y)
      (chain.map fun p => p.eval interval.lower)
      (chain.map fun p => p.eval interval.upper) := by
  induction certificates with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      apply List.Forall₂.cons
      · exact Data.Rat.Sign.Basic.sign_eq_of_mul_pos head.endpoint_stable
      · exact inductionHypothesis

/-- Strict-sign certificates for every chain member preserve endpoint variation.

The entrywise endpoint sign relation preserves each adjacent sign distance
and therefore the doubled finite variation of the exact retained chain. -/
public theorem endpointVariation_eq {interval : Data.Rat.Interval.Bounds} {chain : List
  Dense.Rational.Basic.CoordinatePolynomial}
    (certificates : Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates interval chain) :
    Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 chain interval.lower =
      Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 chain interval.upper := by
  apply Data.Rat.Sign.Variation.variation2_congr_of_forall₂_sign
  exact certificates.endpoint_signs

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates
