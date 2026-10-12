module

import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.Basic
import Purelib.Data.Rat.Sign.Jump
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Neutral certificates for retained signed chains

The retained polynomial inputs and interval bounds determine the certificate
indices. Each certificate retains its actual samples, signed chains and branch evidence.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral

open Purelib
open Purelib.Polynomial

@[expose] public section

set_option genInjectivity false in
/-- A nonempty chain whose fixed-sign heads and disjoint signed triples all cancel between the two endpoints.

Each constructor retains the exact head and tail indices. Stable heads
carry strict-sign certificates; an event carries the original remainder
equation and signed-step certificate before continuing with its retained tail. -/
inductive NeutralChainCertificate (interval : Data.Rat.Interval.Bounds) :
    (head : Dense.Rational.Basic.CoordinatePolynomial) → (tail : List Dense.Rational.Basic.CoordinatePolynomial) → Type
  /-- Certify a singleton chain by a strict-sign certificate for its only member. -/ | single {p :
    Dense.Rational.Basic.CoordinatePolynomial}
      (headStable : Dense.Rational.Sign.Interval.Basic.Certificate p interval) :
      Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval p []
  /-- Prepend a strict-sign head to an already neutral nonempty chain. -/ | stable {p q :
    Dense.Rational.Basic.CoordinatePolynomial} {tail : List Dense.Rational.Basic.CoordinatePolynomial}
      (headStable : Dense.Rational.Sign.Interval.Basic.Certificate p interval)
      (rest : Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval q tail) :
      Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval p (q :: tail)
  /-- Prepend a signed Euclidean event to a neutral remainder chain.

The displayed remainder equation and signed-step certificate make the two new jumps cancel between endpoints. -/ | event
  {p q r : Dense.Rational.Basic.CoordinatePolynomial} {tail : List Dense.Rational.Basic.CoordinatePolynomial}
      (nextEq : r = -((Dense.Basic.DensePolynomial.divMod p q).remainder))
      (step : Dense.Rational.SignedRemainder.Signs.Step.SignedStepCellCertificate p q interval)
      (rest : Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval r tail) :
      Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval p (q :: r ::
        tail)

constructive_injectivity NeutralChainCertificate

end

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate

open Purelib
open Purelib.Polynomial

/-- Recover the strict-sign interval certificate for the first chain member.

The singleton and stable branches retain their head certificate directly;
the event branch extracts it from the original signed-step certificate. -/
@[expose] public def headStable {interval : Data.Rat.Interval.Bounds} {p :
  Dense.Rational.Basic.CoordinatePolynomial}
    {tail : List Dense.Rational.Basic.CoordinatePolynomial}
    (certificate : Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval p tail) :
    Dense.Rational.Sign.Interval.Basic.Certificate p interval :=
  match certificate with
  | .single headCertificate => headCertificate
  | .stable headCertificate .. => headCertificate
  | .event _ step .. => step.leftCertificate

/-- The first member of a neutral chain has equal signs at both endpoints.

The retained strict-sign head certificate gives a positive product of
endpoint values, so their integer signs agree. -/
public theorem headEndpointSign_eq {interval : Data.Rat.Interval.Bounds} {p :
  Dense.Rational.Basic.CoordinatePolynomial}
    {tail : List Dense.Rational.Basic.CoordinatePolynomial}
    (certificate : Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval p tail) :
    Data.Rat.Sign.Basic.sign (p.eval interval.lower) = Data.Rat.Sign.Basic.sign (p.eval interval.upper) :=
  Data.Rat.Sign.Basic.sign_eq_of_mul_pos certificate.headStable.endpoint_stable

/-- A neutral nonempty chain has equal endpoint variations.

Stable heads preserve each adjacent jump, while certified signed triples preserve the sum of their two jumps. -/
public theorem endpointVariation_eq {interval : Data.Rat.Interval.Bounds} {p :
  Dense.Rational.Basic.CoordinatePolynomial}
    {tail : List Dense.Rational.Basic.CoordinatePolynomial}
    (certificate : Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval p tail) :
    Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 (p :: tail) interval.lower =
      Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 (p :: tail) interval.upper := by
  induction certificate with
  | single => rfl
  | @stable p q tail headStable rest inductionHypothesis =>
      have headSign := Data.Rat.Sign.Basic.sign_eq_of_mul_pos headStable.endpoint_stable
      have nextSign := rest.headEndpointSign_eq
      change Data.Rat.Sign.Jump.signJump (p.eval interval.lower) (q.eval interval.lower) +
          Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 (q :: tail) interval.lower =
        Data.Rat.Sign.Jump.signJump (p.eval interval.upper) (q.eval interval.upper) +
          Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 (q :: tail) interval.upper
      rw [Data.Rat.Sign.Jump.signJump_congr headSign nextSign, inductionHypothesis]
  | @event p q r tail nextEq step rest inductionHypothesis =>
      subst r
      have localCancellation := step.endpoint_cancellation
      change
        Data.Rat.Sign.Jump.signJump (p.eval interval.lower) (q.eval interval.lower) +
            (Data.Rat.Sign.Jump.signJump (q.eval interval.lower)
                ((-((Dense.Basic.DensePolynomial.divMod p q).remainder)).eval interval.lower) +
              Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
                ((-((Dense.Basic.DensePolynomial.divMod p q).remainder)) :: tail) interval.lower) =
          Data.Rat.Sign.Jump.signJump (p.eval interval.upper) (q.eval interval.upper) +
            (Data.Rat.Sign.Jump.signJump (q.eval interval.upper)
                ((-((Dense.Basic.DensePolynomial.divMod p q).remainder)).eval interval.upper) +
              Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
                ((-((Dense.Basic.DensePolynomial.divMod p q).remainder)) :: tail) interval.upper)
      rw [← Nat.add_assoc, ← Nat.add_assoc, localCancellation,
        inductionHypothesis]

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral

open Purelib
open Purelib.Polynomial

@[expose] public section

set_option genInjectivity false in
/-- A neutral-chain certificate allowing either an empty or a nonempty polynomial list.

The nonempty case retains the indexed certificate for that exact head and tail. -/
inductive NeutralChainCertificates (interval : Data.Rat.Interval.Bounds) :
    List Dense.Rational.Basic.CoordinatePolynomial → Type
  /-- The empty polynomial chain is neutral. -/ | nil :
    Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates interval []
  /-- Package a neutral certificate for the displayed nonempty chain. -/ | cons {head :
    Dense.Rational.Basic.CoordinatePolynomial} {tail : List Dense.Rational.Basic.CoordinatePolynomial}
      (certificate : Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval head tail) :
      Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates interval (head :: tail)

constructive_injectivity NeutralChainCertificates

end

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates

open Purelib
open Purelib.Polynomial

/-- Any certified neutral chain has equal variations at the interval endpoints.

The indexed neutral certificates relate the actual chain at both interval
endpoints and preserve its doubled finite sign variation. -/
public theorem endpointVariation_eq {interval : Data.Rat.Interval.Bounds} {chain : List
  Dense.Rational.Basic.CoordinatePolynomial}
    (certificates : Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates interval chain) :
    Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 chain interval.lower =
      Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 chain interval.upper := by
  cases certificates with
  | nil => rfl
  | cons certificate => exact certificate.endpointVariation_eq

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates
