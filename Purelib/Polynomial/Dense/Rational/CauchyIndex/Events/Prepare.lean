module

import Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Signs
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.Prepare
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.Neutral
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral

/-!
# Finite preparation of Cauchy event certificates

The retained polynomial inputs and interval bounds determine the certificate
indices. Each certificate retains its actual samples, signed chains and branch evidence.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Prepare

open Purelib
open Purelib.Polynomial

set_option backward.match.sparseCases false in
/-- Executable finite event classifier for one displayed Cauchy pair.

The first branch retains a strict denominator sign and neutral full chain.
Otherwise the procedure retains a strict numerator sign and neutral remainder
tail, or returns none when neither finite certificate pair is available. -/
@[expose] public def cauchyEventSigns?
    (R S : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
    Option (Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns R S interval) :=
  match Dense.Rational.Sign.Interval.Prepare.certificate? S interval,
      Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval
        (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain S R) with
  | some denominator, some chain => some (.ofNeutral denominator chain)
  | _, _ =>
      match Dense.Rational.Sign.Interval.Prepare.certificate? R interval,
          Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval
            (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain R (-((Dense.Basic.DensePolynomial.divMod S
              R).remainder))) with
      | some numerator, some tail =>
          some (.ofResolvedNumerator numerator tail)
      | _, _ => none

set_option backward.match.sparseCases false in
/-- The certificate-retaining scanner follows exactly the same finite branch order as `cauchyEventSigns?`.

The scanner retains the exact successful strict-sign and neutral-chain
certificates. It tests the denominator branch before the numerator branch and
returns none if both finite attempts remain unresolved. -/
@[expose] public def cauchyEventResolution?
    (R S : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
    Option (Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution R S interval) :=
  match Dense.Rational.Sign.Interval.Prepare.certificate? S interval,
      Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval
        (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain S R) with
  | some denominator, some chain => some (.neutral denominator chain)
  | _, _ =>
      match Dense.Rational.Sign.Interval.Prepare.certificate? R interval,
          Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval
            (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain R (-((Dense.Basic.DensePolynomial.divMod S
              R).remainder))) with
      | some numerator, some tail => some (.numerator numerator tail)
      | _, _ => none

/-- Forgetting retained resolution data gives the sign-only event classifier.

Both procedures follow the same neutral-chain and resolved-numerator branch order. -/
public theorem cauchyEventResolution?_map_signs
    (R S : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
    (Dense.Rational.CauchyIndex.Events.Prepare.cauchyEventResolution? R S interval).map
        Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution.signs =
      Dense.Rational.CauchyIndex.Events.Prepare.cauchyEventSigns? R S interval := by
  unfold Dense.Rational.CauchyIndex.Events.Prepare.cauchyEventResolution?
    Dense.Rational.CauchyIndex.Events.Prepare.cauchyEventSigns?
  split
  · rfl
  · split <;> rfl

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Prepare
