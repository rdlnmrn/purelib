module
import Purelib.Polynomial.Dense.Arithmetic

public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained Cauchy-event resolution branches

A neutral denominator chain or a resolved numerator tail retains the original
strict-sign certificate that selected the finite branch.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic

open Purelib
open Purelib.Polynomial

@[expose] public section

set_option genInjectivity false in
/-- The proof-bearing branch chosen by the finite Cauchy-event scanner.

The neutral branch retains the denominator strict-sign certificate and
the exact full-chain certificate. The numerator branch retains its strict-sign
certificate and the exact neutral tail beginning with the negated remainder. -/
inductive CauchyEventResolution
    (R S : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) where
  /-- Resolve a cell with a nonvanishing denominator and a neutral full chain.

The retained strict-sign certificate excludes denominator zeros throughout the interval. -/ | neutral
      (denominator : Dense.Rational.Sign.Interval.Basic.Certificate S interval)
      (chain : Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates interval
        (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain S R))
  /-- Resolve a cell with a nonvanishing numerator and a neutral remainder tail.

The tail is the exact signed chain beginning with the numerator and the negated remainder of denominator division. -/ |
  numerator
      (certificate : Dense.Rational.Sign.Interval.Basic.Certificate R interval)
      (tail : Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates interval
        (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain R (-((Dense.Basic.DensePolynomial.divMod S
          R).remainder))))

constructive_injectivity CauchyEventResolution

end

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
