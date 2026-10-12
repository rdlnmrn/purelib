module

import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.Ring.Int

/-!
# Vanishing Cauchy indices of certified neutral chains

The retained polynomial inputs and interval bounds determine the certificate
indices. Each certificate retains its actual samples, signed chains and branch evidence.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates

open Purelib
open Purelib.Polynomial

/-- Whole-cell strict signs for the actual raw signed chain force its doubled Cauchy index to vanish.

The retained chain has equal doubled endpoint variations. Subtracting
those two integer readings gives zero without changing the original chain. -/
public theorem cauchyIndex2_eq_zero {R S : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificates : Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates interval
      (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain S R)) :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S interval.lower interval.upper = 0 := by
  unfold Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
  rw [certificates.endpointVariation_eq]
  ring1

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Certificate.ChainSignCertificates

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates

open Purelib
open Purelib.Polynomial

/-- Neutral certificates for the signed remainder chain force its doubled Cauchy index to vanish.

The retained chain has equal doubled endpoint variations. Subtracting
those two integer readings gives zero without changing the original chain. -/
public theorem cauchyIndex2_eq_zero {R S : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificates : Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates interval
      (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain S R)) :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S interval.lower interval.upper = 0 := by
  unfold Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
  rw [certificates.endpointVariation_eq]
  ring1

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates
