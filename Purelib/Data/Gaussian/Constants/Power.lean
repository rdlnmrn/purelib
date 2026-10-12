module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Multiplication by the supplied natural power of gamma scales squared norm by the corresponding power of two. -/
theorem Constants.Power.normSq_gamma_pow_mul (exponent : Nat) (source : Basic.Canonical) :
    Norm.Basic.normSq (Power.natPow Basic.Canonical.gamma exponent * source) =
      (2 : Fraction.Rational) ^ exponent * Norm.Basic.normSq source := by
  rw [Norm.Basic.normSq_mul, Power.normSq_natPow, Constants.normSq_gamma]

end Gaussian

end Purelib.Data

end

/-!
# Choice-free completed CCL blocks

Raw words, decoder matrices, determinants, and the strict post-inversion norm
estimate are all finite computations over constructive Gaussian fractions.
-/

@[expose] public section

namespace Purelib.Data.Gaussian.Constants.Power

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A strict dyadic norm bound remains the same strict bound after multiplication by the matching power of gamma. -/
theorem normalized_denominator_descent (exponent : Nat)
    {postDenominator oldDenominator : Basic.Canonical}
    (scaled : (2 : Fraction.Rational) ^ exponent * Data.Gaussian.Norm.Basic.normSq postDenominator <
      Data.Gaussian.Norm.Basic.normSq oldDenominator) :
    Data.Gaussian.Norm.Basic.normSq (Power.natPow Basic.Canonical.gamma exponent * postDenominator) <
      Data.Gaussian.Norm.Basic.normSq oldDenominator := by
  rw [normSq_gamma_pow_mul]
  exact scaled

end Purelib.Data.Gaussian.Constants.Power

end
