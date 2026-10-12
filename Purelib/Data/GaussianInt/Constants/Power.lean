module
import Purelib.Data.Gaussian.Constants
public import Purelib.Data.Gaussian.Power

public import Purelib.Data.GaussianInt.Constants
public import Purelib.Data.GaussianInt.Power
import Mathlib.Algebra.Group.Nat.Defs

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic

@[expose] public section
namespace Purelib.Data.GaussianInt

/-- The quadrance of the explicit nth power of one plus the imaginary unit is two to that
power. -/
@[simp] theorem normNat_gammaInt_pow (exponent : Nat) :
    normNat (natPow gammaInt exponent) = 2 ^ exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [natPow_succ, normNat_mul, inductionHypothesis, normNat_gammaInt,
        Nat.pow_succ]

/-- Embedding an explicit power of integral gamma gives the same explicit power of
rational gamma. -/
@[simp] theorem toGaussian_gammaInt_pow (exponent : Nat) :
    toGaussian (natPow gammaInt exponent) =
      Power.natPow
        Canonical.gamma exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [natPow_succ, toGaussian_mul, inductionHypothesis,
        Power.natPow_succ,
        toGaussian_gammaInt]

end Purelib.Data.GaussianInt
end
