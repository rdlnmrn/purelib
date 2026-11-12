module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Cofactor
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Residual bounds for finite multiplicity bases

The exact multiplicity basis gives two complementary finite statements.
First, a sufficiently small residual of the original polynomial selects at
least one displayed squarefree basis factor with small residual.  Second, for
a preselected factor, an explicit positive lower bound on the remaining
unit/cofactor product transfers its residual bound back to the original
polynomial in an integer-power form.

No rational root, real exponent, root collection, or completed value occurs:
all powers are natural powers of displayed rational quadrances.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Power

/-- Rational constant absorbing a positive cofactor lower bound into every
positive natural multiplicity. -/
def integerPowerConstant (localConstant
  cofactorLower : Fraction.Rational) :
    Fraction.Rational :=
  localConstant * max 1 cofactorLower⁻¹

/-- Integer-power chordal transfer for a preselected repeated factor.  The
input `localBound` may come from either local residual-to-chordal theorem.
The conclusion contains only natural powers and the original displayed
polynomial residual quadrance. -/
theorem
  chordalPow_le_integerPowerConstant_mul_sourceResidual
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (decomposition :
      Squarefree.Decomposition p)
    (before after : List Basis.Positive.PositiveEntry) (entry :
      Basis.Positive.PositiveEntry)
    (split : decomposition.positiveMultiplicityEntries =
      before ++ entry :: after) (point : Gaussian.Basic.Canonical)
    (cofactor : Cofactor.CofactorLower decomposition before after point)
    {chordal localConstant : Fraction.Rational}
    (chordalNonnegative : 0 ≤ chordal)
    (localConstantNonnegative : 0 ≤ localConstant)
    (localBound : chordal ≤ localConstant *
      Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point)) :
    chordal ^ entry.multiplicity ≤
      integerPowerConstant localConstant cofactor.bound ^ entry.multiplicity
        *
        Gaussian.Norm.Basic.normSq (p.eval point) := by
  let residual := Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point)
  let inverseScale := max 1 cofactor.bound⁻¹
  have inversePositive : 0 < cofactor.bound⁻¹ :=
    Field.inv_pos_direct cofactor.positive
  have inverseScaleOne : (1 : Fraction.Rational) ≤ inverseScale :=
    Basic.le_max_left _ _
  have inverseScalePositive : 0 < inverseScale :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le inverseScaleOne
  have inverseLeScale : cofactor.bound⁻¹ ≤ inverseScale :=
    Basic.le_max_right _ _
  have scaleLePower : inverseScale ≤
      inverseScale ^ entry.multiplicity := by
    obtain ⟨tail, multiplicityEq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt entry.multiplicityPositive)
    rw [multiplicityEq, pow_succ]
    have oneLeTailPower : (1 : Fraction.Rational) ≤ inverseScale ^ tail := by
      have onePower : (1 : Fraction.Rational) ^ tail ≤ inverseScale ^ tail :=
        Arithmetic.pow_le_pow_direct (by decide)
          inverseScaleOne tail
      simpa only [one_pow] using onePower
    calc
      inverseScale = 1 * inverseScale := by ring1
      _ ≤ inverseScale ^ tail * inverseScale :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          oneLeTailPower inverseScalePositive.le
  have inverseLePower : cofactor.bound⁻¹ ≤
      inverseScale ^ entry.multiplicity :=
    inverseLeScale.trans scaleLePower
  have localPower : chordal ^ entry.multiplicity ≤
      localConstant ^ entry.multiplicity * residual ^ entry.multiplicity := by
    have powered := Arithmetic.pow_le_pow_direct
      chordalNonnegative localBound entry.multiplicity
    simpa only [Fraction.Field.mul_pow_direct, residual] using powered
  have cofactorTransfer :=
    Cofactor.cofactor_mul_factorResidualPow_le_sourceResidual decomposition before
      after entry split point cofactor
  have residualPowerBound : residual ^ entry.multiplicity ≤
      cofactor.bound⁻¹ * Gaussian.Norm.Basic.normSq (p.eval point) := by
    have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct
      cofactorTransfer
      (Field.inv_pos_direct cofactor.positive).le
    calc
      residual ^ entry.multiplicity =
          cofactor.bound⁻¹ *
            (cofactor.bound * residual ^ entry.multiplicity) := by
        rw [← Fraction.Field.mul_assoc,
          Fraction.Field.inv_mul_cancel cofactor.bound
            cofactor.positive.ne',
          Fraction.Field.one_mul]
      _ ≤ cofactor.bound⁻¹ * Gaussian.Norm.Basic.normSq (p.eval point) := scaled
  have absorbed : residual ^ entry.multiplicity ≤
      inverseScale ^ entry.multiplicity * Gaussian.Norm.Basic.normSq (p.eval point) :=
    residualPowerBound.trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        inverseLePower (Gaussian.Norm.Basic.normSq_nonneg (p.eval point)))
  calc
    chordal ^ entry.multiplicity ≤
        localConstant ^ entry.multiplicity *
          residual ^ entry.multiplicity := localPower
    _ ≤ localConstant ^ entry.multiplicity *
          (inverseScale ^ entry.multiplicity * Gaussian.Norm.Basic.normSq (p.eval point)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct absorbed
        (Arithmetic.pow_nonneg_direct localConstantNonnegative
          entry.multiplicity)
    _ = integerPowerConstant localConstant cofactor.bound ^
          entry.multiplicity * Gaussian.Norm.Basic.normSq (p.eval point) := by
      dsimp only [integerPowerConstant, inverseScale]
      rw [Fraction.Field.mul_pow_direct]
      ring1

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Power

end
