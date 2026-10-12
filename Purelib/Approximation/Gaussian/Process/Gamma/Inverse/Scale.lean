module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Process.Apart.Based
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Gamma.Inverse
public import Purelib.Approximation.Gaussian.Process.Multiplication
public import Purelib.Approximation.Gaussian.Process.Normalization.Basic
public import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Data.Gaussian.Constants
public import Purelib.Data.Gaussian.Constants.Inverse
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
public import Purelib.Data.Gaussian.Power.Gamma
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Process.Gamma

open Purelib.Approximation.Gaussian.Process.Normalization.Basic

open Purelib.Data.CCL.Encoding.Padding

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Constants

open Purelib.Data.Gaussian.Power

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale

/-- Divide the inverse tail by the unary scale already emitted. -/
def normalizedInverseProcess
    (residual : Approximation.Gaussian.Process) (base : residual.State)
    (certificate : Ball.Apart
      (residual.ball base)) (count : Nat) : Approximation.Gaussian.Process :=
  Approximation.Gaussian.Process.mul
    (Approximation.Gaussian.Process.exact
      (Power.natPow Canonical.gamma count)⁻¹)
    (Inverse.inverseOfApartProcess residual base certificate)

/-- Construct the initial normalized inverse state from the exact reciprocal unary factor and the retained apart
residual state. -/
def normalizedInverseInitial
    (residual : Approximation.Gaussian.Process) (base : residual.State)
    (certificate : Ball.Apart
      (residual.ball base)) (count : Nat) :
    (normalizedInverseProcess residual base certificate count).State
      :=
  ((), Inverse.inverseOfApartInitial residual base certificate)

/-- Every candidate of the normalized inverse chart is an exact scaled post-sector inverse of one nonzero residual
admitted at the retained base. The scale records precisely the unary padding already emitted. -/
theorem normalizedInverse_candidate_semantics
    (residual : Approximation.Gaussian.Process) (base : residual.State)
    (certificate : Ball.Apart
      (residual.ball base)) (count : Nat)
    {state : (normalizedInverseProcess residual base certificate
      count).State}
    {value : Canonical}
    (possible : (normalizedInverseProcess residual base certificate
      count).Possible
      state value) :
    ∃ residualValue : Canonical,
      residual.Possible base residualValue ∧
      residualValue ≠ 0 ∧
      value = (Power.natPow Canonical.gamma count)⁻¹ * (Canonical.gamma *
        residualValue)⁻¹ := by
  rcases possible with
    ⟨scale, inverseTail, scalePossible, inversePossible, valueEqual⟩
  rcases inversePossible with
    ⟨numerator, residualValue, numeratorPossible, residualPossible,
      inverseEqual⟩
  have residualAtBase : residual.Possible base residualValue :=
    state.2.2.source.persists residualPossible
  have residualNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq residualValue :=
    certificate.positive.trans_le
      (certificate.lower (residual.possible_inside residualAtBase))
  have residualNonzero : residualValue ≠ 0 := by
    intro residualZero
    rw [residualZero, Data.Gaussian.Norm.Basic.normSq_zero] at residualNormPositive
    exact (lt_irrefl _ residualNormPositive).elim
  refine ⟨residualValue, residualAtBase, residualNonzero, ?_⟩
  calc
    value = scale * inverseTail := valueEqual
    _ = (Power.natPow Canonical.gamma count)⁻¹ * (numerator / residualValue) := by
      rw [scalePossible, inverseEqual]
    _ = (Power.natPow Canonical.gamma count)⁻¹ * (Canonical.gamma⁻¹ /
      residualValue) := by
      rw [numeratorPossible]
    _ = (Power.natPow Canonical.gamma count)⁻¹ * (Canonical.gamma *
      residualValue)⁻¹ := by
      rw [Inverse.gamma_inv_div_eq_inverse residualValue residualNonzero]

/-- Candidate apartness of a normalized inverse process from a retained strict residual upper bound.

The candidate retains the same normalized inverse process and its strict residual
upper bound. That bound supplies an explicit apartness witness at the requested
stage. -/
def normalizedInversePossibleApart
    (residual : Approximation.Gaussian.Process) (base : residual.State)
    (certificate : Ball.Apart
      (residual.ball base)) (count : Nat) (upper : Fraction.Rational)
    (upperBound : ∀ {value : Canonical}, residual.Possible base value →
      Data.Gaussian.Norm.Basic.normSq value ≤ upper)
    (upperStrict : upper <
      Residual.paddingTarget count) :
    Possible.PossibleApart (normalizedInverseProcess residual base
      certificate count) := by
  let power : Fraction.Rational := (2 : Fraction.Rational) ^ (count + 1)
  let lowerSq : Fraction.Rational := (power * upper)⁻¹
  rcases residual.witness base with ⟨displayed, displayedPossible⟩
  have displayedLower := certificate.lower
    (residual.possible_inside displayedPossible)
  have upperPositive : 0 < upper :=
    certificate.positive.trans_le
      (displayedLower.trans (upperBound displayedPossible))
  have powerPositive : 0 < power :=
    Fraction.Order.Arithmetic.pow_pos_direct (by decide) (count + 1)
  have denominatorPositive : 0 < power * upper :=
    Fraction.Order.Arithmetic.mul_pos_direct powerPositive upperPositive
  have denominatorLtOne : power * upper < 1 := by
    have scaled := (Fraction.Order.Field.lt_div_iff_pos powerPositive).1
      upperStrict
    calc
      power * upper = upper * power :=
        Fraction.Field.mul_comm _ _
      _ < 1 := scaled
  have lowerPositive : 0 < lowerSq := by
    exact Fraction.Order.Field.inv_pos_direct denominatorPositive
  have lowerGtOne : 1 < lowerSq := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := power * upper) _ denominatorPositive
    calc
      1 * (power * upper) = power * upper := by ring1
      _ < 1 := denominatorLtOne
      _ = (power * upper)⁻¹ * (power * upper) :=
        (Fraction.Field.inv_mul_cancel _
          denominatorPositive.ne').symm
  let candidateApart := Based.possibleApartOfBall residual base certificate
  exact
    { lowerSq := lowerSq
      positive := lowerPositive
      lower := by
        intro state value possible
        rcases possible with
          ⟨scale, tail, scalePossible, tailPossible, valueEqual⟩
        rcases tailPossible with
          ⟨numerator, denominator, numeratorPossible,
            denominatorPossible, tailEqual⟩
        have denominatorAtBase : residual.Possible base denominator :=
          state.2.2.source.persists denominatorPossible
        have denominatorUpper := upperBound denominatorAtBase
        have denominatorLower :=
          candidateApart.lower state.2.2.source denominatorPossible
        have denominatorNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq denominator :=
          candidateApart.positive.trans_le denominatorLower
        have denominatorNonzero : denominator ≠ 0 := by
          intro denominatorZero
          rw [denominatorZero, Data.Gaussian.Norm.Basic.normSq_zero] at denominatorNormPositive
          exact (lt_irrefl _ denominatorNormPositive).elim
        have smallDenominatorPositive :
            0 < power * Data.Gaussian.Norm.Basic.normSq denominator :=
          Fraction.Order.Arithmetic.mul_pos_direct powerPositive
            denominatorNormPositive
        have smallDenominatorLe :
            power * Data.Gaussian.Norm.Basic.normSq denominator ≤ power * upper :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            denominatorUpper powerPositive.le
        have inverseOrder : (power * upper)⁻¹ ≤
            (power * Data.Gaussian.Norm.Basic.normSq denominator)⁻¹ :=
          Fraction.Order.Field.inv_le_inv_of_pos_direct
            smallDenominatorPositive smallDenominatorLe
        rw [valueEqual, scalePossible, tailEqual, numeratorPossible,
          Data.Gaussian.Norm.Basic.normSq_mul, Gamma.normSq_natPow_gamma_inv,
          Data.Gaussian.Field.normSq_div _ _ denominatorNonzero, Inverse.normSq_gamma_inv,
          Field.half_mul_inverse]
        have normIdentity :
            ((2 : Fraction.Rational) ^ count)⁻¹ *
                (1 / (2 * Data.Gaussian.Norm.Basic.normSq denominator)) =
              (power * Data.Gaussian.Norm.Basic.normSq denominator)⁻¹ := by
          have firstInverse :
              (1 / (2 * Data.Gaussian.Norm.Basic.normSq denominator) : Fraction.Rational) =
                (2 * Data.Gaussian.Norm.Basic.normSq denominator)⁻¹ := by
            change 1 * (2 * Data.Gaussian.Norm.Basic.normSq denominator)⁻¹ =
              (2 * Data.Gaussian.Norm.Basic.normSq denominator)⁻¹
            exact _root_.one_mul _
          rw [firstInverse, ← Fraction.Field.inv_mul_direct]
          apply congrArg (fun coordinate : Fraction.Rational => coordinate⁻¹)
          dsimp only [power]
          rw [pow_succ]
          ring1
        rw [normIdentity]
        exact inverseOrder }

/-- Certify the normalized inverse loop domain from retained residual apartness and a strict upper quadrance below the
emitted padding target.

The lower squared norm uses the exact displayed padding count and the original residual candidate bound. -/
def normalizedInverseLoopDomain
    (residual : Approximation.Gaussian.Process) (base : residual.State)
    (certificate : Ball.Apart
      (residual.ball base)) (count : Nat) (upper : Fraction.Rational)
    (upperBound : ∀ {value : Canonical}, residual.Possible base value →
      Data.Gaussian.Norm.Basic.normSq value ≤ upper)
    (upperStrict : upper <
      Residual.paddingTarget count) :
    Gaussian.Process.Normalization.Basic.LoopDomain
      (normalizedInverseProcess residual base certificate count) :=
  let apart := normalizedInversePossibleApart residual base
    certificate count
    upper upperBound upperStrict
  LoopDomain.ofLower apart (by
    dsimp only [apart]
    let power : Fraction.Rational := (2 : Fraction.Rational) ^ (count + 1)
    rcases residual.witness base with ⟨displayed, displayedPossible⟩
    have displayedLower := certificate.lower
      (residual.possible_inside displayedPossible)
    have upperPositive : 0 < upper := certificate.positive.trans_le
      (displayedLower.trans (upperBound displayedPossible))
    have powerPositive : 0 < power :=
      Fraction.Order.Arithmetic.pow_pos_direct (by decide) (count + 1)
    have denominatorPositive : 0 < power * upper :=
      Fraction.Order.Arithmetic.mul_pos_direct powerPositive upperPositive
    have denominatorLtOne : power * upper < 1 := by
      have scaled := (Fraction.Order.Field.lt_div_iff_pos powerPositive).1
        upperStrict
      calc
        power * upper = upper * power :=
          Fraction.Field.mul_comm _ _
        _ < 1 := scaled
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := power * upper) _ denominatorPositive
    calc
      1 * (power * upper) = power * upper := by ring1
      _ < 1 := denominatorLtOne
      _ = (power * upper)⁻¹ * (power * upper) :=
        (Fraction.Field.inv_mul_cancel _
          denominatorPositive.ne').symm)
end Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale

end
