module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Division
public import Purelib.Approximation.Gaussian.Process.Normalization.Basic
public import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Constants
public import Purelib.Data.Gaussian.Constants.Inverse
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.ComplexContinuedFraction.Encoding (Sector)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Sector

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian.Process.Based

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Process.Normalization.Basic

open Purelib.Approximation.Gaussian.Process.Sector

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.Gaussian.Constants

open Purelib.Data.Rat

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

namespace Purelib.Approximation.Gaussian.Process.Sector.Inverse

/-- Exact affine inverse tail `gamma⁻¹ / residual`. -/
def inverseTailProcess
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (residualBase : (Residual.residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((Residual.residualProcess source base sector).ball residualBase)) : Approximation.Gaussian.Process :=
  let denominator :=
    Residual.apartResidualFuture source base sector residualBase certificate
  Approximation.Gaussian.Process.div
    (Approximation.Gaussian.Process.exact Canonical.gamma⁻¹)
    denominator
    (Preparation.apartifyApart
      (Residual.residualFuturePossibleApart source base sector residualBase certificate))

/-- Explicit initial state of the inverse-tail process. -/
def inverseTailInitial
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (residualBase : (Residual.residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((Residual.residualProcess source base sector).ball residualBase)) :
    (inverseTailProcess source base sector residualBase certificate).State
      :=
  let possibleApart :=
    Residual.residualFuturePossibleApart source base sector residualBase certificate
  ((), Preparation.prepareApartState possibleApart
    (BasedState.initial (Residual.residualProcess source base sector) residualBase))

/-- Uniform lower norm of every affine inverse-tail candidate. -/
def inverseTailLower
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector) : Fraction.Rational :=
  1 / (2 * Residual.safeResidualUpper sector (source.ball base))

/-- The retained inverse-tail lower squared norm is positive when the residual has certified apartness. -/
theorem inverseTailLower_pos
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (safe : Safe.SafeBall sector (source.ball base))
    (residualBase : (Residual.residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((Residual.residualProcess source base sector).ball residualBase)) :
    0 < inverseTailLower source base sector := by
  apply Fraction.Order.Field.div_pos_direct (by decide)
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Residual.safeResidualUpper_pos_of_apart source base sector safe residualBase
      certificate)

/-- The safe-sector residual bound makes the retained inverse-tail lower squared norm strictly greater than one. -/
theorem inverseTailLower_gt_one
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (safe : Safe.SafeBall sector (source.ball base))
    (residualBase : (Residual.residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((Residual.residualProcess source base sector).ball residualBase)) :
    1 < inverseTailLower source base sector := by
  let upper := Residual.safeResidualUpper sector (source.ball base)
  have upperPositive : 0 < upper :=
    Residual.safeResidualUpper_pos_of_apart source base sector safe residualBase
      certificate
  have denominatorPositive : 0 < 2 * upper :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) upperPositive
  apply (Fraction.Order.Field.lt_div_iff_pos denominatorPositive).2
  calc
    1 * (2 * upper) = 2 * upper := by ring1
    _ < 1 := by
      have half := Residual.safeResidualUpper_lt_half safe
      have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide : (0 : Fraction.Rational) < 2) half
      calc
        2 * upper < 2 * (1 / 2) := scaled
        _ = 1 := by
          calc
            2 * (1 / 2 : Fraction.Rational) = (1 / 2) * 2 :=
              Fraction.Field.mul_comm _ _
            _ = 1 :=
              Fraction.Field.div_mul_cancel_of_ne 1 2 (by decide)

/-- Every candidate of the inverse-tail process has one uniform rational lower norm strictly above one. -/
def inverseTailPossibleApart
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (safe : Safe.SafeBall sector (source.ball base))
    (residualBase : (Residual.residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((Residual.residualProcess source base sector).ball residualBase)) :
    Possible.PossibleApart
      (inverseTailProcess source base sector residualBase certificate) :=
        by
  let residualFuture :=
    Residual.apartResidualFuture source base sector residualBase certificate
  let residualApart :=
    Residual.residualFuturePossibleApart source base sector residualBase certificate
  exact
    { lowerSq := inverseTailLower source base sector
      positive := inverseTailLower_pos source base sector safe
        residualBase
        certificate
      lower := by
        intro state value possible
        rcases possible with
          ⟨numerator, residual, numeratorPossible, residualPossible, valueEqual⟩
        have numeratorEqual : numerator = Canonical.gamma⁻¹ := numeratorPossible
        have residualUpper : Data.Gaussian.Norm.Basic.normSq residual ≤
            Residual.safeResidualUpper sector (source.ball base) :=
          Residual.apartResidualFuture_norm_le_upper source base sector safe
            residualBase certificate residualPossible
        have residualLower := residualApart.lower state.2.source residualPossible
        have residualNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq residual :=
          residualApart.positive.trans_le residualLower
        have residualNonzero : residual ≠ 0 := by
          intro residualZero
          rw [residualZero, Data.Gaussian.Norm.Basic.normSq_zero] at residualNormPositive
          exact (lt_irrefl _ residualNormPositive).elim
        have halfInverse (value : Fraction.Rational) :
            (1 / 2 : Fraction.Rational) * value⁻¹ = 1 / (2 * value) := by
          have oneDiv : (1 / value : Fraction.Rational) = value⁻¹ := by
            change 1 * value⁻¹ = value⁻¹
            exact Fraction.Field.one_mul _
          rw [← oneDiv, Fraction.Field.div_mul_div_direct,
            Fraction.Field.mul_one_direct]
        rw [valueEqual, numeratorEqual,
          Data.Gaussian.Field.normSq_div _ _ residualNonzero, Inverse.normSq_gamma_inv,
          halfInverse]
        apply Fraction.Order.Field.div_le_div_of_nonneg_left_direct
          (by decide : (0 : Fraction.Rational) ≤ 1)
          (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
            residualNormPositive)
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          residualUpper (by decide) }

/-- The inverse tail therefore supplies the semantically natural loop domain needed by the total redundant decision. -/
def inverseTailLoopDomain
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (safe : Safe.SafeBall sector (source.ball base))
    (residualBase : (Residual.residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((Residual.residualProcess source base sector).ball residualBase)) :
    Gaussian.Process.Normalization.Basic.LoopDomain (inverseTailProcess
      source base sector residualBase certificate) :=
  LoopDomain.ofLower
    (inverseTailPossibleApart source base sector safe residualBase
      certificate)
    (inverseTailLower_gt_one source base sector safe residualBase
      certificate)

/-- Every later inverse-tail candidate is the exact inverse chart of a nonzero residual candidate already admitted at
the selected residual base. -/
theorem inverseTail_candidate_semantics
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (residualBase : (Residual.residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((Residual.residualProcess source base sector).ball residualBase))
    {state : (inverseTailProcess source base sector residualBase
      certificate).State} {tail : Canonical}
    (possible : (inverseTailProcess source base sector residualBase
      certificate).Possible state tail) :
    ∃ residual : Canonical,
      (Residual.residualProcess source base sector).Possible residualBase residual ∧
      residual ≠ 0 ∧ tail = (Canonical.gamma * residual)⁻¹ := by
  let residualApart :=
    Residual.residualFuturePossibleApart source base sector residualBase certificate
  rcases possible with
    ⟨numerator, residual, numeratorPossible, residualPossible, tailEqual⟩
  have residualAtBase :
      (Residual.residualProcess source base sector).Possible residualBase residual :=
    state.2.source.persists residualPossible
  have residualLower := residualApart.lower state.2.source residualPossible
  have residualNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq residual :=
    residualApart.positive.trans_le residualLower
  have residualNonzero : residual ≠ 0 := by
    intro residualZero
    rw [residualZero, Data.Gaussian.Norm.Basic.normSq_zero] at residualNormPositive
    exact (lt_irrefl _ residualNormPositive).elim
  refine ⟨residual, residualAtBase, residualNonzero, ?_⟩
  calc
    tail = numerator / residual := tailEqual
    _ = Canonical.gamma⁻¹ / residual := by rw [numeratorPossible]
    _ = (Canonical.gamma * residual)⁻¹ :=
      Inverse.gamma_inv_div_eq_inverse residual residualNonzero
end Purelib.Approximation.Gaussian.Process.Sector.Inverse

end
