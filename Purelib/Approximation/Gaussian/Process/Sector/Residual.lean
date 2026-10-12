module
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
public import Purelib.Approximation.Gaussian.Process.Apart.Based
import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Translation
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.ComplexContinuedFraction.Encoding (Sector)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Sector

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian.Process.Based

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.Gaussian.Norm

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

namespace Purelib.Approximation.Gaussian.Process.Sector.Residual

/-! ## A safe emitted sector gives a persistent residual chart -/

/-- Rational uniform residual upper bound already contained in a safe-ball certificate. -/
def safeResidualUpper (sector :
  Sector)
    (ball : Approximation.Gaussian.Enclosure.Ball) : Fraction.Rational :=
  16 * ball.radiusSq +
    (16 / 15) * Data.Gaussian.Norm.Basic.normSq (ball.center - sector.rep)

/-- A safe-sector certificate bounds the retained residual upper quadrance strictly below one half. -/
theorem safeResidualUpper_lt_half
    {sector : Sector} {ball : Approximation.Gaussian.Enclosure.Ball}
    (safe : Safe.SafeBall sector ball) :
    safeResidualUpper sector ball < 1 / 2 :=
  safe

/-- Every admitted candidate of the rebased residual process satisfies the same explicit upper bound as the ball on
which the sector was emitted. -/
theorem translated_based_norm_le_safeResidualUpper
    (process : Approximation.Gaussian.Process) (base : process.State)
    (sector : Sector)
    (_safe : Safe.SafeBall sector (process.ball base))
    {state : (Gaussian.Process.Translation.translate (Gaussian.Process.Based.based process base) sector.rep).State}
    {residual : Data.Gaussian.Basic.Canonical}
    (possible : (Gaussian.Process.Translation.translate (Gaussian.Process.Based.based process base) sector.rep).Possible
      state residual) :
    Data.Gaussian.Norm.Basic.normSq residual ≤ safeResidualUpper
      sector (process.ball base) := by
  rcases possible with ⟨sourceValue, sourcePossible, residualEqual⟩
  have basePossible : process.Possible base sourceValue :=
    state.persists sourcePossible
  have inside := process.possible_inside basePossible
  have difference :
      sourceValue - sector.rep =
        (sourceValue - (process.ball base).center) +
          ((process.ball base).center - sector.rep) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  rw [residualEqual, difference]
  exact (Weighted.normSq_add_le_weighted _ _).trans
    (add_le_add
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        inside (by decide)) le_rfl)

/-- Residual process after emitting a safe sector at one finite source state. -/
def residualProcess (source :
  Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector) : Approximation.Gaussian.Process :=
  Gaussian.Process.Translation.translate (Gaussian.Process.Based.based source base) sector.rep

/-- Retain the original base state as the initial state of the sector-translated residual process. -/
def residualInitial (source :
  Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector) :
    (residualProcess source base sector).State :=
  BasedState.initial source base

/-- Candidate apartness inherited from a residual ball on which the small-or-apart controller selected its apart branch.
-/
def residualFuturePossibleApart
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (residualBase : (residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((residualProcess source base sector).ball residualBase)) :
    Possible.PossibleApart (Gaussian.Process.Based.based (residualProcess
      source base sector) residualBase) :=
  Based.possibleApartOfBall _ _ certificate

/-- Apartified residual future used as the denominator of the exact inverse chart. -/
def apartResidualFuture
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (residualBase : (residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((residualProcess source base sector).ball residualBase)) :
        Approximation.Gaussian.Process :=
  Preparation.apartify
    (residualFuturePossibleApart source base sector residualBase
      certificate)

/-- The original safe-sector upper bound persists through rebasing and apartification of the residual process. -/
theorem apartResidualFuture_norm_le_upper
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (safe : Safe.SafeBall sector (source.ball base))
    (residualBase : (residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((residualProcess source base sector).ball residualBase))
    {state : (apartResidualFuture source base sector residualBase
      certificate).State} {residual : Data.Gaussian.Basic.Canonical}
    (possible : (apartResidualFuture source base sector residualBase
      certificate).Possible state residual) :
    Data.Gaussian.Norm.Basic.normSq residual ≤ safeResidualUpper
      sector (source.ball base) := by
  apply translated_based_norm_le_safeResidualUpper source base sector
    safe
  exact state.source.persists possible

/-- An apart residual ball forces the original safe-sector upper quadrance bound to be strictly positive. -/
theorem safeResidualUpper_pos_of_apart
    (source : Approximation.Gaussian.Process) (base : source.State)
    (sector : Sector)
    (safe : Safe.SafeBall sector (source.ball base))
    (residualBase : (residualProcess source base sector).State)
    (certificate : Ball.Apart
      ((residualProcess source base sector).ball residualBase)) :
    0 < safeResidualUpper sector (source.ball base) := by
  rcases (residualProcess source base sector).witness residualBase with
    ⟨residual, possible⟩
  have residualLower := certificate.lower
    ((residualProcess source base sector).possible_inside possible)
  have residualUpper :=
    translated_based_norm_le_safeResidualUpper source base sector safe
      possible
  exact certificate.positive.trans_le (residualLower.trans residualUpper)
end Purelib.Approximation.Gaussian.Process.Sector.Residual

end
