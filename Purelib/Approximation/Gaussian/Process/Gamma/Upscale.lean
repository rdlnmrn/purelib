module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Multiplication
public import Purelib.Approximation.Gaussian.Process.Normalization.Basic
public import Purelib.Approximation.Rational.Geometric.Upscale
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian.Process.Based

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Process.Normalization.Basic

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Gaussian

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

namespace Purelib.Approximation.Gaussian.Process.Gamma.Upscale

/-- Scale a based process upward by an exact natural power of `gamma`. -/
def upscaledProcess (source :
  Approximation.Gaussian.Process) (base : source.State)
    (exponent : Nat) : Approximation.Gaussian.Process :=
  Approximation.Gaussian.Process.mul
    (Approximation.Gaussian.Process.exact
      (Power.natPow Canonical.gamma exponent))
    (Gaussian.Process.Based.based source base)

/-- Pair the exact scaling process's unit state with the original base as its initial based state. -/
def upscaledInitial (source :
  Approximation.Gaussian.Process) (base : source.State)
    (exponent : Nat) : (upscaledProcess source base exponent).State :=
  ((), BasedState.initial source base)

/-- Every later initial-low candidate is the exact upward rescaling of one candidate admitted at the retained original
state. -/
theorem upscaled_candidate_semantics
    (source : Approximation.Gaussian.Process) (base : source.State) (exponent : Nat)
    {state : (upscaledProcess source base exponent).State} {value :
      Canonical}
    (possible : (upscaledProcess source base exponent).Possible state
      value) :
    ∃ sourceValue : Canonical,
      source.Possible base sourceValue ∧
      value = Power.natPow Canonical.gamma exponent * sourceValue := by
  rcases possible with
    ⟨factor, sourceValue, factorPossible, sourcePossible, valueEqual⟩
  exact ⟨sourceValue, state.2.persists sourcePossible,
    valueEqual.trans (congrArg (fun item => item * sourceValue)
      factorPossible)⟩

/-- Transport the original base ball's apartness to the gamma-power-scaled process.

The retained lower quadrance is multiplied by the displayed power of two and applies to every possible scaled reading.
-/
def upscaledPossibleApart
    (source : Approximation.Gaussian.Process) (base : source.State)
    (certificate : Ball.Apart
      (source.ball base)) (exponent : Nat) :
    Possible.PossibleApart (upscaledProcess source base exponent) := by
  exact
    { lowerSq := (2 : Fraction.Rational) ^ exponent * certificate.lowerSq
      positive := Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Order.Arithmetic.pow_pos_direct (by decide) exponent)
        certificate.positive
      lower := by
        intro state value possible
        rcases possible with
          ⟨factor, sourceValue, factorPossible, sourcePossible, valueEqual⟩
        have sourceAtBase : source.Possible base sourceValue :=
          state.2.persists sourcePossible
        have sourceLower := certificate.lower
          (source.possible_inside sourceAtBase)
        rw [valueEqual, factorPossible, Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_natPow,
          Constants.normSq_gamma]
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          sourceLower
          (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) exponent) }

/-- Compute a gamma scaling exponent from the original apartness lower quadrance and certify the scaled loop domain. -/
def upscaledLoopDomain
    (source : Approximation.Gaussian.Process) (base : source.State)
    (certificate : Ball.Apart
      (source.ball base)) :
    Gaussian.Process.Normalization.Basic.LoopDomain
      (upscaledProcess source base (Upscale.upscaleExponent
        certificate.lowerSq)) :=
  let apart := upscaledPossibleApart source base certificate
    (Upscale.upscaleExponent certificate.lowerSq)
  LoopDomain.ofLower apart (Upscale.upscaleExponent_lower certificate.positive)

/-- Certify the loop domain after a retained prior gamma-power prefix followed by the computed apartness scaling
exponent. -/
def upscaledLoopDomainWithPrefix
    (source : Approximation.Gaussian.Process) (base : source.State)
    (certificate : Ball.Apart
      (source.ball base)) (priorCount : Nat) :
    Gaussian.Process.Normalization.Basic.LoopDomain (upscaledProcess source
      base
      (priorCount + Upscale.upscaleExponent certificate.lowerSq)) :=
  let apart := upscaledPossibleApart source base certificate
    (priorCount + Upscale.upscaleExponent certificate.lowerSq)
  LoopDomain.ofLower apart
    (Upscale.upscaledPrefix_lower priorCount certificate.positive)

end Purelib.Approximation.Gaussian.Process.Gamma.Upscale

end
