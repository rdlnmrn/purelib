module
public import Purelib.Approximation.Gaussian.Process.Observation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Multiplication
public import Purelib.Approximation.Gaussian.Process.Normalization.Basic
public import Purelib.Data.Gaussian.Constants.Inverse
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Sector

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian.Process.Based

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Process.Normalization.Basic

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

namespace Purelib.Approximation.Gaussian.Process.Gamma.Downscale

/-- Process after one emitted unary-one digit, normalized by multiplication with `gamma⁻¹`. -/
def unaryScaledProcess (source :
  Process) (base : source.State) : Process :=
  mul
    (exact Canonical.gamma⁻¹)
    (Based.based source base)

/-- The initial paired state of the inverse-gamma process and original process rebased at the displayed base. -/
def unaryScaledInitial (source :
  Process) (base : source.State) :
    (unaryScaledProcess source base).State :=
  ((), BasedState.initial source base)

/-- Every later candidate after a unary output is exactly the preceding candidate multiplied by the inverse unary scale.
-/
theorem unaryScaled_candidate_semantics
    (source : Process) (base : source.State)
    {state : (unaryScaledProcess source base).State} {value :
      Canonical}
    (possible : (unaryScaledProcess source base).Possible state value) :
    ∃ sourceValue : Canonical,
      source.Possible base sourceValue ∧
      value = Canonical.gamma⁻¹ * sourceValue := by
  rcases possible with
    ⟨factor, sourceValue, factorPossible, sourcePossible, valueEqual⟩
  exact ⟨sourceValue, state.2.persists sourcePossible,
    valueEqual.trans (congrArg (fun item => item * sourceValue)
      factorPossible)⟩

/-- Half the original base ball's explicit unary candidate lower quadrance. -/
def unaryScaledLower (source :
  Process) (base : source.State) : Fraction.Rational :=
  Ball.Bounds.unaryCandidateLower (source.ball base) / 2

/-- A passing unary test makes the scaled process's retained lower quadrance strictly greater than one. -/
theorem unaryScaledLower_gt_one
    (source : Process) (base : source.State)
    (unary : Large.UnaryBall (source.ball base)) :
    1 < unaryScaledLower source base := by
  apply (Fraction.Order.Field.lt_div_iff_pos
    (by decide : (0 : Fraction.Rational) < 2)).2
  calc
    1 * 2 = 2 := by ring1
    _ < Ball.Bounds.unaryCandidateLower (source.ball base) :=
      Large.unaryCandidateLower_gt_two unary

/-- Uniform candidate lower norm after unary normalization. -/
def unaryScaledPossibleApart
    (source : Process) (base : source.State)
    (_unary : Large.UnaryBall (source.ball base)) :
    Possible.PossibleApart (unaryScaledProcess source base) := by
  exact
    { lowerSq := unaryScaledLower source base
      positive := lt_trans (by decide : (0 : Fraction.Rational) < 1)
        (unaryScaledLower_gt_one source base _unary)
      lower := by
        intro state value possible
        rcases possible with
          ⟨factor, sourceValue, factorPossible, sourcePossible, valueEqual⟩
        have factorEqual : factor = Canonical.gamma⁻¹ := factorPossible
        have sourceAtBase : source.Possible base sourceValue :=
          state.2.persists sourcePossible
        have sourceLower := Ball.Bounds.unaryCandidateLower_le
          (source.possible_inside sourceAtBase)
        rw [valueEqual, factorEqual, Basic.normSq_mul, Inverse.normSq_gamma_inv]
        change Ball.Bounds.unaryCandidateLower (source.ball base) / 2 ≤
          (1 / 2 : Fraction.Rational) * Basic.normSq sourceValue
        have halfIdentity : (1 / 2 : Fraction.Rational) * Basic.normSq sourceValue =
            Basic.normSq sourceValue / 2 := by
          change (1 * (2 : Fraction.Rational)⁻¹) * Basic.normSq sourceValue =
            Basic.normSq sourceValue * (2 : Fraction.Rational)⁻¹
          calc
            (1 * (2 : Fraction.Rational)⁻¹) * Basic.normSq sourceValue =
                (2 : Fraction.Rational)⁻¹ * Basic.normSq sourceValue := by
              rw [_root_.one_mul]
            _ = Basic.normSq sourceValue * (2 : Fraction.Rational)⁻¹ :=
              Fraction.Field.mul_comm _ _
        rw [halfIdentity]
        apply (Fraction.Order.Field.div_le_iff_pos
          (by decide : (0 : Fraction.Rational) < 2)).2
        calc
          Ball.Bounds.unaryCandidateLower (source.ball base) ≤ Basic.normSq sourceValue :=
            sourceLower
          _ = (Basic.normSq sourceValue / 2) * 2 :=
            (Fraction.Field.div_mul_cancel_of_ne
              (Basic.normSq sourceValue) 2 (by decide)).symm }

/-- Build the scaled process's loop-domain certificate from its original unary test and retained lower quadrance. -/
def unaryScaledLoopDomain
    (source : Process) (base : source.State)
    (unary : Large.UnaryBall (source.ball base)) :
    LoopDomain (unaryScaledProcess
      source base) :=
  LoopDomain.ofLower (unaryScaledPossibleApart source base unary)
    (unaryScaledLower_gt_one source base unary)
namespace unaryScaledLoopDomain

/-- Build the original unary loop domain from its same retained numerical observation.

The lower quadrance and triangle weight use the exact cached ball. All bounds
retain the original process, base and unary certificate; their proof fields
perform no further source observation.
-/
def ofObservation (source : Process) (base : source.State) (observation : Process.Observation source base)
    (unary : Large.UnaryBall (source.ball base)) : LoopDomain (unaryScaledProcess source base) := by
  let lower := Ball.Bounds.unaryCandidateLower observation.ball / 2
  have lowerEq : lower = unaryScaledLower source base :=
    congrArg (fun ball => Ball.Bounds.unaryCandidateLower ball / 2) observation.ballEq
  let apart : Possible.PossibleApart (unaryScaledProcess source base) :=
    { lowerSq := lower
      positive := lowerEq.symm ▸ (unaryScaledPossibleApart source base unary).positive
      lower := by
        intro state value possible
        exact lowerEq.symm ▸ (unaryScaledPossibleApart source base unary).lower state possible }
  have aboveOne : 1 < apart.lowerSq := by
    change 1 < lower
    exact lowerEq.symm ▸ unaryScaledLower_gt_one source base unary
  exact LoopDomain.ofLower apart aboveOne

/-- Reusing the retained observation preserves the original complete unary loop-domain record. -/
theorem ofObservation_eq (source : Process) (base : source.State) (observation : Process.Observation source base)
    (unary : Large.UnaryBall (source.ball base)) :
    ofObservation source base observation unary = unaryScaledLoopDomain source base unary := by
  rcases observation with ⟨ball, ballEq, witness, witnessEq, generic, genericEq⟩
  cases ballEq
  rfl

end unaryScaledLoopDomain

end Purelib.Approximation.Gaussian.Process.Gamma.Downscale

end
