module
import Purelib.Data.Rat.Fraction.Cast

import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
public import Purelib.NumberTheory.Approximation.Best.Cylinder.Basis
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Parameter
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Transition
import Purelib.NumberTheory.Approximation.Dirichlet.Window.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Field.Defs
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data
open Purelib.Algebra

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Adjacent critical windows at every finite Pell stage

The source constructed for critical stage `k + 1` supports not only its
native consecutive-best window, but also the next critical pair basis at
stage `k + 2`.  The proof transports the next basis through the fixed
unimodular critical-branch transition and applies the uniform two-parameter
finite cylinder theorem.  Every parameter and source remains an explicitly
evaluated rational object at a supplied finite stage.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Tower

/-- The real Gaussian factor given by the next Pell parameter.

Multiplying a lower error by this factor gives its lower error after one critical basis transition. -/
@[expose] def lowerErrorScale (stage : Nat) : Gaussian.Basic.Canonical :=
  ⟨Dirichlet.Critical.Parameter.pellParameter (stage + 1), 0⟩

/-- The next-Pell-parameter lower-error scale has positive quadrance. -/
theorem lowerErrorScale_normSq_pos (stage : Nat) :
    0 < Data.Gaussian.Norm.Basic.normSq
      (Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) := by
  have parameterPositive :
      (0 : Fraction.Rational) <
        Dirichlet.Critical.Parameter.pellParameter (stage + 1) :=
    (show (0 : Fraction.Rational) < 1 / 4 by decide).trans_le
      (Dirichlet.Critical.Parameter.oneFourth_le_pellParameter (stage + 1))
  apply Gaussian.Norm.Basic.normSq_pos
  intro zero
  have realZero := congrArg Gaussian.Basic.re zero
  simp only [Dirichlet.Critical.Adjacent.Tower.lowerErrorScale,
    Gaussian.Basic.zero_re] at realZero
  exact parameterPositive.ne' realZero

/-- The single-parameter critical error ratio is the two-parameter error coordinate at the same rational value. -/
theorem criticalErrorRatio_eq_twoParameter (value : Fraction.Rational) :
    Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio value =
      Dirichlet.Critical.Cylinder.TwoParameter.errorRatio value := by
  rfl

/-- The single-parameter critical denominator ratio is the two-parameter denominator coordinate at the same rational
value. -/
private theorem criticalDenominatorRatio_eq_twoParameter
    (value : Fraction.Rational) :
    Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio value =
      Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio value := by
  rfl

/-- The lower transition coefficients combine to the next Pell parameter as a real Gaussian factor. -/
private theorem lowerCombinationFactor (stage : Nat) :
    GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromLower +
        GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromUpper *
          Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
            (Dirichlet.Critical.Parameter.pellParameter (stage + 1)) =
      Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage := by
  rw [Dirichlet.Critical.Adjacent.Tower.criticalErrorRatio_eq_twoParameter]
  apply Gaussian.Basic.ext <;>
    simp only [Dirichlet.Critical.Adjacent.Tower.lowerErrorScale, Dirichlet.Critical.Transition.lowerFromLower,
      Dirichlet.Critical.Transition.lowerFromUpper,
      GaussianInt.toGaussian,
      Dirichlet.Critical.Cylinder.TwoParameter.errorRatio_re,
      Dirichlet.Critical.Cylinder.TwoParameter.errorRatio_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Ring.IntCast.cast_zero, Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  · calc
      _ = (2 * (1 / 2 : Fraction.Rational)) *
          Dirichlet.Critical.Parameter.pellParameter (stage + 1) := by
        ring1
      _ = Dirichlet.Critical.Parameter.pellParameter (stage + 1) := by
        rw [show (2 : Fraction.Rational) * (1 / 2) = 1 by decide]
        ring1
  · calc
      _ = 1 - 2 * (1 / 2 : Fraction.Rational) := by ring1
      _ = 0 := by
        rw [show (2 : Fraction.Rational) * (1 / 2) = 1 by decide]
        ring1

/-- The upper transition coefficients combine to the lower-error scale times the preceding error ratio. -/
private theorem upperCombinationFactor (stage : Nat) :
    GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromLower +
        GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromUpper *
          Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
            (Dirichlet.Critical.Parameter.pellParameter (stage + 1)) =
      Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage *
        Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
          (Dirichlet.Critical.Parameter.pellParameter stage) := by
  rw [Dirichlet.Critical.Adjacent.Tower.criticalErrorRatio_eq_twoParameter]
  apply Gaussian.Basic.ext
  · simp only [Dirichlet.Critical.Adjacent.Tower.lowerErrorScale, Dirichlet.Critical.Transition.upperFromLower,
      Dirichlet.Critical.Transition.upperFromUpper,
      GaussianInt.toGaussian,
      Dirichlet.Critical.Cylinder.TwoParameter.errorRatio_re,
      Dirichlet.Critical.Cylinder.TwoParameter.errorRatio_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.mul_re,
      Ring.IntCast.cast_zero, Int.cast_ofNat, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    calc
      _ = (-2 + 4 * (1 / 2 : Fraction.Rational)) +
          (1 / 2 : Fraction.Rational) *
            Dirichlet.Critical.Parameter.pellParameter (stage + 1) := by
        ring1
      _ = (1 / 2 : Fraction.Rational) *
          Dirichlet.Critical.Parameter.pellParameter (stage + 1) := by
        rw [show (4 : Fraction.Rational) * (1 / 2) = 2 by decide]
        ring1
      _ = _ := by ring1
  · simp only [Dirichlet.Critical.Adjacent.Tower.lowerErrorScale, Dirichlet.Critical.Transition.upperFromLower,
      Dirichlet.Critical.Transition.upperFromUpper,
      GaussianInt.toGaussian,
      Dirichlet.Critical.Cylinder.TwoParameter.errorRatio_re,
      Dirichlet.Critical.Cylinder.TwoParameter.errorRatio_im,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_im,
      Ring.IntCast.cast_zero, Int.cast_ofNat, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    calc
      _ =
        (1 / 2 : Fraction.Rational) *
          (4 * Dirichlet.Critical.Parameter.pellParameter (stage + 1) - 1) := by
            ring1
      _ = (1 / 2 : Fraction.Rational) *
          (Dirichlet.Critical.Parameter.pellParameter (stage + 1) *
            Dirichlet.Critical.Parameter.pellParameter stage) := by
        rw [Dirichlet.Critical.Transition.four_mul_pellParameter_succ_sub_one]
      _ = Dirichlet.Critical.Parameter.pellParameter (stage + 1) *
          ((1 / 2 : Fraction.Rational) *
            Dirichlet.Critical.Parameter.pellParameter stage) +
          0 * (1 / 2 : Fraction.Rational) := by
        ring1

/-- At the stage-`stage+1` source, the stage-`stage+2` lower error is the old lower error times its transition scale. -/
private theorem next_error_lower (stage : Nat) :
    Best.Error.error
        (Dirichlet.Critical.Pair.criticalSource (stage + 1)).value
        (Dirichlet.Critical.Pair.criticalLowerPair (stage + 2)) =
      Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
        Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage := by
  rw [show stage + 2 = (stage + 1) + 1 by rfl,
    Dirichlet.Critical.Transition.criticalLowerPair_succ,
    Best.Error.error_linearCombination,
    Dirichlet.Critical.Pair.criticalSource_error_lower,
    Dirichlet.Critical.Pair.criticalSource_error_upper]
  calc
    GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromLower *
          Dirichlet.Critical.Pair.criticalLowerError (stage + 1) +
        GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromUpper *
          (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
            Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
              (Dirichlet.Critical.Parameter.pellParameter (stage + 1))) =
      Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
        (GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromLower +
          GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromUpper *
            Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
              (Dirichlet.Critical.Parameter.pellParameter (stage + 1))) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    _ = Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
        Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage := by rw
          [Dirichlet.Critical.Adjacent.Tower.lowerCombinationFactor]

/-- At the stage-`stage+1` source, the stage-`stage+2` upper error is the scaled lower error times the stage-`stage`
error ratio. -/
private theorem next_error_upper (stage : Nat) :
    Best.Error.error
        (Dirichlet.Critical.Pair.criticalSource (stage + 1)).value
        (Dirichlet.Critical.Pair.criticalUpperPair (stage + 2)) =
      (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
          Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) *
        Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
          (Dirichlet.Critical.Parameter.pellParameter stage) := by
  rw [show stage + 2 = (stage + 1) + 1 by rfl,
    Dirichlet.Critical.Transition.criticalUpperPair_succ,
    Best.Error.error_linearCombination,
    Dirichlet.Critical.Pair.criticalSource_error_lower,
    Dirichlet.Critical.Pair.criticalSource_error_upper]
  calc
    GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromLower *
          Dirichlet.Critical.Pair.criticalLowerError (stage + 1) +
        GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromUpper *
          (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
            Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
              (Dirichlet.Critical.Parameter.pellParameter (stage + 1))) =
      Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
        (GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromLower +
          GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromUpper *
            Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
              (Dirichlet.Critical.Parameter.pellParameter (stage + 1))) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    _ = Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
        (Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage *
          Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
            (Dirichlet.Critical.Parameter.pellParameter stage)) := by
      rw [Dirichlet.Critical.Adjacent.Tower.upperCombinationFactor]
    _ = (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
          Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) *
        Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
          (Dirichlet.Critical.Parameter.pellParameter stage) := by
      rw [Gaussian.Basic.mul_assoc]

/-- The next lower denominator is the next upper denominator times its normalized two-parameter ratio. -/
private theorem next_denominator_lower (stage : Nat) :
    GaussianInt.toGaussian
        (Dirichlet.Critical.Pair.criticalLowerPair
          (stage + 2)).denominator =
      GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalUpperPair
            (stage + 2)).denominator *
        Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio
          (Dirichlet.Critical.Parameter.pellParameter (stage + 2)) := by
  have upperNonzero :
      GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalUpperPair
            (stage + 2)).denominator ≠ 0 := by
    intro zero
    exact Dirichlet.Critical.Pair.criticalUpper_denominator_ne_zero
      (stage + 2) (GaussianInt.toGaussian_eq_zero.mp zero)
  have ratioIdentity :=
    Dirichlet.Critical.Pair.criticalPair_denominatorRatio (stage + 2)
  rw [Dirichlet.Critical.Adjacent.Tower.criticalDenominatorRatio_eq_twoParameter] at ratioIdentity
  calc
    GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalLowerPair
            (stage + 2)).denominator =
        Dirichlet.Window.Basic.denominatorRatio
            (Dirichlet.Critical.Pair.criticalLowerPair (stage + 2))
            (Dirichlet.Critical.Pair.criticalUpperPair (stage + 2)) *
          GaussianInt.toGaussian
            (Dirichlet.Critical.Pair.criticalUpperPair
              (stage + 2)).denominator := by
      unfold Dirichlet.Window.Basic.denominatorRatio
      rw [Gaussian.Basic.mul_assoc,
        Gaussian.Field.inv_mul _ upperNonzero,
        Gaussian.Basic.mul_one]
    _ = Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio
          (Dirichlet.Critical.Parameter.pellParameter (stage + 2)) *
        GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalUpperPair
            (stage + 2)).denominator := by
      rw [ratioIdentity]
    _ = GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalUpperPair
            (stage + 2)).denominator *
        Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio
          (Dirichlet.Critical.Parameter.pellParameter (stage + 2)) := by
      rw [Gaussian.Basic.mul_comm]

/-- A next-stage coefficient combination factors through the retained source error and normalized error coordinate.

The source is fixed at `stage+1`, the target basis is at `stage+2`, and the normalized error parameter is at `stage`. -/
private theorem next_error_linearCombination
    (stage : Nat) (left right : GaussianInt) :
    Best.Error.error
        (Dirichlet.Critical.Pair.criticalSource (stage + 1)).value
        (GaussianInt.Pair.LinearCombination.linearCombination
          (Dirichlet.Critical.Pair.criticalLowerPair (stage + 2))
          (Dirichlet.Critical.Pair.criticalUpperPair (stage + 2))
          left right) =
      (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
          Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) *
        Dirichlet.Critical.Cylinder.TwoParameter.normalizedError
          (Dirichlet.Critical.Parameter.pellParameter stage) left right := by
  rw [Best.Error.error_linearCombination, Dirichlet.Critical.Adjacent.Tower.next_error_lower,
    Dirichlet.Critical.Adjacent.Tower.next_error_upper]
  unfold Dirichlet.Critical.Cylinder.TwoParameter.normalizedError
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- A next-stage coefficient combination factors its denominator through the target upper denominator and normalized
coordinate. -/
private theorem next_denominator_linearCombination
    (stage : Nat) (left right : GaussianInt) :
    GaussianInt.toGaussian
        (GaussianInt.Pair.LinearCombination.linearCombination
          (Dirichlet.Critical.Pair.criticalLowerPair (stage + 2))
          (Dirichlet.Critical.Pair.criticalUpperPair (stage + 2))
          left right).denominator =
      GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalUpperPair
            (stage + 2)).denominator *
        Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
          (Dirichlet.Critical.Parameter.pellParameter (stage + 2))
          left right := by
  simp only [GaussianInt.Pair.LinearCombination.linearCombination, GaussianInt.toGaussian_add,
    GaussianInt.toGaussian_mul]
  rw [Dirichlet.Critical.Adjacent.Tower.next_denominator_lower]
  unfold Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- The native critical lower error has positive quadrance at every finite stage. -/
theorem criticalLowerError_normSq_pos (stage : Nat) :
    0 < Data.Gaussian.Norm.Basic.normSq
      (Dirichlet.Critical.Pair.criticalLowerError stage) := by
  have nativeWindow :=
    Dirichlet.Critical.Pair.criticalPairs_areConsecutiveBest stage
  have nativeErrorOrder :
      Best.Error.errorQuadrance
          (Dirichlet.Critical.Pair.criticalSource stage).value
          (Dirichlet.Critical.Pair.criticalUpperPair stage) <
        Best.Error.errorQuadrance
          (Dirichlet.Critical.Pair.criticalSource stage).value
          (Dirichlet.Critical.Pair.criticalLowerPair stage) :=
    nativeWindow.2.1.2.1 _ nativeWindow.1.1 nativeWindow.2.2.1
  rw [← Dirichlet.Critical.Pair.criticalSource_error_lower]
  exact (Gaussian.Norm.Basic.normSq_nonneg _).trans_lt
    nativeErrorOrder

set_option genInjectivity false in
/-- Exact normalized error data for one critical pair basis transported to a
possibly later target stage while retaining one fixed displayed source. -/
structure TransportedNormalForm
    (source : GaussianInt.Fraction) (errorStage targetStage : Nat) where
  /-- The exact Gaussian lower error retained for the fixed source and target basis. -/ lowerError :
    Gaussian.Basic.Canonical
  /-- The retained lower error has strictly positive quadrance. -/ lowerErrorPositive :
    0 < Data.Gaussian.Norm.Basic.normSq lowerError
  /-- The target lower pair has exactly the retained lower error at the fixed source. -/ lowerIdentity :
    Best.Error.error source.value
        (Dirichlet.Critical.Pair.criticalLowerPair targetStage) =
      lowerError
  /-- The target upper error is the retained lower error times the error-stage Pell ratio. -/ upperIdentity :
    Best.Error.error source.value
        (Dirichlet.Critical.Pair.criticalUpperPair targetStage) =
      lowerError * Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
        (Dirichlet.Critical.Parameter.pellParameter errorStage)

constructive_injectivity TransportedNormalForm

/-- The native critical pair is already in transported normal form. -/
@[expose] def nativeNormalForm (stage : Nat) :
    Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm
      (Dirichlet.Critical.Pair.criticalSource stage) stage stage :=
  { lowerError := Dirichlet.Critical.Pair.criticalLowerError stage
    lowerErrorPositive := Dirichlet.Critical.Adjacent.Tower.criticalLowerError_normSq_pos stage
    lowerIdentity :=
      Dirichlet.Critical.Pair.criticalSource_error_lower stage
    upperIdentity := by
      rw [Dirichlet.Critical.Pair.criticalSource_error_upper,
        Dirichlet.Critical.Adjacent.Tower.criticalErrorRatio_eq_twoParameter] }

/-- One fixed critical-branch basis transition moves the normalized error
parameter back by one supplied stage while moving the target basis forward
by one stage. -/
@[expose] def TransportedNormalForm.advance
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm source (errorStage + 1) targetStage) :
    Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm source errorStage (targetStage + 1) := by
  let nextLowerError := normal.lowerError * Dirichlet.Critical.Adjacent.Tower.lowerErrorScale errorStage
  refine
    { lowerError := nextLowerError
      lowerErrorPositive := ?_
      lowerIdentity := ?_
      upperIdentity := ?_ }
  · dsimp only [nextLowerError]
    rw [Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_pos_direct
      normal.lowerErrorPositive (Dirichlet.Critical.Adjacent.Tower.lowerErrorScale_normSq_pos errorStage)
  · rw [Dirichlet.Critical.Transition.criticalLowerPair_succ,
      Best.Error.error_linearCombination, normal.lowerIdentity, normal.upperIdentity]
    change
      GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromLower * normal.lowerError +
          GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromUpper *
            (normal.lowerError *
              Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
                (Dirichlet.Critical.Parameter.pellParameter
                  (errorStage + 1))) =
        nextLowerError
    rw [← Dirichlet.Critical.Adjacent.Tower.criticalErrorRatio_eq_twoParameter]
    calc
      GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromLower * normal.lowerError +
          GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromUpper *
            (normal.lowerError *
              Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
                (Dirichlet.Critical.Parameter.pellParameter
                  (errorStage + 1))) =
        normal.lowerError *
          (GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromLower +
            GaussianInt.toGaussian Dirichlet.Critical.Transition.lowerFromUpper *
              Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
                (Dirichlet.Critical.Parameter.pellParameter
                  (errorStage + 1))) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
      _ = normal.lowerError * Dirichlet.Critical.Adjacent.Tower.lowerErrorScale errorStage := by
        exact congrArg (normal.lowerError * ·)
          (Dirichlet.Critical.Adjacent.Tower.lowerCombinationFactor errorStage)
      _ = nextLowerError := by rfl
  · rw [Dirichlet.Critical.Transition.criticalUpperPair_succ,
      Best.Error.error_linearCombination, normal.lowerIdentity, normal.upperIdentity]
    change
      GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromLower * normal.lowerError +
          GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromUpper *
            (normal.lowerError *
              Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
                (Dirichlet.Critical.Parameter.pellParameter
                  (errorStage + 1))) =
        nextLowerError * Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
          (Dirichlet.Critical.Parameter.pellParameter errorStage)
    rw [← Dirichlet.Critical.Adjacent.Tower.criticalErrorRatio_eq_twoParameter]
    calc
      GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromLower * normal.lowerError +
          GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromUpper *
            (normal.lowerError *
              Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
                (Dirichlet.Critical.Parameter.pellParameter
                  (errorStage + 1))) =
        normal.lowerError *
          (GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromLower +
            GaussianInt.toGaussian Dirichlet.Critical.Transition.upperFromUpper *
              Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
                (Dirichlet.Critical.Parameter.pellParameter
                  (errorStage + 1))) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
      _ = normal.lowerError *
          (Dirichlet.Critical.Adjacent.Tower.lowerErrorScale errorStage *
            Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
              (Dirichlet.Critical.Parameter.pellParameter errorStage)) := by
        exact congrArg (normal.lowerError * ·)
          (Dirichlet.Critical.Adjacent.Tower.upperCombinationFactor errorStage)
      _ = nextLowerError * Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
          (Dirichlet.Critical.Parameter.pellParameter errorStage) := by
        dsimp only [nextLowerError]
        rw [Gaussian.Basic.mul_assoc]

/-- Iterating only a supplied finite number of transitions gives the exact
same-source normal form with the error stage moving backward and the target
stage moving forward. -/
@[expose] def transportedNormalForm (backwardStage steps : Nat) :
    Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm
      (Dirichlet.Critical.Pair.criticalSource (backwardStage + steps))
      backwardStage (backwardStage + 2 * steps) := by
  induction steps generalizing backwardStage with
  | zero =>
      simpa only [Nat.add_zero, Nat.mul_zero] using
        Dirichlet.Critical.Adjacent.Tower.nativeNormalForm backwardStage
  | succ steps inductionHypothesis =>
      have previous := inductionHypothesis (backwardStage + 1)
      have advanced := previous.advance
      have sourceStageIdentity :
          (backwardStage + 1) + steps =
            backwardStage + Nat.succ steps := by
        rw [Nat.succ_eq_add_one]
        ring1
      have targetStageIdentity :
          ((backwardStage + 1) + 2 * steps) + 1 =
            backwardStage + 2 * Nat.succ steps := by
        rw [Nat.succ_eq_add_one]
        ring1
      rw [← sourceStageIdentity, ← targetStageIdentity]
      exact advanced

/-- At any target stage, the lower denominator is the upper denominator multiplied by its normalized ratio. -/
theorem target_denominator_lower (targetStage : Nat) :
    GaussianInt.toGaussian
        (Dirichlet.Critical.Pair.criticalLowerPair
          targetStage).denominator =
      GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalUpperPair
            targetStage).denominator *
        Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio
          (Dirichlet.Critical.Parameter.pellParameter targetStage) := by
  have upperNonzero :
      GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalUpperPair
            targetStage).denominator ≠ 0 := by
    intro zero
    exact Dirichlet.Critical.Pair.criticalUpper_denominator_ne_zero
      targetStage (GaussianInt.toGaussian_eq_zero.mp zero)
  have ratioIdentity :=
    Dirichlet.Critical.Pair.criticalPair_denominatorRatio targetStage
  rw [Dirichlet.Critical.Adjacent.Tower.criticalDenominatorRatio_eq_twoParameter] at ratioIdentity
  calc
    GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalLowerPair
            targetStage).denominator =
        Dirichlet.Window.Basic.denominatorRatio
            (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
            (Dirichlet.Critical.Pair.criticalUpperPair targetStage) *
          GaussianInt.toGaussian
            (Dirichlet.Critical.Pair.criticalUpperPair
              targetStage).denominator := by
      unfold Dirichlet.Window.Basic.denominatorRatio
      rw [Gaussian.Basic.mul_assoc,
        Gaussian.Field.inv_mul _ upperNonzero,
        Gaussian.Basic.mul_one]
    _ = Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio
          (Dirichlet.Critical.Parameter.pellParameter targetStage) *
        GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalUpperPair
            targetStage).denominator := by
      rw [ratioIdentity]
    _ = GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalUpperPair
            targetStage).denominator *
        Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio
          (Dirichlet.Critical.Parameter.pellParameter targetStage) := by
      rw [Gaussian.Basic.mul_comm]

/-- A coefficient combination in the target critical basis factors through
the target upper denominator and its two-parameter normalized coordinate. -/
theorem target_denominator_linearCombination
    (targetStage : Nat) (left right : GaussianInt) :
    GaussianInt.toGaussian
        (GaussianInt.Pair.LinearCombination.linearCombination
          (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
          (Dirichlet.Critical.Pair.criticalUpperPair targetStage)
          left right).denominator =
      GaussianInt.toGaussian
          (Dirichlet.Critical.Pair.criticalUpperPair
            targetStage).denominator *
        Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
          (Dirichlet.Critical.Parameter.pellParameter targetStage)
          left right := by
  simp only [GaussianInt.Pair.LinearCombination.linearCombination, GaussianInt.toGaussian_add,
    GaussianInt.toGaussian_mul]
  rw [Dirichlet.Critical.Adjacent.Tower.target_denominator_lower]
  unfold Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- The embedded upper denominator at any target stage has positive quadrance. -/
private theorem target_upperDenominator_normSq_pos (targetStage : Nat) :
    0 < Data.Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian
        (Dirichlet.Critical.Pair.criticalUpperPair
          targetStage).denominator) := by
  apply Gaussian.Norm.Basic.normSq_pos
  intro zero
  exact Dirichlet.Critical.Pair.criticalUpper_denominator_ne_zero
    targetStage (GaussianInt.toGaussian_eq_zero.mp zero)

/-- A coefficient combination in a transported critical basis factors
through its exact lower error and its two-parameter normalized coordinate. -/
theorem TransportedNormalForm.error_linearCombination
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm source errorStage targetStage)
    (left right : GaussianInt) :
    Best.Error.error source.value
        (GaussianInt.Pair.LinearCombination.linearCombination
          (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
          (Dirichlet.Critical.Pair.criticalUpperPair targetStage)
          left right) =
      normal.lowerError *
        Dirichlet.Critical.Cylinder.TwoParameter.normalizedError
          (Dirichlet.Critical.Parameter.pellParameter errorStage)
          left right := by
  rw [Best.Error.error_linearCombination,
    Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm.lowerIdentity normal,
    Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm.upperIdentity normal]
  unfold Dirichlet.Critical.Cylinder.TwoParameter.normalizedError
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- Every transported finite critical normal form supplies a full global
consecutive-best certificate through the two-parameter cylinder theorem. -/
theorem TransportedNormalForm.strictExteriorCertificate
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm source errorStage targetStage) :
    Best.Cylinder.Basis.StrictExteriorCertificate source.value
      (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
      (Dirichlet.Critical.Pair.criticalUpperPair targetStage) := by
  refine
    { indexOne :=
        Dirichlet.Critical.Pair.criticalPair_indexOne targetStage
      lowerDenominatorNonzero :=
        Dirichlet.Critical.Pair.criticalLower_denominator_ne_zero
          targetStage
      upperDenominatorNonzero :=
        Dirichlet.Critical.Pair.criticalUpper_denominator_ne_zero
          targetStage
      errorOrder := ?_
      denominatorOrder :=
        Dirichlet.Critical.Pair.critical_denominatorQuadrance_ordered
          targetStage
      bothNonzeroExterior := ?_ }
  · unfold Best.Error.errorQuadrance
    rw [normal.lowerIdentity, normal.upperIdentity]
    have ratioStrict :=
      Dirichlet.Critical.Cylinder.TwoParameter.normSq_errorRatio_lt_one
        (Dirichlet.Critical.Parameter.pellParameter_isCritical errorStage)
    calc
      Data.Gaussian.Norm.Basic.normSq
          (normal.lowerError *
            Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
              (Dirichlet.Critical.Parameter.pellParameter errorStage)) =
        Data.Gaussian.Norm.Basic.normSq normal.lowerError *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
              (Dirichlet.Critical.Parameter.pellParameter errorStage)) := by
        rw [Gaussian.Norm.Basic.normSq_mul]
      _ < Data.Gaussian.Norm.Basic.normSq normal.lowerError * 1 :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          normal.lowerErrorPositive ratioStrict
      _ = Data.Gaussian.Norm.Basic.normSq normal.lowerError := by
        ring1
  · intro left right leftNonzero rightNonzero
    rcases Dirichlet.Critical.Cylinder.TwoParameter.strictExterior
        (Dirichlet.Critical.Parameter.pellParameter_isCritical errorStage)
        (Dirichlet.Critical.Parameter.pellParameter_isCritical targetStage)
        left right leftNonzero rightNonzero with
      errorExterior | denominatorExterior
    · left
      unfold Best.Error.errorQuadrance
      rw [normal.lowerIdentity, normal.error_linearCombination]
      calc
        Data.Gaussian.Norm.Basic.normSq normal.lowerError =
            Data.Gaussian.Norm.Basic.normSq normal.lowerError * 1 := by
          ring1
        _ < Data.Gaussian.Norm.Basic.normSq normal.lowerError *
            Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError
                (Dirichlet.Critical.Parameter.pellParameter errorStage)
                left right) :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            normal.lowerErrorPositive errorExterior
        _ = Data.Gaussian.Norm.Basic.normSq
            (normal.lowerError *
              Dirichlet.Critical.Cylinder.TwoParameter.normalizedError
                (Dirichlet.Critical.Parameter.pellParameter errorStage)
                left right) := by
          exact (Gaussian.Norm.Basic.normSq_mul _ _).symm
    · right
      apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
      unfold Best.Error.denominatorQuadrance
      rw [← GaussianInt.normSq_toGaussian, ← GaussianInt.normSq_toGaussian,
        Dirichlet.Critical.Adjacent.Tower.target_denominator_linearCombination]
      calc
        Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
              (Dirichlet.Critical.Pair.criticalUpperPair
                targetStage).denominator) =
          Data.Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian
                (Dirichlet.Critical.Pair.criticalUpperPair
                  targetStage).denominator) * 1 := by
            ring1
        _ < Data.Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian
                (Dirichlet.Critical.Pair.criticalUpperPair
                  targetStage).denominator) *
            Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
                (Dirichlet.Critical.Parameter.pellParameter targetStage)
                left right) :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            (Dirichlet.Critical.Adjacent.Tower.target_upperDenominator_normSq_pos targetStage)
            denominatorExterior
        _ = Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
                (Dirichlet.Critical.Pair.criticalUpperPair
                  targetStage).denominator *
              Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
                (Dirichlet.Critical.Parameter.pellParameter targetStage)
                left right) := by
          rw [Gaussian.Norm.Basic.normSq_mul]

/-- A transported normal form retains a nonzero lower error. -/
private theorem TransportedNormalForm.lowerError_ne_zero
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm source errorStage targetStage) :
    normal.lowerError ≠ 0 := by
  intro zero
  have normZero := congrArg Data.Gaussian.Norm.Basic.normSq zero
  rw [Gaussian.Norm.Basic.normSq_zero] at normZero
  exact (ne_of_gt normal.lowerErrorPositive) normZero

/-- The abstract consecutive-window error ratio is exactly the earlier Pell
parameter carried by the transported normal form. -/
theorem TransportedNormalForm.errorRatio_eq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm source errorStage targetStage) :
    Dirichlet.Window.Basic.errorRatio source.value
        (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
        (Dirichlet.Critical.Pair.criticalUpperPair targetStage) =
      Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
        (Dirichlet.Critical.Parameter.pellParameter errorStage) := by
  unfold Dirichlet.Window.Basic.errorRatio
  rw [normal.lowerIdentity, normal.upperIdentity]
  calc
    (normal.lowerError *
          Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
            (Dirichlet.Critical.Parameter.pellParameter errorStage)) *
        Data.Gaussian.Field.inv normal.lowerError =
      Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
          (Dirichlet.Critical.Parameter.pellParameter errorStage) *
        (normal.lowerError *
          Data.Gaussian.Field.inv normal.lowerError) := by
      rw [Gaussian.Basic.mul_comm normal.lowerError,
        Gaussian.Basic.mul_assoc]
    _ = Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
        (Dirichlet.Critical.Parameter.pellParameter errorStage) * 1 := by
      rw [Gaussian.Field.mul_inv _
        normal.lowerError_ne_zero]
    _ = Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
        (Dirichlet.Critical.Parameter.pellParameter errorStage) := by
      rw [Gaussian.Basic.mul_one]

/-- The denominator ratio at the transported target remains the later Pell
parameter built into that explicit pair basis. -/
theorem transportedDenominatorRatio_eq (targetStage : Nat) :
    Dirichlet.Window.Basic.denominatorRatio
        (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
        (Dirichlet.Critical.Pair.criticalUpperPair targetStage) =
      Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio
        (Dirichlet.Critical.Parameter.pellParameter targetStage) := by
  rw [Dirichlet.Critical.Pair.criticalPair_denominatorRatio,
    Dirichlet.Critical.Adjacent.Tower.criticalDenominatorRatio_eq_twoParameter]

/-- The normalized determinant gap of a transported same-source window is
the exact two-parameter rational gap. -/
theorem TransportedNormalForm.normalizedGap_eq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm source errorStage targetStage) :
    Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio
            (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
            (Dirichlet.Critical.Pair.criticalUpperPair targetStage) *
          Dirichlet.Window.Basic.errorRatio source.value
            (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
            (Dirichlet.Critical.Pair.criticalUpperPair targetStage)) =
      Dirichlet.Critical.Cylinder.TwoParameter.gap
        (Dirichlet.Critical.Parameter.pellParameter errorStage)
        (Dirichlet.Critical.Parameter.pellParameter targetStage) := by
  rw [normal.errorRatio_eq, Dirichlet.Critical.Adjacent.Tower.transportedDenominatorRatio_eq]
  rfl

/-- Exact index-one product identity for every transported finite window. -/
theorem TransportedNormalForm.window_mul_gap_eq_one
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm source errorStage targetStage) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
          (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
          (Dirichlet.Critical.Pair.criticalUpperPair targetStage) *
        Dirichlet.Critical.Cylinder.TwoParameter.gap
          (Dirichlet.Critical.Parameter.pellParameter errorStage)
          (Dirichlet.Critical.Parameter.pellParameter targetStage) = 1 := by
  have consecutive := normal.strictExteriorCertificate.areConsecutiveBest
  have identity :=
    Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindow_mul_normalizedGap_eq_index
      consecutive
  rw [normal.normalizedGap_eq,
    Dirichlet.Critical.Pair.criticalPair_indexOne] at identity
  exact identity

/-- Every transported critical window has quadrance strictly below two.

The strict error-ratio margin puts twice the normalized determinant gap
above one. The exact index-one window-gap product then gives the bound.
-/
theorem TransportedNormalForm.windowQuadrance_lt_two
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
      (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
      (Dirichlet.Critical.Pair.criticalUpperPair targetStage) < 2 := by
  let gap := Dirichlet.Critical.Cylinder.TwoParameter.gap
    (Dirichlet.Critical.Parameter.pellParameter errorStage) (Dirichlet.Critical.Parameter.pellParameter targetStage)
  have errorCertificate := Dirichlet.Critical.Parameter.pellParameter_isCritical errorStage
  have denominatorCertificate := Dirichlet.Critical.Parameter.pellParameter_isCritical targetStage
  have twoLe : (2 : Fraction.Rational) ≤ 2 *
      (1 + Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
          (Dirichlet.Critical.Parameter.pellParameter errorStage))) := by
    calc
      (2 : Fraction.Rational) = 2 * 1 := by ring1
      _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_right (Gaussian.Norm.Basic.normSq_nonneg _)) (by decide)
  have doubledGap : (1 : Fraction.Rational) < 2 * gap := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := (2 : Fraction.Rational)) _ (by decide)
    calc
      (1 : Fraction.Rational) * 2 = 2 := by ring1
      _ < 4 * gap := twoLe.trans_lt
        (Dirichlet.Critical.Cylinder.TwoParameter.error_margin errorCertificate denominatorCertificate)
      _ = (2 * gap) * 2 := by ring1
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := gap) _
    (Dirichlet.Critical.Cylinder.TwoParameter.gap_pos errorCertificate denominatorCertificate)
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
        (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
        (Dirichlet.Critical.Pair.criticalUpperPair targetStage) * gap = 1 := normal.window_mul_gap_eq_one
    _ < 2 * gap := doubledGap

/-- A threshold strictly above the exact transported gap is violated by the
corresponding displayed same-source Dirichlet window. -/
theorem TransportedNormalForm.one_lt_threshold_mul_window
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm source errorStage targetStage)
    (threshold : Fraction.Rational)
    (gapStrict :
      Dirichlet.Critical.Cylinder.TwoParameter.gap
          (Dirichlet.Critical.Parameter.pellParameter errorStage)
          (Dirichlet.Critical.Parameter.pellParameter targetStage) < threshold) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
      (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
      (Dirichlet.Critical.Pair.criticalUpperPair targetStage) := by
  let window := Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
    (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
    (Dirichlet.Critical.Pair.criticalUpperPair targetStage)
  let gap := Dirichlet.Critical.Cylinder.TwoParameter.gap
    (Dirichlet.Critical.Parameter.pellParameter errorStage)
    (Dirichlet.Critical.Parameter.pellParameter targetStage)
  have productIdentity : window * gap = 1 := by
    simpa only [window, gap] using normal.window_mul_gap_eq_one
  have gapNonnegative : (0 : Fraction.Rational) ≤ gap := by
    dsimp only [gap, Dirichlet.Critical.Cylinder.TwoParameter.gap]
    exact Gaussian.Norm.Basic.normSq_nonneg _
  have gapTimesWindowPositive : 0 < gap * window := by
    calc
      (0 : Fraction.Rational) < 1 := by decide
      _ = gap * window := by rw [Fraction.Field.mul_comm,
        productIdentity]
  have windowPositive : 0 < window :=
    Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
      gapTimesWindowPositive gapNonnegative
  calc
    (1 : Fraction.Rational) = gap * window := by
      rw [Fraction.Field.mul_comm, productIdentity]
    _ < threshold * window :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (by simpa only [gap] using gapStrict) windowPositive

/-- Once the earlier error stage lies beyond the explicit sharpness stage,
every later transported denominator stage has gap below the same proposed
sharper threshold. -/
theorem transportedGap_lt_sharperThreshold
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale backwardStage targetStage : Nat)
    (backwardBeyond :
      Dirichlet.Critical.Sharpness.sharpnessStage threshold requestedScale ≤
        backwardStage)
    (targetBeyond : backwardStage ≤ targetStage) :
    Dirichlet.Critical.Cylinder.TwoParameter.gap
        (Dirichlet.Critical.Parameter.pellParameter backwardStage)
        (Dirichlet.Critical.Parameter.pellParameter targetStage) < threshold := by
  let baseStage :=
    Dirichlet.Critical.Sharpness.sharpnessStage threshold requestedScale
  have errorParameterOrder :
      Dirichlet.Critical.Parameter.pellParameter baseStage ≤
        Dirichlet.Critical.Parameter.pellParameter backwardStage :=
    Dirichlet.Critical.Transition.pellParameter_le_of_le backwardBeyond
  have denominatorStageOrder : baseStage ≤ targetStage :=
    backwardBeyond.trans targetBeyond
  have denominatorParameterOrder :
      Dirichlet.Critical.Parameter.pellParameter baseStage ≤
        Dirichlet.Critical.Parameter.pellParameter targetStage :=
    Dirichlet.Critical.Transition.pellParameter_le_of_le denominatorStageOrder
  have mixedGapBound := Dirichlet.Critical.Cylinder.TwoParameter.gap_antitone
    (Dirichlet.Critical.Parameter.pellParameter_isCritical backwardStage)
    (Dirichlet.Critical.Parameter.pellParameter_isCritical baseStage)
    (Dirichlet.Critical.Parameter.pellParameter_isCritical targetStage)
    errorParameterOrder denominatorParameterOrder
  calc
    Dirichlet.Critical.Cylinder.TwoParameter.gap
          (Dirichlet.Critical.Parameter.pellParameter backwardStage)
          (Dirichlet.Critical.Parameter.pellParameter targetStage) ≤
        Dirichlet.Critical.Cylinder.TwoParameter.gap
          (Dirichlet.Critical.Parameter.pellParameter baseStage)
          (Dirichlet.Critical.Parameter.pellParameter baseStage) := mixedGapBound
    _ = Dirichlet.Critical.Cylinder.Basic.criticalGap
        (Dirichlet.Critical.Parameter.pellParameter baseStage) :=
      Dirichlet.Critical.Cylinder.TwoParameter.diagonalGap_eq_criticalGap _
    _ < threshold := by
      simpa only [baseStage] using
        Dirichlet.Critical.Sharpness.criticalGap_lt_sharperThreshold
          certificate requestedScale

/-- An arbitrary supplied finite transport depth yields a genuine
consecutive-best window at the later target stage for one fixed rational
source. -/
theorem transportedPairs_areConsecutiveBest
    (backwardStage steps : Nat) :
    Best.Consecutive.Basic.AreConsecutiveBest
      (Dirichlet.Critical.Pair.criticalSource
        (backwardStage + steps)).value
      (Dirichlet.Critical.Pair.criticalLowerPair
        (backwardStage + 2 * steps))
      (Dirichlet.Critical.Pair.criticalUpperPair
        (backwardStage + 2 * steps)) :=
  (Dirichlet.Critical.Adjacent.Tower.transportedNormalForm backwardStage steps).strictExteriorCertificate
    |>.areConsecutiveBest

/-- The lower error after one basis transition has positive quadrance. -/
private theorem next_lowerError_normSq_pos (stage : Nat) :
    0 < Data.Gaussian.Norm.Basic.normSq
      (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
        Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) := by
  rw [Gaussian.Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Dirichlet.Critical.Adjacent.Tower.criticalLowerError_normSq_pos (stage + 1))
    (Dirichlet.Critical.Adjacent.Tower.lowerErrorScale_normSq_pos stage)

/-- The embedded upper denominator after one basis transition has positive quadrance. -/
private theorem next_upperDenominator_normSq_pos (stage : Nat) :
    0 < Data.Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian
        (Dirichlet.Critical.Pair.criticalUpperPair
          (stage + 2)).denominator) := by
  apply Gaussian.Norm.Basic.normSq_pos
  intro zero
  exact Dirichlet.Critical.Pair.criticalUpper_denominator_ne_zero
    (stage + 2) (GaussianInt.toGaussian_eq_zero.mp zero)

/-- The exact strict-basis certificate for the window immediately after the
native window of a supplied positive critical stage. -/
theorem nextStrictExteriorCertificate (stage : Nat) :
    Best.Cylinder.Basis.StrictExteriorCertificate
      (Dirichlet.Critical.Pair.criticalSource (stage + 1)).value
      (Dirichlet.Critical.Pair.criticalLowerPair (stage + 2))
      (Dirichlet.Critical.Pair.criticalUpperPair (stage + 2)) := by
  refine
    { indexOne :=
        Dirichlet.Critical.Pair.criticalPair_indexOne (stage + 2)
      lowerDenominatorNonzero :=
        Dirichlet.Critical.Pair.criticalLower_denominator_ne_zero
          (stage + 2)
      upperDenominatorNonzero :=
        Dirichlet.Critical.Pair.criticalUpper_denominator_ne_zero
          (stage + 2)
      errorOrder := ?_
      denominatorOrder :=
        Dirichlet.Critical.Pair.critical_denominatorQuadrance_ordered
          (stage + 2)
      bothNonzeroExterior := ?_ }
  · unfold Best.Error.errorQuadrance
    rw [Dirichlet.Critical.Adjacent.Tower.next_error_lower, Dirichlet.Critical.Adjacent.Tower.next_error_upper]
    have ratioStrict :=
      Dirichlet.Critical.Cylinder.TwoParameter.normSq_errorRatio_lt_one
        (Dirichlet.Critical.Parameter.pellParameter_isCritical stage)
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
              Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) *
            Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
              (Dirichlet.Critical.Parameter.pellParameter stage)) =
        Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
              Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
              (Dirichlet.Critical.Parameter.pellParameter stage)) := by
        rw [Gaussian.Norm.Basic.normSq_mul]
      _ < Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
              Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) * 1 :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (Dirichlet.Critical.Adjacent.Tower.next_lowerError_normSq_pos stage) ratioStrict
      _ = Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
            Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) := by ring1
  · intro left right leftNonzero rightNonzero
    rcases Dirichlet.Critical.Cylinder.TwoParameter.strictExterior
        (Dirichlet.Critical.Parameter.pellParameter_isCritical stage)
        (Dirichlet.Critical.Parameter.pellParameter_isCritical
          (stage + 2)) left right leftNonzero rightNonzero with
      errorExterior | denominatorExterior
    · left
      unfold Best.Error.errorQuadrance
      rw [Dirichlet.Critical.Adjacent.Tower.next_error_lower,
        Dirichlet.Critical.Adjacent.Tower.next_error_linearCombination]
      calc
        Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
              Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) =
          Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
                Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) * 1 := by ring1
        _ < Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
                Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) *
            Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError
                (Dirichlet.Critical.Parameter.pellParameter stage)
                left right) :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            (Dirichlet.Critical.Adjacent.Tower.next_lowerError_normSq_pos stage) errorExterior
        _ = Data.Gaussian.Norm.Basic.normSq
            ((Dirichlet.Critical.Pair.criticalLowerError (stage + 1) *
                Dirichlet.Critical.Adjacent.Tower.lowerErrorScale stage) *
              Dirichlet.Critical.Cylinder.TwoParameter.normalizedError
                (Dirichlet.Critical.Parameter.pellParameter stage)
                left right) := by
          exact (Gaussian.Norm.Basic.normSq_mul _ _).symm
    · right
      apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
      unfold Best.Error.denominatorQuadrance
      rw [← GaussianInt.normSq_toGaussian, ← GaussianInt.normSq_toGaussian,
        Dirichlet.Critical.Adjacent.Tower.next_denominator_linearCombination]
      calc
        Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
              (Dirichlet.Critical.Pair.criticalUpperPair
                (stage + 2)).denominator) =
          Data.Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian
                (Dirichlet.Critical.Pair.criticalUpperPair
                  (stage + 2)).denominator) * 1 := by ring1
        _ < Data.Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian
                (Dirichlet.Critical.Pair.criticalUpperPair
                  (stage + 2)).denominator) *
            Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
                (Dirichlet.Critical.Parameter.pellParameter (stage + 2))
                left right) :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            (Dirichlet.Critical.Adjacent.Tower.next_upperDenominator_normSq_pos stage) denominatorExterior
        _ = Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
                (Dirichlet.Critical.Pair.criticalUpperPair
                  (stage + 2)).denominator *
              Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
                (Dirichlet.Critical.Parameter.pellParameter (stage + 2))
                left right) := by
          rw [Gaussian.Norm.Basic.normSq_mul]

/-- The next critical pair basis is a genuine consecutive-best window for
the same rational source as the native window at stage `stage + 1`. -/
theorem nextPairs_areConsecutiveBest (stage : Nat) :
    Best.Consecutive.Basic.AreConsecutiveBest
      (Dirichlet.Critical.Pair.criticalSource (stage + 1)).value
      (Dirichlet.Critical.Pair.criticalLowerPair (stage + 2))
      (Dirichlet.Critical.Pair.criticalUpperPair (stage + 2)) :=
  (Dirichlet.Critical.Adjacent.Tower.nextStrictExteriorCertificate stage).areConsecutiveBest

/-- At every supplied finite stage, one displayed rational source supports
its native critical window and the immediately following, strictly
scale-separated critical window. -/
theorem criticalSource_succ_supports_two_windows (stage : Nat) :
    Best.Consecutive.Basic.AreConsecutiveBest
        (Dirichlet.Critical.Pair.criticalSource (stage + 1)).value
        (Dirichlet.Critical.Pair.criticalLowerPair (stage + 1))
        (Dirichlet.Critical.Pair.criticalUpperPair (stage + 1)) ∧
      Best.Consecutive.Basic.AreConsecutiveBest
        (Dirichlet.Critical.Pair.criticalSource (stage + 1)).value
        (Dirichlet.Critical.Pair.criticalLowerPair (stage + 2))
        (Dirichlet.Critical.Pair.criticalUpperPair (stage + 2)) ∧
      Best.Error.denominatorQuadrance
          (Dirichlet.Critical.Pair.criticalUpperPair (stage + 1)) <
        Best.Error.denominatorQuadrance
          (Dirichlet.Critical.Pair.criticalLowerPair (stage + 2)) :=
  ⟨Dirichlet.Critical.Pair.criticalPairs_areConsecutiveBest (stage + 1),
    Dirichlet.Critical.Adjacent.Tower.nextPairs_areConsecutiveBest stage,
    Dirichlet.Critical.Transition.criticalUpper_lt_nextLower_denominatorQuadrance
      (stage + 1)⟩

/-- Positive-stage form of the adjacent-window theorem, convenient when the
current stage was computed from a threshold and requested scale. -/
theorem criticalSource_supports_next_of_pos
    (currentStage : Nat) (positive : 0 < currentStage) :
    Best.Consecutive.Basic.AreConsecutiveBest
        (Dirichlet.Critical.Pair.criticalSource currentStage).value
        (Dirichlet.Critical.Pair.criticalLowerPair currentStage)
        (Dirichlet.Critical.Pair.criticalUpperPair currentStage) ∧
      Best.Consecutive.Basic.AreConsecutiveBest
        (Dirichlet.Critical.Pair.criticalSource currentStage).value
        (Dirichlet.Critical.Pair.criticalLowerPair (currentStage + 1))
        (Dirichlet.Critical.Pair.criticalUpperPair (currentStage + 1)) ∧
      Best.Error.denominatorQuadrance
          (Dirichlet.Critical.Pair.criticalUpperPair currentStage) <
        Best.Error.denominatorQuadrance
          (Dirichlet.Critical.Pair.criticalLowerPair (currentStage + 1)) := by
  obtain ⟨stage, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simpa only [Nat.succ_eq_add_one] using
    Dirichlet.Critical.Adjacent.Tower.criticalSource_succ_supports_two_windows stage

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Tower

end
