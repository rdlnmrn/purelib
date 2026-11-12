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

open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.GaussianInt.Pair

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
  ⟨Parameter.pellParameter (stage + 1), 0⟩

/-- The next-Pell-parameter lower-error scale has positive quadrance. -/
theorem lowerErrorScale_normSq_pos (stage : Nat) :
    0 < Gaussian.Norm.Basic.normSq
      (lowerErrorScale stage) := by
  have parameterPositive :
      (0 : Fraction.Rational) <
        Parameter.pellParameter (stage + 1) :=
    (show (0 : Fraction.Rational) < 1 / 4 by decide).trans_le
      (Parameter.oneFourth_le_pellParameter (stage + 1))
  apply Gaussian.Norm.Basic.normSq_pos
  intro zero
  have realZero := congrArg Gaussian.Basic.re zero
  simp only [lowerErrorScale,
    Gaussian.Basic.zero_re] at realZero
  exact parameterPositive.ne' realZero

/-- The single-parameter critical error ratio is the two-parameter error coordinate at the same rational value. -/
theorem criticalErrorRatio_eq_twoParameter (value : Fraction.Rational) :
    Cylinder.Basic.criticalErrorRatio value =
      Cylinder.TwoParameter.errorRatio value := by
  rfl

/-- The single-parameter critical denominator ratio is the two-parameter denominator coordinate at the same rational
value. -/
private theorem criticalDenominatorRatio_eq_twoParameter
    (value : Fraction.Rational) :
    Cylinder.Basic.criticalDenominatorRatio value =
      Cylinder.TwoParameter.denominatorRatio value := by
  rfl

/-- The lower transition coefficients combine to the next Pell parameter as a real Gaussian factor. -/
private theorem lowerCombinationFactor (stage : Nat) :
    GaussianInt.toGaussian Transition.lowerFromLower +
        GaussianInt.toGaussian Transition.lowerFromUpper *
          Cylinder.Basic.criticalErrorRatio
            (Parameter.pellParameter (stage + 1)) =
      lowerErrorScale stage := by
  rw [criticalErrorRatio_eq_twoParameter]
  apply Gaussian.Basic.ext <;>
    simp only [lowerErrorScale, Transition.lowerFromLower,
      Transition.lowerFromUpper,
      GaussianInt.toGaussian,
      Cylinder.TwoParameter.errorRatio_re,
      Cylinder.TwoParameter.errorRatio_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Ring.IntCast.cast_zero, Int.cast_one, ← Fraction.Cast.intCast_eq_fromInt]
  · calc
      _ = (2 * (1 / 2 : Fraction.Rational)) *
          Parameter.pellParameter (stage + 1) := by
        ring1
      _ = Parameter.pellParameter (stage + 1) := by
        rw [show (2 : Fraction.Rational) * (1 / 2) = 1 by decide]
        ring1
  · calc
      _ = 1 - 2 * (1 / 2 : Fraction.Rational) := by ring1
      _ = 0 := by
        rw [show (2 : Fraction.Rational) * (1 / 2) = 1 by decide]
        ring1

/-- The upper transition coefficients combine to the lower-error scale times the preceding error ratio. -/
private theorem upperCombinationFactor (stage : Nat) :
    GaussianInt.toGaussian Transition.upperFromLower +
        GaussianInt.toGaussian Transition.upperFromUpper *
          Cylinder.Basic.criticalErrorRatio
            (Parameter.pellParameter (stage + 1)) =
      lowerErrorScale stage *
        Cylinder.TwoParameter.errorRatio
          (Parameter.pellParameter stage) := by
  rw [criticalErrorRatio_eq_twoParameter]
  apply Gaussian.Basic.ext
  · simp only [lowerErrorScale, Transition.upperFromLower,
      Transition.upperFromUpper,
      GaussianInt.toGaussian,
      Cylinder.TwoParameter.errorRatio_re,
      Cylinder.TwoParameter.errorRatio_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.mul_re,
      Ring.IntCast.cast_zero, Int.cast_ofNat, ← Fraction.Cast.intCast_eq_fromInt]
    calc
      _ = (-2 + 4 * (1 / 2 : Fraction.Rational)) +
          (1 / 2 : Fraction.Rational) *
            Parameter.pellParameter (stage + 1) := by
        ring1
      _ = (1 / 2 : Fraction.Rational) *
          Parameter.pellParameter (stage + 1) := by
        rw [show (4 : Fraction.Rational) * (1 / 2) = 2 by decide]
        ring1
      _ = _ := by ring1
  · simp only [lowerErrorScale, Transition.upperFromLower,
      Transition.upperFromUpper,
      GaussianInt.toGaussian,
      Cylinder.TwoParameter.errorRatio_re,
      Cylinder.TwoParameter.errorRatio_im,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_im,
      Ring.IntCast.cast_zero, Int.cast_ofNat, ← Fraction.Cast.intCast_eq_fromInt]
    calc
      _ =
        (1 / 2 : Fraction.Rational) *
          (4 * Parameter.pellParameter (stage + 1) - 1) := by
            ring1
      _ = (1 / 2 : Fraction.Rational) *
          (Parameter.pellParameter (stage + 1) *
            Parameter.pellParameter stage) := by
        rw [Transition.four_mul_pellParameter_succ_sub_one]
      _ = Parameter.pellParameter (stage + 1) *
          ((1 / 2 : Fraction.Rational) *
            Parameter.pellParameter stage) +
          0 * (1 / 2 : Fraction.Rational) := by
        ring1

/-- At the stage-`stage+1` source, the stage-`stage+2` lower error is the old lower error times its transition scale. -/
private theorem next_error_lower (stage : Nat) :
    Best.Error.error
        (Pair.criticalSource (stage + 1)).value
        (Pair.criticalLowerPair (stage + 2)) =
      Pair.criticalLowerError (stage + 1) *
        lowerErrorScale stage := by
  rw [show stage + 2 = (stage + 1) + 1 by rfl,
    Transition.criticalLowerPair_succ,
    Best.Error.error_linearCombination,
    Pair.criticalSource_error_lower,
    Pair.criticalSource_error_upper]
  calc
    GaussianInt.toGaussian Transition.lowerFromLower *
          Pair.criticalLowerError (stage + 1) +
        GaussianInt.toGaussian Transition.lowerFromUpper *
          (Pair.criticalLowerError (stage + 1) *
            Cylinder.Basic.criticalErrorRatio
              (Parameter.pellParameter (stage + 1))) =
      Pair.criticalLowerError (stage + 1) *
        (GaussianInt.toGaussian Transition.lowerFromLower +
          GaussianInt.toGaussian Transition.lowerFromUpper *
            Cylinder.Basic.criticalErrorRatio
              (Parameter.pellParameter (stage + 1))) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    _ = Pair.criticalLowerError (stage + 1) *
        lowerErrorScale stage := by rw
          [lowerCombinationFactor]

/-- At the stage-`stage+1` source, the stage-`stage+2` upper error is the scaled lower error times the stage-`stage`
error ratio. -/
private theorem next_error_upper (stage : Nat) :
    Best.Error.error
        (Pair.criticalSource (stage + 1)).value
        (Pair.criticalUpperPair (stage + 2)) =
      (Pair.criticalLowerError (stage + 1) *
          lowerErrorScale stage) *
        Cylinder.TwoParameter.errorRatio
          (Parameter.pellParameter stage) := by
  rw [show stage + 2 = (stage + 1) + 1 by rfl,
    Transition.criticalUpperPair_succ,
    Best.Error.error_linearCombination,
    Pair.criticalSource_error_lower,
    Pair.criticalSource_error_upper]
  calc
    GaussianInt.toGaussian Transition.upperFromLower *
          Pair.criticalLowerError (stage + 1) +
        GaussianInt.toGaussian Transition.upperFromUpper *
          (Pair.criticalLowerError (stage + 1) *
            Cylinder.Basic.criticalErrorRatio
              (Parameter.pellParameter (stage + 1))) =
      Pair.criticalLowerError (stage + 1) *
        (GaussianInt.toGaussian Transition.upperFromLower +
          GaussianInt.toGaussian Transition.upperFromUpper *
            Cylinder.Basic.criticalErrorRatio
              (Parameter.pellParameter (stage + 1))) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    _ = Pair.criticalLowerError (stage + 1) *
        (lowerErrorScale stage *
          Cylinder.TwoParameter.errorRatio
            (Parameter.pellParameter stage)) := by
      rw [upperCombinationFactor]
    _ = (Pair.criticalLowerError (stage + 1) *
          lowerErrorScale stage) *
        Cylinder.TwoParameter.errorRatio
          (Parameter.pellParameter stage) := by
      rw [Gaussian.Basic.mul_assoc]

/-- The next lower denominator is the next upper denominator times its normalized two-parameter ratio. -/
private theorem next_denominator_lower (stage : Nat) :
    GaussianInt.toGaussian
        (Pair.criticalLowerPair
          (stage + 2)).denominator =
      GaussianInt.toGaussian
          (Pair.criticalUpperPair
            (stage + 2)).denominator *
        Cylinder.TwoParameter.denominatorRatio
          (Parameter.pellParameter (stage + 2)) := by
  have upperNonzero :
      GaussianInt.toGaussian
          (Pair.criticalUpperPair
            (stage + 2)).denominator ≠ 0 := by
    intro zero
    exact Pair.criticalUpper_denominator_ne_zero
      (stage + 2) (GaussianInt.toGaussian_eq_zero.mp zero)
  have ratioIdentity :=
    Pair.criticalPair_denominatorRatio (stage + 2)
  rw [criticalDenominatorRatio_eq_twoParameter] at ratioIdentity
  calc
    GaussianInt.toGaussian
          (Pair.criticalLowerPair
            (stage + 2)).denominator =
        Window.Basic.denominatorRatio
            (Pair.criticalLowerPair (stage + 2))
            (Pair.criticalUpperPair (stage + 2)) *
          GaussianInt.toGaussian
            (Pair.criticalUpperPair
              (stage + 2)).denominator := by
      unfold Window.Basic.denominatorRatio
      rw [Gaussian.Basic.mul_assoc,
        Gaussian.Field.inv_mul _ upperNonzero,
        Gaussian.Basic.mul_one]
    _ = Cylinder.TwoParameter.denominatorRatio
          (Parameter.pellParameter (stage + 2)) *
        GaussianInt.toGaussian
          (Pair.criticalUpperPair
            (stage + 2)).denominator := by
      rw [ratioIdentity]
    _ = GaussianInt.toGaussian
          (Pair.criticalUpperPair
            (stage + 2)).denominator *
        Cylinder.TwoParameter.denominatorRatio
          (Parameter.pellParameter (stage + 2)) := by
      rw [Gaussian.Basic.mul_comm]

/-- A next-stage coefficient combination factors through the retained source error and normalized error coordinate.

The source is fixed at `stage+1`, the target basis is at `stage+2`, and the normalized error parameter is at `stage`. -/
private theorem next_error_linearCombination
    (stage : Nat) (left right : GaussianInt) :
    Best.Error.error
        (Pair.criticalSource (stage + 1)).value
        (LinearCombination.linearCombination
          (Pair.criticalLowerPair (stage + 2))
          (Pair.criticalUpperPair (stage + 2))
          left right) =
      (Pair.criticalLowerError (stage + 1) *
          lowerErrorScale stage) *
        Cylinder.TwoParameter.normalizedError
          (Parameter.pellParameter stage) left right := by
  rw [Best.Error.error_linearCombination, next_error_lower,
    next_error_upper]
  unfold Cylinder.TwoParameter.normalizedError
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
        (LinearCombination.linearCombination
          (Pair.criticalLowerPair (stage + 2))
          (Pair.criticalUpperPair (stage + 2))
          left right).denominator =
      GaussianInt.toGaussian
          (Pair.criticalUpperPair
            (stage + 2)).denominator *
        Cylinder.TwoParameter.normalizedDenominator
          (Parameter.pellParameter (stage + 2))
          left right := by
  simp only [LinearCombination.linearCombination, GaussianInt.toGaussian_add,
    GaussianInt.toGaussian_mul]
  rw [next_denominator_lower]
  unfold Cylinder.TwoParameter.normalizedDenominator
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- The native critical lower error has positive quadrance at every finite stage. -/
theorem criticalLowerError_normSq_pos (stage : Nat) :
    0 < Gaussian.Norm.Basic.normSq
      (Pair.criticalLowerError stage) := by
  have nativeWindow :=
    Pair.criticalPairs_areConsecutiveBest stage
  have nativeErrorOrder :
      Best.Error.errorQuadrance
          (Pair.criticalSource stage).value
          (Pair.criticalUpperPair stage) <
        Best.Error.errorQuadrance
          (Pair.criticalSource stage).value
          (Pair.criticalLowerPair stage) :=
    nativeWindow.2.1.2.1 _ nativeWindow.1.1 nativeWindow.2.2.1
  rw [← Pair.criticalSource_error_lower]
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
    0 < Gaussian.Norm.Basic.normSq lowerError
  /-- The target lower pair has exactly the retained lower error at the fixed source. -/ lowerIdentity :
    Best.Error.error source.value
        (Pair.criticalLowerPair targetStage) =
      lowerError
  /-- The target upper error is the retained lower error times the error-stage Pell ratio. -/ upperIdentity :
    Best.Error.error source.value
        (Pair.criticalUpperPair targetStage) =
      lowerError * Cylinder.TwoParameter.errorRatio
        (Parameter.pellParameter errorStage)

constructive_injectivity TransportedNormalForm

/-- The native critical pair is already in transported normal form. -/
@[expose] def nativeNormalForm (stage : Nat) :
    TransportedNormalForm
      (Pair.criticalSource stage) stage stage :=
  { lowerError := Pair.criticalLowerError stage
    lowerErrorPositive := criticalLowerError_normSq_pos stage
    lowerIdentity :=
      Pair.criticalSource_error_lower stage
    upperIdentity := by
      rw [Pair.criticalSource_error_upper,
        criticalErrorRatio_eq_twoParameter] }

/-- One fixed critical-branch basis transition moves the normalized error
parameter back by one supplied stage while moving the target basis forward
by one stage. -/
@[expose] def TransportedNormalForm.advance
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source (errorStage + 1) targetStage) :
    TransportedNormalForm source errorStage (targetStage + 1) := by
  let nextLowerError := normal.lowerError * lowerErrorScale errorStage
  refine
    { lowerError := nextLowerError
      lowerErrorPositive := ?_
      lowerIdentity := ?_
      upperIdentity := ?_ }
  · dsimp only [nextLowerError]
    rw [Gaussian.Norm.Basic.normSq_mul]
    exact Arithmetic.mul_pos_direct
      normal.lowerErrorPositive (lowerErrorScale_normSq_pos errorStage)
  · rw [Transition.criticalLowerPair_succ,
      Best.Error.error_linearCombination, normal.lowerIdentity, normal.upperIdentity]
    change
      GaussianInt.toGaussian Transition.lowerFromLower * normal.lowerError +
          GaussianInt.toGaussian Transition.lowerFromUpper *
            (normal.lowerError *
              Cylinder.TwoParameter.errorRatio
                (Parameter.pellParameter
                  (errorStage + 1))) =
        nextLowerError
    rw [← criticalErrorRatio_eq_twoParameter]
    calc
      GaussianInt.toGaussian Transition.lowerFromLower * normal.lowerError +
          GaussianInt.toGaussian Transition.lowerFromUpper *
            (normal.lowerError *
              Cylinder.Basic.criticalErrorRatio
                (Parameter.pellParameter
                  (errorStage + 1))) =
        normal.lowerError *
          (GaussianInt.toGaussian Transition.lowerFromLower +
            GaussianInt.toGaussian Transition.lowerFromUpper *
              Cylinder.Basic.criticalErrorRatio
                (Parameter.pellParameter
                  (errorStage + 1))) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
      _ = normal.lowerError * lowerErrorScale errorStage := by
        exact congrArg (normal.lowerError * ·)
          (lowerCombinationFactor errorStage)
      _ = nextLowerError := by rfl
  · rw [Transition.criticalUpperPair_succ,
      Best.Error.error_linearCombination, normal.lowerIdentity, normal.upperIdentity]
    change
      GaussianInt.toGaussian Transition.upperFromLower * normal.lowerError +
          GaussianInt.toGaussian Transition.upperFromUpper *
            (normal.lowerError *
              Cylinder.TwoParameter.errorRatio
                (Parameter.pellParameter
                  (errorStage + 1))) =
        nextLowerError * Cylinder.TwoParameter.errorRatio
          (Parameter.pellParameter errorStage)
    rw [← criticalErrorRatio_eq_twoParameter]
    calc
      GaussianInt.toGaussian Transition.upperFromLower * normal.lowerError +
          GaussianInt.toGaussian Transition.upperFromUpper *
            (normal.lowerError *
              Cylinder.Basic.criticalErrorRatio
                (Parameter.pellParameter
                  (errorStage + 1))) =
        normal.lowerError *
          (GaussianInt.toGaussian Transition.upperFromLower +
            GaussianInt.toGaussian Transition.upperFromUpper *
              Cylinder.Basic.criticalErrorRatio
                (Parameter.pellParameter
                  (errorStage + 1))) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
      _ = normal.lowerError *
          (lowerErrorScale errorStage *
            Cylinder.TwoParameter.errorRatio
              (Parameter.pellParameter errorStage)) := by
        exact congrArg (normal.lowerError * ·)
          (upperCombinationFactor errorStage)
      _ = nextLowerError * Cylinder.TwoParameter.errorRatio
          (Parameter.pellParameter errorStage) := by
        dsimp only [nextLowerError]
        rw [Gaussian.Basic.mul_assoc]

/-- Iterating only a supplied finite number of transitions gives the exact
same-source normal form with the error stage moving backward and the target
stage moving forward. -/
@[expose] def transportedNormalForm (backwardStage steps : Nat) :
    TransportedNormalForm
      (Pair.criticalSource (backwardStage + steps))
      backwardStage (backwardStage + 2 * steps) := by
  induction steps generalizing backwardStage with
  | zero =>
      simpa only [Nat.add_zero, Nat.mul_zero] using
        nativeNormalForm backwardStage
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
        (Pair.criticalLowerPair
          targetStage).denominator =
      GaussianInt.toGaussian
          (Pair.criticalUpperPair
            targetStage).denominator *
        Cylinder.TwoParameter.denominatorRatio
          (Parameter.pellParameter targetStage) := by
  have upperNonzero :
      GaussianInt.toGaussian
          (Pair.criticalUpperPair
            targetStage).denominator ≠ 0 := by
    intro zero
    exact Pair.criticalUpper_denominator_ne_zero
      targetStage (GaussianInt.toGaussian_eq_zero.mp zero)
  have ratioIdentity :=
    Pair.criticalPair_denominatorRatio targetStage
  rw [criticalDenominatorRatio_eq_twoParameter] at ratioIdentity
  calc
    GaussianInt.toGaussian
          (Pair.criticalLowerPair
            targetStage).denominator =
        Window.Basic.denominatorRatio
            (Pair.criticalLowerPair targetStage)
            (Pair.criticalUpperPair targetStage) *
          GaussianInt.toGaussian
            (Pair.criticalUpperPair
              targetStage).denominator := by
      unfold Window.Basic.denominatorRatio
      rw [Gaussian.Basic.mul_assoc,
        Gaussian.Field.inv_mul _ upperNonzero,
        Gaussian.Basic.mul_one]
    _ = Cylinder.TwoParameter.denominatorRatio
          (Parameter.pellParameter targetStage) *
        GaussianInt.toGaussian
          (Pair.criticalUpperPair
            targetStage).denominator := by
      rw [ratioIdentity]
    _ = GaussianInt.toGaussian
          (Pair.criticalUpperPair
            targetStage).denominator *
        Cylinder.TwoParameter.denominatorRatio
          (Parameter.pellParameter targetStage) := by
      rw [Gaussian.Basic.mul_comm]

/-- A coefficient combination in the target critical basis factors through
the target upper denominator and its two-parameter normalized coordinate. -/
theorem target_denominator_linearCombination
    (targetStage : Nat) (left right : GaussianInt) :
    GaussianInt.toGaussian
        (LinearCombination.linearCombination
          (Pair.criticalLowerPair targetStage)
          (Pair.criticalUpperPair targetStage)
          left right).denominator =
      GaussianInt.toGaussian
          (Pair.criticalUpperPair
            targetStage).denominator *
        Cylinder.TwoParameter.normalizedDenominator
          (Parameter.pellParameter targetStage)
          left right := by
  simp only [LinearCombination.linearCombination, GaussianInt.toGaussian_add,
    GaussianInt.toGaussian_mul]
  rw [target_denominator_lower]
  unfold Cylinder.TwoParameter.normalizedDenominator
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- The embedded upper denominator at any target stage has positive quadrance. -/
private theorem target_upperDenominator_normSq_pos (targetStage : Nat) :
    0 < Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian
        (Pair.criticalUpperPair
          targetStage).denominator) := by
  apply Gaussian.Norm.Basic.normSq_pos
  intro zero
  exact Pair.criticalUpper_denominator_ne_zero
    targetStage (GaussianInt.toGaussian_eq_zero.mp zero)

/-- A coefficient combination in a transported critical basis factors
through its exact lower error and its two-parameter normalized coordinate. -/
theorem TransportedNormalForm.error_linearCombination
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (left right : GaussianInt) :
    Best.Error.error source.value
        (LinearCombination.linearCombination
          (Pair.criticalLowerPair targetStage)
          (Pair.criticalUpperPair targetStage)
          left right) =
      normal.lowerError *
        Cylinder.TwoParameter.normalizedError
          (Parameter.pellParameter errorStage)
          left right := by
  rw [Best.Error.error_linearCombination,
    TransportedNormalForm.lowerIdentity normal,
    TransportedNormalForm.upperIdentity normal]
  unfold Cylinder.TwoParameter.normalizedError
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
    (normal : TransportedNormalForm source errorStage targetStage) :
    Best.Cylinder.Basis.StrictExteriorCertificate source.value
      (Pair.criticalLowerPair targetStage)
      (Pair.criticalUpperPair targetStage) := by
  refine
    { indexOne :=
        Pair.criticalPair_indexOne targetStage
      lowerDenominatorNonzero :=
        Pair.criticalLower_denominator_ne_zero
          targetStage
      upperDenominatorNonzero :=
        Pair.criticalUpper_denominator_ne_zero
          targetStage
      errorOrder := ?_
      denominatorOrder :=
        Pair.critical_denominatorQuadrance_ordered
          targetStage
      bothNonzeroExterior := ?_ }
  · unfold Best.Error.errorQuadrance
    rw [normal.lowerIdentity, normal.upperIdentity]
    have ratioStrict :=
      Cylinder.TwoParameter.normSq_errorRatio_lt_one
        (Parameter.pellParameter_isCritical errorStage)
    calc
      Gaussian.Norm.Basic.normSq
          (normal.lowerError *
            Cylinder.TwoParameter.errorRatio
              (Parameter.pellParameter errorStage)) =
        Gaussian.Norm.Basic.normSq normal.lowerError *
          Gaussian.Norm.Basic.normSq
            (Cylinder.TwoParameter.errorRatio
              (Parameter.pellParameter errorStage)) := by
        rw [Gaussian.Norm.Basic.normSq_mul]
      _ < Gaussian.Norm.Basic.normSq normal.lowerError * 1 :=
        Arithmetic.mul_lt_mul_of_pos_left_direct
          normal.lowerErrorPositive ratioStrict
      _ = Gaussian.Norm.Basic.normSq normal.lowerError := by
        ring1
  · intro left right leftNonzero rightNonzero
    rcases Cylinder.TwoParameter.strictExterior
        (Parameter.pellParameter_isCritical errorStage)
        (Parameter.pellParameter_isCritical targetStage)
        left right leftNonzero rightNonzero with
      errorExterior | denominatorExterior
    · left
      unfold Best.Error.errorQuadrance
      rw [normal.lowerIdentity, normal.error_linearCombination]
      calc
        Gaussian.Norm.Basic.normSq normal.lowerError =
            Gaussian.Norm.Basic.normSq normal.lowerError * 1 := by
          ring1
        _ < Gaussian.Norm.Basic.normSq normal.lowerError *
            Gaussian.Norm.Basic.normSq
              (Cylinder.TwoParameter.normalizedError
                (Parameter.pellParameter errorStage)
                left right) :=
          Arithmetic.mul_lt_mul_of_pos_left_direct
            normal.lowerErrorPositive errorExterior
        _ = Gaussian.Norm.Basic.normSq
            (normal.lowerError *
              Cylinder.TwoParameter.normalizedError
                (Parameter.pellParameter errorStage)
                left right) := by
          exact (Gaussian.Norm.Basic.normSq_mul _ _).symm
    · right
      apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
      unfold Best.Error.denominatorQuadrance
      rw [← GaussianInt.normSq_toGaussian, ← GaussianInt.normSq_toGaussian,
        target_denominator_linearCombination]
      calc
        Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
              (Pair.criticalUpperPair
                targetStage).denominator) =
          Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian
                (Pair.criticalUpperPair
                  targetStage).denominator) * 1 := by
            ring1
        _ < Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian
                (Pair.criticalUpperPair
                  targetStage).denominator) *
            Gaussian.Norm.Basic.normSq
              (Cylinder.TwoParameter.normalizedDenominator
                (Parameter.pellParameter targetStage)
                left right) :=
          Arithmetic.mul_lt_mul_of_pos_left_direct
            (target_upperDenominator_normSq_pos targetStage)
            denominatorExterior
        _ = Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
                (Pair.criticalUpperPair
                  targetStage).denominator *
              Cylinder.TwoParameter.normalizedDenominator
                (Parameter.pellParameter targetStage)
                left right) := by
          rw [Gaussian.Norm.Basic.normSq_mul]

/-- A transported normal form retains a nonzero lower error. -/
private theorem TransportedNormalForm.lowerError_ne_zero
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    normal.lowerError ≠ 0 := by
  intro zero
  have normZero := congrArg Gaussian.Norm.Basic.normSq zero
  rw [Gaussian.Norm.Basic.normSq_zero] at normZero
  exact (ne_of_gt normal.lowerErrorPositive) normZero

/-- The abstract consecutive-window error ratio is exactly the earlier Pell
parameter carried by the transported normal form. -/
theorem TransportedNormalForm.errorRatio_eq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    Window.Basic.errorRatio source.value
        (Pair.criticalLowerPair targetStage)
        (Pair.criticalUpperPair targetStage) =
      Cylinder.TwoParameter.errorRatio
        (Parameter.pellParameter errorStage) := by
  unfold Window.Basic.errorRatio
  rw [normal.lowerIdentity, normal.upperIdentity]
  calc
    (normal.lowerError *
          Cylinder.TwoParameter.errorRatio
            (Parameter.pellParameter errorStage)) *
        Gaussian.Field.inv normal.lowerError =
      Cylinder.TwoParameter.errorRatio
          (Parameter.pellParameter errorStage) *
        (normal.lowerError *
          Gaussian.Field.inv normal.lowerError) := by
      rw [Gaussian.Basic.mul_comm normal.lowerError,
        Gaussian.Basic.mul_assoc]
    _ = Cylinder.TwoParameter.errorRatio
        (Parameter.pellParameter errorStage) * 1 := by
      rw [Gaussian.Field.mul_inv _
        normal.lowerError_ne_zero]
    _ = Cylinder.TwoParameter.errorRatio
        (Parameter.pellParameter errorStage) := by
      rw [Gaussian.Basic.mul_one]

/-- The denominator ratio at the transported target remains the later Pell
parameter built into that explicit pair basis. -/
theorem transportedDenominatorRatio_eq (targetStage : Nat) :
    Window.Basic.denominatorRatio
        (Pair.criticalLowerPair targetStage)
        (Pair.criticalUpperPair targetStage) =
      Cylinder.TwoParameter.denominatorRatio
        (Parameter.pellParameter targetStage) := by
  rw [Pair.criticalPair_denominatorRatio,
    criticalDenominatorRatio_eq_twoParameter]

/-- The normalized determinant gap of a transported same-source window is
the exact two-parameter rational gap. -/
theorem TransportedNormalForm.normalizedGap_eq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    Gaussian.Norm.Basic.normSq
        (1 - Window.Basic.denominatorRatio
            (Pair.criticalLowerPair targetStage)
            (Pair.criticalUpperPair targetStage) *
          Window.Basic.errorRatio source.value
            (Pair.criticalLowerPair targetStage)
            (Pair.criticalUpperPair targetStage)) =
      Cylinder.TwoParameter.gap
        (Parameter.pellParameter errorStage)
        (Parameter.pellParameter targetStage) := by
  rw [normal.errorRatio_eq, transportedDenominatorRatio_eq]
  rfl

/-- Exact index-one product identity for every transported finite window. -/
theorem TransportedNormalForm.window_mul_gap_eq_one
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    Window.SourceBound.dirichletWindowQuadrance source.value
          (Pair.criticalLowerPair targetStage)
          (Pair.criticalUpperPair targetStage) *
        Cylinder.TwoParameter.gap
          (Parameter.pellParameter errorStage)
          (Parameter.pellParameter targetStage) = 1 := by
  have consecutive := normal.strictExteriorCertificate.areConsecutiveBest
  have identity :=
    Window.Basic.AreConsecutiveBest.dirichletWindow_mul_normalizedGap_eq_index
      consecutive
  rw [normal.normalizedGap_eq,
    Pair.criticalPair_indexOne] at identity
  exact identity

/-- Every transported critical window has quadrance strictly below two.

The strict error-ratio margin puts twice the normalized determinant gap
above one. The exact index-one window-gap product then gives the bound.
-/
theorem TransportedNormalForm.windowQuadrance_lt_two
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    Window.SourceBound.dirichletWindowQuadrance source.value
      (Pair.criticalLowerPair targetStage)
      (Pair.criticalUpperPair targetStage) < 2 := by
  let gap := Cylinder.TwoParameter.gap
    (Parameter.pellParameter errorStage) (Parameter.pellParameter targetStage)
  have errorCertificate := Parameter.pellParameter_isCritical errorStage
  have denominatorCertificate := Parameter.pellParameter_isCritical targetStage
  have twoLe : (2 : Fraction.Rational) ≤ 2 *
      (1 + Gaussian.Norm.Basic.normSq
        (Cylinder.TwoParameter.errorRatio
          (Parameter.pellParameter errorStage))) := by
    calc
      (2 : Fraction.Rational) = 2 * 1 := by ring1
      _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_right (Gaussian.Norm.Basic.normSq_nonneg _)) (by decide)
  have doubledGap : (1 : Fraction.Rational) < 2 * gap := by
    apply Arithmetic.lt_of_mul_lt_mul_right_direct (c := (2 : Fraction.Rational)) _ (by decide)
    calc
      (1 : Fraction.Rational) * 2 = 2 := by ring1
      _ < 4 * gap := twoLe.trans_lt
        (Cylinder.TwoParameter.error_margin errorCertificate denominatorCertificate)
      _ = (2 * gap) * 2 := by ring1
  apply Arithmetic.lt_of_mul_lt_mul_right_direct (c := gap) _
    (Cylinder.TwoParameter.gap_pos errorCertificate denominatorCertificate)
  calc
    Window.SourceBound.dirichletWindowQuadrance source.value
        (Pair.criticalLowerPair targetStage)
        (Pair.criticalUpperPair targetStage) * gap = 1 := normal.window_mul_gap_eq_one
    _ < 2 * gap := doubledGap

/-- A threshold strictly above the exact transported gap is violated by the
corresponding displayed same-source Dirichlet window. -/
theorem TransportedNormalForm.one_lt_threshold_mul_window
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (threshold : Fraction.Rational)
    (gapStrict :
      Cylinder.TwoParameter.gap
          (Parameter.pellParameter errorStage)
          (Parameter.pellParameter targetStage) < threshold) :
    1 < threshold * Window.SourceBound.dirichletWindowQuadrance source.value
      (Pair.criticalLowerPair targetStage)
      (Pair.criticalUpperPair targetStage) := by
  let window := Window.SourceBound.dirichletWindowQuadrance source.value
    (Pair.criticalLowerPair targetStage)
    (Pair.criticalUpperPair targetStage)
  let gap := Cylinder.TwoParameter.gap
    (Parameter.pellParameter errorStage)
    (Parameter.pellParameter targetStage)
  have productIdentity : window * gap = 1 := by
    simpa only [window, gap] using normal.window_mul_gap_eq_one
  have gapNonnegative : (0 : Fraction.Rational) ≤ gap := by
    dsimp only [gap, Cylinder.TwoParameter.gap]
    exact Gaussian.Norm.Basic.normSq_nonneg _
  have gapTimesWindowPositive : 0 < gap * window := by
    calc
      (0 : Fraction.Rational) < 1 := by decide
      _ = gap * window := by rw [Fraction.Field.mul_comm,
        productIdentity]
  have windowPositive : 0 < window :=
    Arithmetic.pos_of_mul_pos_right_direct
      gapTimesWindowPositive gapNonnegative
  calc
    (1 : Fraction.Rational) = gap * window := by
      rw [Fraction.Field.mul_comm, productIdentity]
    _ < threshold * window :=
      Arithmetic.mul_lt_mul_of_pos_right_direct
        (by simpa only [gap] using gapStrict) windowPositive

/-- Once the earlier error stage lies beyond the explicit sharpness stage,
every later transported denominator stage has gap below the same proposed
sharper threshold. -/
theorem transportedGap_lt_sharperThreshold
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale backwardStage targetStage : Nat)
    (backwardBeyond :
      Sharpness.sharpnessStage threshold requestedScale ≤
        backwardStage)
    (targetBeyond : backwardStage ≤ targetStage) :
    Cylinder.TwoParameter.gap
        (Parameter.pellParameter backwardStage)
        (Parameter.pellParameter targetStage) < threshold := by
  let baseStage :=
    Sharpness.sharpnessStage threshold requestedScale
  have errorParameterOrder :
      Parameter.pellParameter baseStage ≤
        Parameter.pellParameter backwardStage :=
    Transition.pellParameter_le_of_le backwardBeyond
  have denominatorStageOrder : baseStage ≤ targetStage :=
    backwardBeyond.trans targetBeyond
  have denominatorParameterOrder :
      Parameter.pellParameter baseStage ≤
        Parameter.pellParameter targetStage :=
    Transition.pellParameter_le_of_le denominatorStageOrder
  have mixedGapBound := Cylinder.TwoParameter.gap_antitone
    (Parameter.pellParameter_isCritical backwardStage)
    (Parameter.pellParameter_isCritical baseStage)
    (Parameter.pellParameter_isCritical targetStage)
    errorParameterOrder denominatorParameterOrder
  calc
    Cylinder.TwoParameter.gap
          (Parameter.pellParameter backwardStage)
          (Parameter.pellParameter targetStage) ≤
        Cylinder.TwoParameter.gap
          (Parameter.pellParameter baseStage)
          (Parameter.pellParameter baseStage) := mixedGapBound
    _ = Cylinder.Basic.criticalGap
        (Parameter.pellParameter baseStage) :=
      Cylinder.TwoParameter.diagonalGap_eq_criticalGap _
    _ < threshold := by
      simpa only [baseStage] using
        Sharpness.criticalGap_lt_sharperThreshold
          certificate requestedScale

/-- An arbitrary supplied finite transport depth yields a genuine
consecutive-best window at the later target stage for one fixed rational
source. -/
theorem transportedPairs_areConsecutiveBest
    (backwardStage steps : Nat) :
    Best.Consecutive.Basic.AreConsecutiveBest
      (Pair.criticalSource
        (backwardStage + steps)).value
      (Pair.criticalLowerPair
        (backwardStage + 2 * steps))
      (Pair.criticalUpperPair
        (backwardStage + 2 * steps)) :=
  (transportedNormalForm backwardStage steps).strictExteriorCertificate
    |>.areConsecutiveBest

/-- The lower error after one basis transition has positive quadrance. -/
private theorem next_lowerError_normSq_pos (stage : Nat) :
    0 < Gaussian.Norm.Basic.normSq
      (Pair.criticalLowerError (stage + 1) *
        lowerErrorScale stage) := by
  rw [Gaussian.Norm.Basic.normSq_mul]
  exact Arithmetic.mul_pos_direct
    (criticalLowerError_normSq_pos (stage + 1))
    (lowerErrorScale_normSq_pos stage)

/-- The embedded upper denominator after one basis transition has positive quadrance. -/
private theorem next_upperDenominator_normSq_pos (stage : Nat) :
    0 < Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian
        (Pair.criticalUpperPair
          (stage + 2)).denominator) := by
  apply Gaussian.Norm.Basic.normSq_pos
  intro zero
  exact Pair.criticalUpper_denominator_ne_zero
    (stage + 2) (GaussianInt.toGaussian_eq_zero.mp zero)

/-- The exact strict-basis certificate for the window immediately after the
native window of a supplied positive critical stage. -/
theorem nextStrictExteriorCertificate (stage : Nat) :
    Best.Cylinder.Basis.StrictExteriorCertificate
      (Pair.criticalSource (stage + 1)).value
      (Pair.criticalLowerPair (stage + 2))
      (Pair.criticalUpperPair (stage + 2)) := by
  refine
    { indexOne :=
        Pair.criticalPair_indexOne (stage + 2)
      lowerDenominatorNonzero :=
        Pair.criticalLower_denominator_ne_zero
          (stage + 2)
      upperDenominatorNonzero :=
        Pair.criticalUpper_denominator_ne_zero
          (stage + 2)
      errorOrder := ?_
      denominatorOrder :=
        Pair.critical_denominatorQuadrance_ordered
          (stage + 2)
      bothNonzeroExterior := ?_ }
  · unfold Best.Error.errorQuadrance
    rw [next_error_lower, next_error_upper]
    have ratioStrict :=
      Cylinder.TwoParameter.normSq_errorRatio_lt_one
        (Parameter.pellParameter_isCritical stage)
    calc
      Gaussian.Norm.Basic.normSq
          ((Pair.criticalLowerError (stage + 1) *
              lowerErrorScale stage) *
            Cylinder.TwoParameter.errorRatio
              (Parameter.pellParameter stage)) =
        Gaussian.Norm.Basic.normSq
            (Pair.criticalLowerError (stage + 1) *
              lowerErrorScale stage) *
          Gaussian.Norm.Basic.normSq
            (Cylinder.TwoParameter.errorRatio
              (Parameter.pellParameter stage)) := by
        rw [Gaussian.Norm.Basic.normSq_mul]
      _ < Gaussian.Norm.Basic.normSq
            (Pair.criticalLowerError (stage + 1) *
              lowerErrorScale stage) * 1 :=
        Arithmetic.mul_lt_mul_of_pos_left_direct
          (next_lowerError_normSq_pos stage) ratioStrict
      _ = Gaussian.Norm.Basic.normSq
          (Pair.criticalLowerError (stage + 1) *
            lowerErrorScale stage) := by ring1
  · intro left right leftNonzero rightNonzero
    rcases Cylinder.TwoParameter.strictExterior
        (Parameter.pellParameter_isCritical stage)
        (Parameter.pellParameter_isCritical
          (stage + 2)) left right leftNonzero rightNonzero with
      errorExterior | denominatorExterior
    · left
      unfold Best.Error.errorQuadrance
      rw [next_error_lower,
        next_error_linearCombination]
      calc
        Gaussian.Norm.Basic.normSq
            (Pair.criticalLowerError (stage + 1) *
              lowerErrorScale stage) =
          Gaussian.Norm.Basic.normSq
              (Pair.criticalLowerError (stage + 1) *
                lowerErrorScale stage) * 1 := by ring1
        _ < Gaussian.Norm.Basic.normSq
              (Pair.criticalLowerError (stage + 1) *
                lowerErrorScale stage) *
            Gaussian.Norm.Basic.normSq
              (Cylinder.TwoParameter.normalizedError
                (Parameter.pellParameter stage)
                left right) :=
          Arithmetic.mul_lt_mul_of_pos_left_direct
            (next_lowerError_normSq_pos stage) errorExterior
        _ = Gaussian.Norm.Basic.normSq
            ((Pair.criticalLowerError (stage + 1) *
                lowerErrorScale stage) *
              Cylinder.TwoParameter.normalizedError
                (Parameter.pellParameter stage)
                left right) := by
          exact (Gaussian.Norm.Basic.normSq_mul _ _).symm
    · right
      apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
      unfold Best.Error.denominatorQuadrance
      rw [← GaussianInt.normSq_toGaussian, ← GaussianInt.normSq_toGaussian,
        next_denominator_linearCombination]
      calc
        Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
              (Pair.criticalUpperPair
                (stage + 2)).denominator) =
          Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian
                (Pair.criticalUpperPair
                  (stage + 2)).denominator) * 1 := by ring1
        _ < Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian
                (Pair.criticalUpperPair
                  (stage + 2)).denominator) *
            Gaussian.Norm.Basic.normSq
              (Cylinder.TwoParameter.normalizedDenominator
                (Parameter.pellParameter (stage + 2))
                left right) :=
          Arithmetic.mul_lt_mul_of_pos_left_direct
            (next_upperDenominator_normSq_pos stage) denominatorExterior
        _ = Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
                (Pair.criticalUpperPair
                  (stage + 2)).denominator *
              Cylinder.TwoParameter.normalizedDenominator
                (Parameter.pellParameter (stage + 2))
                left right) := by
          rw [Gaussian.Norm.Basic.normSq_mul]

/-- The next critical pair basis is a genuine consecutive-best window for
the same rational source as the native window at stage `stage + 1`. -/
theorem nextPairs_areConsecutiveBest (stage : Nat) :
    Best.Consecutive.Basic.AreConsecutiveBest
      (Pair.criticalSource (stage + 1)).value
      (Pair.criticalLowerPair (stage + 2))
      (Pair.criticalUpperPair (stage + 2)) :=
  (nextStrictExteriorCertificate stage).areConsecutiveBest

/-- At every supplied finite stage, one displayed rational source supports
its native critical window and the immediately following, strictly
scale-separated critical window. -/
theorem criticalSource_succ_supports_two_windows (stage : Nat) :
    Best.Consecutive.Basic.AreConsecutiveBest
        (Pair.criticalSource (stage + 1)).value
        (Pair.criticalLowerPair (stage + 1))
        (Pair.criticalUpperPair (stage + 1)) ∧
      Best.Consecutive.Basic.AreConsecutiveBest
        (Pair.criticalSource (stage + 1)).value
        (Pair.criticalLowerPair (stage + 2))
        (Pair.criticalUpperPair (stage + 2)) ∧
      Best.Error.denominatorQuadrance
          (Pair.criticalUpperPair (stage + 1)) <
        Best.Error.denominatorQuadrance
          (Pair.criticalLowerPair (stage + 2)) :=
  ⟨Pair.criticalPairs_areConsecutiveBest (stage + 1),
    nextPairs_areConsecutiveBest stage,
    Transition.criticalUpper_lt_nextLower_denominatorQuadrance
      (stage + 1)⟩

/-- Positive-stage form of the adjacent-window theorem, convenient when the
current stage was computed from a threshold and requested scale. -/
theorem criticalSource_supports_next_of_pos
    (currentStage : Nat) (positive : 0 < currentStage) :
    Best.Consecutive.Basic.AreConsecutiveBest
        (Pair.criticalSource currentStage).value
        (Pair.criticalLowerPair currentStage)
        (Pair.criticalUpperPair currentStage) ∧
      Best.Consecutive.Basic.AreConsecutiveBest
        (Pair.criticalSource currentStage).value
        (Pair.criticalLowerPair (currentStage + 1))
        (Pair.criticalUpperPair (currentStage + 1)) ∧
      Best.Error.denominatorQuadrance
          (Pair.criticalUpperPair currentStage) <
        Best.Error.denominatorQuadrance
          (Pair.criticalLowerPair (currentStage + 1)) := by
  obtain ⟨stage, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simpa only [Nat.succ_eq_add_one] using
    criticalSource_succ_supports_two_windows stage

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Tower

end
