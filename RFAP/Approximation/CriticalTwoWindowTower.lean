import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.BasisCylinder
import RFAP.Approximation.CriticalBranch
import RFAP.Approximation.TwoParameterCylinder

/-!
# Adjacent critical windows at every finite Pell stage

The source constructed for critical stage `k + 1` supports not only its
native consecutive-best window, but also the next critical pair basis at
stage `k + 2`.  The proof transports the next basis through the fixed
unimodular critical-branch transition and applies the uniform two-parameter
finite cylinder theorem.  Every parameter and source remains an explicitly
evaluated rational object at a supplied finite stage.
-/

namespace RFAP.CriticalTwoWindowTower

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Fraction := RFAP.HurwitzRational.Fraction

open RFAP.BestApproximation
open RFAP.ConstructiveGaussianHeight.GaussianInt

private def lowerErrorScale (stage : Nat) : Gaussian :=
  ⟨RFAP.FiniteWindowSharpness.pellParameter (stage + 1), 0⟩

private theorem lowerErrorScale_normSq_pos (stage : Nat) :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (lowerErrorScale stage) := by
  have parameterPositive :
      (0 : Coordinate) <
        RFAP.FiniteWindowSharpness.pellParameter (stage + 1) :=
    (show (0 : Coordinate) < 1 / 4 by decide).trans_le
      (RFAP.FiniteWindowSharpness.oneFourth_le_pellParameter (stage + 1))
  apply RFAP.ConstructiveGaussian.Gaussian.normSq_pos
  intro zero
  have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
  simp only [lowerErrorScale,
    RFAP.ConstructiveGaussian.Gaussian.zero_re] at realZero
  exact parameterPositive.ne' realZero

private theorem criticalErrorRatio_eq_twoParameter (value : Coordinate) :
    RFAP.FiniteWindowSharpness.criticalErrorRatio value =
      RFAP.TwoParameterCylinder.errorRatio value := by
  rfl

private theorem criticalDenominatorRatio_eq_twoParameter
    (value : Coordinate) :
    RFAP.FiniteWindowSharpness.criticalDenominatorRatio value =
      RFAP.TwoParameterCylinder.denominatorRatio value := by
  rfl

private theorem lowerCombinationFactor (stage : Nat) :
    toGaussian RFAP.CriticalBranch.lowerFromLower +
        toGaussian RFAP.CriticalBranch.lowerFromUpper *
          RFAP.FiniteWindowSharpness.criticalErrorRatio
            (RFAP.FiniteWindowSharpness.pellParameter (stage + 1)) =
      lowerErrorScale stage := by
  rw [criticalErrorRatio_eq_twoParameter]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [lowerErrorScale, RFAP.CriticalBranch.lowerFromLower,
      RFAP.CriticalBranch.lowerFromUpper,
      RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian,
      RFAP.TwoParameterCylinder.errorRatio_re,
      RFAP.TwoParameterCylinder.errorRatio_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      Int.cast_zero, Int.cast_one, Int.cast_neg, Int.cast_ofNat]
  · calc
      _ = (2 * (1 / 2 : Coordinate)) *
          RFAP.FiniteWindowSharpness.pellParameter (stage + 1) := by
        ring1
      _ = RFAP.FiniteWindowSharpness.pellParameter (stage + 1) := by
        rw [show (2 : Coordinate) * (1 / 2) = 1 by decide]
        ring1
  · calc
      _ = 1 - 2 * (1 / 2 : Coordinate) := by ring1
      _ = 0 := by
        rw [show (2 : Coordinate) * (1 / 2) = 1 by decide]
        ring1

private theorem upperCombinationFactor (stage : Nat) :
    toGaussian RFAP.CriticalBranch.upperFromLower +
        toGaussian RFAP.CriticalBranch.upperFromUpper *
          RFAP.FiniteWindowSharpness.criticalErrorRatio
            (RFAP.FiniteWindowSharpness.pellParameter (stage + 1)) =
      lowerErrorScale stage *
        RFAP.TwoParameterCylinder.errorRatio
          (RFAP.FiniteWindowSharpness.pellParameter stage) := by
  rw [criticalErrorRatio_eq_twoParameter]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [lowerErrorScale, RFAP.CriticalBranch.upperFromLower,
      RFAP.CriticalBranch.upperFromUpper,
      RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian,
      RFAP.TwoParameterCylinder.errorRatio_re,
      RFAP.TwoParameterCylinder.errorRatio_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      Int.cast_zero, Int.cast_one, Int.cast_neg, Int.cast_ofNat]
    calc
      _ = (-2 + 4 * (1 / 2 : Coordinate)) +
          (1 / 2 : Coordinate) *
            RFAP.FiniteWindowSharpness.pellParameter (stage + 1) := by
        ring1
      _ = (1 / 2 : Coordinate) *
          RFAP.FiniteWindowSharpness.pellParameter (stage + 1) := by
        rw [show (4 : Coordinate) * (1 / 2) = 2 by decide]
        ring1
      _ = _ := by ring1
  · simp only [lowerErrorScale, RFAP.CriticalBranch.upperFromLower,
      RFAP.CriticalBranch.upperFromUpper,
      RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian,
      RFAP.TwoParameterCylinder.errorRatio_re,
      RFAP.TwoParameterCylinder.errorRatio_im,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      Int.cast_zero, Int.cast_one, Int.cast_neg, Int.cast_ofNat]
    calc
      _ =
        (1 / 2 : Coordinate) *
          (4 * RFAP.FiniteWindowSharpness.pellParameter (stage + 1) - 1) := by
            ring1
      _ = (1 / 2 : Coordinate) *
          (RFAP.FiniteWindowSharpness.pellParameter (stage + 1) *
            RFAP.FiniteWindowSharpness.pellParameter stage) := by
        rw [RFAP.CriticalBranch.four_mul_pellParameter_succ_sub_one]
      _ = RFAP.FiniteWindowSharpness.pellParameter (stage + 1) *
          ((1 / 2 : Coordinate) *
            RFAP.FiniteWindowSharpness.pellParameter stage) +
          0 * (1 / 2 : Coordinate) := by
        ring1

private theorem next_error_lower (stage : Nat) :
    RFAP.HurwitzApproximation.error
        (RFAP.FiniteWindowSharpness.criticalSource (stage + 1)).value
        (RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 2)) =
      RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
        lowerErrorScale stage := by
  rw [show stage + 2 = (stage + 1) + 1 by rfl,
    RFAP.CriticalBranch.criticalLowerPair_succ,
    error_linearCombination,
    RFAP.FiniteWindowSharpness.criticalSource_error_lower,
    RFAP.FiniteWindowSharpness.criticalSource_error_upper]
  calc
    toGaussian RFAP.CriticalBranch.lowerFromLower *
          RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) +
        toGaussian RFAP.CriticalBranch.lowerFromUpper *
          (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
            RFAP.FiniteWindowSharpness.criticalErrorRatio
              (RFAP.FiniteWindowSharpness.pellParameter (stage + 1))) =
      RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
        (toGaussian RFAP.CriticalBranch.lowerFromLower +
          toGaussian RFAP.CriticalBranch.lowerFromUpper *
            RFAP.FiniteWindowSharpness.criticalErrorRatio
              (RFAP.FiniteWindowSharpness.pellParameter (stage + 1))) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    _ = RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
        lowerErrorScale stage := by rw [lowerCombinationFactor]

private theorem next_error_upper (stage : Nat) :
    RFAP.HurwitzApproximation.error
        (RFAP.FiniteWindowSharpness.criticalSource (stage + 1)).value
        (RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 2)) =
      (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
          lowerErrorScale stage) *
        RFAP.TwoParameterCylinder.errorRatio
          (RFAP.FiniteWindowSharpness.pellParameter stage) := by
  rw [show stage + 2 = (stage + 1) + 1 by rfl,
    RFAP.CriticalBranch.criticalUpperPair_succ,
    error_linearCombination,
    RFAP.FiniteWindowSharpness.criticalSource_error_lower,
    RFAP.FiniteWindowSharpness.criticalSource_error_upper]
  calc
    toGaussian RFAP.CriticalBranch.upperFromLower *
          RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) +
        toGaussian RFAP.CriticalBranch.upperFromUpper *
          (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
            RFAP.FiniteWindowSharpness.criticalErrorRatio
              (RFAP.FiniteWindowSharpness.pellParameter (stage + 1))) =
      RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
        (toGaussian RFAP.CriticalBranch.upperFromLower +
          toGaussian RFAP.CriticalBranch.upperFromUpper *
            RFAP.FiniteWindowSharpness.criticalErrorRatio
              (RFAP.FiniteWindowSharpness.pellParameter (stage + 1))) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    _ = RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
        (lowerErrorScale stage *
          RFAP.TwoParameterCylinder.errorRatio
            (RFAP.FiniteWindowSharpness.pellParameter stage)) := by
      rw [upperCombinationFactor]
    _ = (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
          lowerErrorScale stage) *
        RFAP.TwoParameterCylinder.errorRatio
          (RFAP.FiniteWindowSharpness.pellParameter stage) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]

private theorem next_denominator_lower (stage : Nat) :
    toGaussian
        (RFAP.FiniteWindowSharpness.criticalLowerPair
          (stage + 2)).denominator =
      toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair
            (stage + 2)).denominator *
        RFAP.TwoParameterCylinder.denominatorRatio
          (RFAP.FiniteWindowSharpness.pellParameter (stage + 2)) := by
  have upperNonzero :
      toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair
            (stage + 2)).denominator ≠ 0 := by
    intro zero
    exact RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero
      (stage + 2) (toGaussian_eq_zero.mp zero)
  have ratioIdentity :=
    RFAP.FiniteWindowSharpness.criticalPair_denominatorRatio (stage + 2)
  rw [criticalDenominatorRatio_eq_twoParameter] at ratioIdentity
  calc
    toGaussian
          (RFAP.FiniteWindowSharpness.criticalLowerPair
            (stage + 2)).denominator =
        RFAP.DirichletWindow.denominatorRatio
            (RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 2))
            (RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 2)) *
          toGaussian
            (RFAP.FiniteWindowSharpness.criticalUpperPair
              (stage + 2)).denominator := by
      unfold RFAP.DirichletWindow.denominatorRatio
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _ upperNonzero,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]
    _ = RFAP.TwoParameterCylinder.denominatorRatio
          (RFAP.FiniteWindowSharpness.pellParameter (stage + 2)) *
        toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair
            (stage + 2)).denominator := by
      rw [ratioIdentity]
    _ = toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair
            (stage + 2)).denominator *
        RFAP.TwoParameterCylinder.denominatorRatio
          (RFAP.FiniteWindowSharpness.pellParameter (stage + 2)) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm]

private theorem next_error_linearCombination
    (stage : Nat) (left right : GaussianInt) :
    RFAP.HurwitzApproximation.error
        (RFAP.FiniteWindowSharpness.criticalSource (stage + 1)).value
        (linearCombination
          (RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 2))
          (RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 2))
          left right) =
      (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
          lowerErrorScale stage) *
        RFAP.TwoParameterCylinder.normalizedError
          (RFAP.FiniteWindowSharpness.pellParameter stage) left right := by
  rw [error_linearCombination, next_error_lower, next_error_upper]
  unfold RFAP.TwoParameterCylinder.normalizedError
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

private theorem next_denominator_linearCombination
    (stage : Nat) (left right : GaussianInt) :
    toGaussian
        (linearCombination
          (RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 2))
          (RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 2))
          left right).denominator =
      toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair
            (stage + 2)).denominator *
        RFAP.TwoParameterCylinder.normalizedDenominator
          (RFAP.FiniteWindowSharpness.pellParameter (stage + 2))
          left right := by
  simp only [linearCombination, toGaussian_add, toGaussian_mul]
  rw [next_denominator_lower]
  unfold RFAP.TwoParameterCylinder.normalizedDenominator
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

private theorem criticalLowerError_normSq_pos (stage : Nat) :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (RFAP.FiniteWindowSharpness.criticalLowerError stage) := by
  have nativeWindow :=
    RFAP.FiniteWindowSharpness.criticalPairs_areConsecutiveBest stage
  have nativeErrorOrder :
      errorQuadrance
          (RFAP.FiniteWindowSharpness.criticalSource stage).value
          (RFAP.FiniteWindowSharpness.criticalUpperPair stage) <
        errorQuadrance
          (RFAP.FiniteWindowSharpness.criticalSource stage).value
          (RFAP.FiniteWindowSharpness.criticalLowerPair stage) :=
    nativeWindow.2.1.2.1 _ nativeWindow.1.1 nativeWindow.2.2.1
  rw [← RFAP.FiniteWindowSharpness.criticalSource_error_lower]
  exact (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _).trans_lt
    nativeErrorOrder

/-- Exact normalized error data for one critical pair basis transported to a
possibly later target stage while retaining one fixed displayed source. -/
structure TransportedNormalForm
    (source : Fraction) (errorStage targetStage : Nat) where
  lowerError : Gaussian
  lowerErrorPositive :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq lowerError
  lowerIdentity :
    RFAP.HurwitzApproximation.error source.value
        (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage) =
      lowerError
  upperIdentity :
    RFAP.HurwitzApproximation.error source.value
        (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) =
      lowerError * RFAP.TwoParameterCylinder.errorRatio
        (RFAP.FiniteWindowSharpness.pellParameter errorStage)

/-- The native critical pair is already in transported normal form. -/
def nativeNormalForm (stage : Nat) :
    TransportedNormalForm
      (RFAP.FiniteWindowSharpness.criticalSource stage) stage stage :=
  { lowerError := RFAP.FiniteWindowSharpness.criticalLowerError stage
    lowerErrorPositive := criticalLowerError_normSq_pos stage
    lowerIdentity :=
      RFAP.FiniteWindowSharpness.criticalSource_error_lower stage
    upperIdentity := by
      rw [RFAP.FiniteWindowSharpness.criticalSource_error_upper,
        criticalErrorRatio_eq_twoParameter] }

/-- One fixed critical-branch basis transition moves the normalized error
parameter back by one supplied stage while moving the target basis forward
by one stage. -/
def TransportedNormalForm.advance
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source (errorStage + 1) targetStage) :
    TransportedNormalForm source errorStage (targetStage + 1) := by
  let nextLowerError := normal.lowerError * lowerErrorScale errorStage
  refine
    { lowerError := nextLowerError
      lowerErrorPositive := ?_
      lowerIdentity := ?_
      upperIdentity := ?_ }
  · dsimp only [nextLowerError]
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
    exact RFAP.ConstructiveFraction.mul_pos_direct
      normal.lowerErrorPositive (lowerErrorScale_normSq_pos errorStage)
  · rw [RFAP.CriticalBranch.criticalLowerPair_succ,
      error_linearCombination, normal.lowerIdentity, normal.upperIdentity]
    change
      toGaussian RFAP.CriticalBranch.lowerFromLower * normal.lowerError +
          toGaussian RFAP.CriticalBranch.lowerFromUpper *
            (normal.lowerError *
              RFAP.TwoParameterCylinder.errorRatio
                (RFAP.FiniteWindowSharpness.pellParameter
                  (errorStage + 1))) =
        nextLowerError
    rw [← criticalErrorRatio_eq_twoParameter]
    calc
      toGaussian RFAP.CriticalBranch.lowerFromLower * normal.lowerError +
          toGaussian RFAP.CriticalBranch.lowerFromUpper *
            (normal.lowerError *
              RFAP.FiniteWindowSharpness.criticalErrorRatio
                (RFAP.FiniteWindowSharpness.pellParameter
                  (errorStage + 1))) =
        normal.lowerError *
          (toGaussian RFAP.CriticalBranch.lowerFromLower +
            toGaussian RFAP.CriticalBranch.lowerFromUpper *
              RFAP.FiniteWindowSharpness.criticalErrorRatio
                (RFAP.FiniteWindowSharpness.pellParameter
                  (errorStage + 1))) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
      _ = normal.lowerError * lowerErrorScale errorStage := by
        rw [lowerCombinationFactor]
      _ = nextLowerError := by rfl
  · rw [RFAP.CriticalBranch.criticalUpperPair_succ,
      error_linearCombination, normal.lowerIdentity, normal.upperIdentity]
    change
      toGaussian RFAP.CriticalBranch.upperFromLower * normal.lowerError +
          toGaussian RFAP.CriticalBranch.upperFromUpper *
            (normal.lowerError *
              RFAP.TwoParameterCylinder.errorRatio
                (RFAP.FiniteWindowSharpness.pellParameter
                  (errorStage + 1))) =
        nextLowerError * RFAP.TwoParameterCylinder.errorRatio
          (RFAP.FiniteWindowSharpness.pellParameter errorStage)
    rw [← criticalErrorRatio_eq_twoParameter]
    calc
      toGaussian RFAP.CriticalBranch.upperFromLower * normal.lowerError +
          toGaussian RFAP.CriticalBranch.upperFromUpper *
            (normal.lowerError *
              RFAP.FiniteWindowSharpness.criticalErrorRatio
                (RFAP.FiniteWindowSharpness.pellParameter
                  (errorStage + 1))) =
        normal.lowerError *
          (toGaussian RFAP.CriticalBranch.upperFromLower +
            toGaussian RFAP.CriticalBranch.upperFromUpper *
              RFAP.FiniteWindowSharpness.criticalErrorRatio
                (RFAP.FiniteWindowSharpness.pellParameter
                  (errorStage + 1))) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
      _ = normal.lowerError *
          (lowerErrorScale errorStage *
            RFAP.TwoParameterCylinder.errorRatio
              (RFAP.FiniteWindowSharpness.pellParameter errorStage)) := by
        rw [upperCombinationFactor]
      _ = nextLowerError * RFAP.TwoParameterCylinder.errorRatio
          (RFAP.FiniteWindowSharpness.pellParameter errorStage) := by
        dsimp only [nextLowerError]
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]

/-- Iterating only a supplied finite number of transitions gives the exact
same-source normal form with the error stage moving backward and the target
stage moving forward. -/
def transportedNormalForm (backwardStage steps : Nat) :
    TransportedNormalForm
      (RFAP.FiniteWindowSharpness.criticalSource (backwardStage + steps))
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

private theorem target_denominator_lower (targetStage : Nat) :
    toGaussian
        (RFAP.FiniteWindowSharpness.criticalLowerPair
          targetStage).denominator =
      toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair
            targetStage).denominator *
        RFAP.TwoParameterCylinder.denominatorRatio
          (RFAP.FiniteWindowSharpness.pellParameter targetStage) := by
  have upperNonzero :
      toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair
            targetStage).denominator ≠ 0 := by
    intro zero
    exact RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero
      targetStage (toGaussian_eq_zero.mp zero)
  have ratioIdentity :=
    RFAP.FiniteWindowSharpness.criticalPair_denominatorRatio targetStage
  rw [criticalDenominatorRatio_eq_twoParameter] at ratioIdentity
  calc
    toGaussian
          (RFAP.FiniteWindowSharpness.criticalLowerPair
            targetStage).denominator =
        RFAP.DirichletWindow.denominatorRatio
            (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
            (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) *
          toGaussian
            (RFAP.FiniteWindowSharpness.criticalUpperPair
              targetStage).denominator := by
      unfold RFAP.DirichletWindow.denominatorRatio
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _ upperNonzero,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]
    _ = RFAP.TwoParameterCylinder.denominatorRatio
          (RFAP.FiniteWindowSharpness.pellParameter targetStage) *
        toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair
            targetStage).denominator := by
      rw [ratioIdentity]
    _ = toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair
            targetStage).denominator *
        RFAP.TwoParameterCylinder.denominatorRatio
          (RFAP.FiniteWindowSharpness.pellParameter targetStage) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm]

/-- A coefficient combination in the target critical basis factors through
the target upper denominator and its two-parameter normalized coordinate. -/
theorem target_denominator_linearCombination
    (targetStage : Nat) (left right : GaussianInt) :
    toGaussian
        (linearCombination
          (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
          (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)
          left right).denominator =
      toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair
            targetStage).denominator *
        RFAP.TwoParameterCylinder.normalizedDenominator
          (RFAP.FiniteWindowSharpness.pellParameter targetStage)
          left right := by
  simp only [linearCombination, toGaussian_add, toGaussian_mul]
  rw [target_denominator_lower]
  unfold RFAP.TwoParameterCylinder.normalizedDenominator
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

private theorem target_upperDenominator_normSq_pos (targetStage : Nat) :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (toGaussian
        (RFAP.FiniteWindowSharpness.criticalUpperPair
          targetStage).denominator) := by
  apply RFAP.ConstructiveGaussian.Gaussian.normSq_pos
  intro zero
  exact RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero
    targetStage (toGaussian_eq_zero.mp zero)

/-- A coefficient combination in a transported critical basis factors
through its exact lower error and its two-parameter normalized coordinate. -/
theorem TransportedNormalForm.error_linearCombination
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (left right : GaussianInt) :
    RFAP.HurwitzApproximation.error source.value
        (linearCombination
          (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
          (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)
          left right) =
      normal.lowerError *
        RFAP.TwoParameterCylinder.normalizedError
          (RFAP.FiniteWindowSharpness.pellParameter errorStage)
          left right := by
  rw [RFAP.BestApproximation.error_linearCombination,
    TransportedNormalForm.lowerIdentity normal,
    TransportedNormalForm.upperIdentity normal]
  unfold RFAP.TwoParameterCylinder.normalizedError
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

/-- Every transported finite critical normal form supplies a full global
consecutive-best certificate through the two-parameter cylinder theorem. -/
theorem TransportedNormalForm.strictExteriorCertificate
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    RFAP.BasisCylinder.StrictExteriorCertificate source.value
      (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
      (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) := by
  refine
    { indexOne :=
        RFAP.FiniteWindowSharpness.criticalPair_indexOne targetStage
      lowerDenominatorNonzero :=
        RFAP.FiniteWindowSharpness.criticalLower_denominator_ne_zero
          targetStage
      upperDenominatorNonzero :=
        RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero
          targetStage
      errorOrder := ?_
      denominatorOrder :=
        RFAP.FiniteWindowSharpness.critical_denominatorQuadrance_ordered
          targetStage
      bothNonzeroExterior := ?_ }
  · unfold errorQuadrance
    rw [normal.lowerIdentity, normal.upperIdentity]
    have ratioStrict :=
      RFAP.TwoParameterCylinder.normSq_errorRatio_lt_one
        (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical errorStage)
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (normal.lowerError *
            RFAP.TwoParameterCylinder.errorRatio
              (RFAP.FiniteWindowSharpness.pellParameter errorStage)) =
        RFAP.ConstructiveGaussian.Gaussian.normSq normal.lowerError *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.TwoParameterCylinder.errorRatio
              (RFAP.FiniteWindowSharpness.pellParameter errorStage)) := by
        rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
      _ < RFAP.ConstructiveGaussian.Gaussian.normSq normal.lowerError * 1 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          normal.lowerErrorPositive ratioStrict
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq normal.lowerError := by
        ring1
  · intro left right leftNonzero rightNonzero
    rcases RFAP.TwoParameterCylinder.strictExterior
        (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical errorStage)
        (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical targetStage)
        left right leftNonzero rightNonzero with
      errorExterior | denominatorExterior
    · left
      unfold errorQuadrance
      rw [normal.lowerIdentity, normal.error_linearCombination]
      calc
        RFAP.ConstructiveGaussian.Gaussian.normSq normal.lowerError =
            RFAP.ConstructiveGaussian.Gaussian.normSq normal.lowerError * 1 := by
          ring1
        _ < RFAP.ConstructiveGaussian.Gaussian.normSq normal.lowerError *
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (RFAP.TwoParameterCylinder.normalizedError
                (RFAP.FiniteWindowSharpness.pellParameter errorStage)
                left right) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            normal.lowerErrorPositive errorExterior
        _ = RFAP.ConstructiveGaussian.Gaussian.normSq
            (normal.lowerError *
              RFAP.TwoParameterCylinder.normalizedError
                (RFAP.FiniteWindowSharpness.pellParameter errorStage)
                left right) := by
          exact (RFAP.ConstructiveGaussian.Gaussian.normSq_mul _ _).symm
    · right
      apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
      unfold denominatorQuadrance
      rw [← normSq_toGaussian, ← normSq_toGaussian,
        target_denominator_linearCombination]
      calc
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (toGaussian
              (RFAP.FiniteWindowSharpness.criticalUpperPair
                targetStage).denominator) =
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (toGaussian
                (RFAP.FiniteWindowSharpness.criticalUpperPair
                  targetStage).denominator) * 1 := by
            ring1
        _ < RFAP.ConstructiveGaussian.Gaussian.normSq
              (toGaussian
                (RFAP.FiniteWindowSharpness.criticalUpperPair
                  targetStage).denominator) *
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (RFAP.TwoParameterCylinder.normalizedDenominator
                (RFAP.FiniteWindowSharpness.pellParameter targetStage)
                left right) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            (target_upperDenominator_normSq_pos targetStage)
            denominatorExterior
        _ = RFAP.ConstructiveGaussian.Gaussian.normSq
            (toGaussian
                (RFAP.FiniteWindowSharpness.criticalUpperPair
                  targetStage).denominator *
              RFAP.TwoParameterCylinder.normalizedDenominator
                (RFAP.FiniteWindowSharpness.pellParameter targetStage)
                left right) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]

private theorem TransportedNormalForm.lowerError_ne_zero
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    normal.lowerError ≠ 0 := by
  intro zero
  have normZero := congrArg RFAP.ConstructiveGaussian.Gaussian.normSq zero
  rw [RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at normZero
  exact (ne_of_gt normal.lowerErrorPositive) normZero

/-- The abstract consecutive-window error ratio is exactly the earlier Pell
parameter carried by the transported normal form. -/
theorem TransportedNormalForm.errorRatio_eq
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    RFAP.DirichletWindow.errorRatio source.value
        (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
        (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) =
      RFAP.TwoParameterCylinder.errorRatio
        (RFAP.FiniteWindowSharpness.pellParameter errorStage) := by
  unfold RFAP.DirichletWindow.errorRatio
  rw [normal.lowerIdentity, normal.upperIdentity]
  calc
    (normal.lowerError *
          RFAP.TwoParameterCylinder.errorRatio
            (RFAP.FiniteWindowSharpness.pellParameter errorStage)) *
        RFAP.ConstructiveGaussian.Gaussian.inv normal.lowerError =
      RFAP.TwoParameterCylinder.errorRatio
          (RFAP.FiniteWindowSharpness.pellParameter errorStage) *
        (normal.lowerError *
          RFAP.ConstructiveGaussian.Gaussian.inv normal.lowerError) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm normal.lowerError,
        RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = RFAP.TwoParameterCylinder.errorRatio
        (RFAP.FiniteWindowSharpness.pellParameter errorStage) * 1 := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_inv _
        normal.lowerError_ne_zero]
    _ = RFAP.TwoParameterCylinder.errorRatio
        (RFAP.FiniteWindowSharpness.pellParameter errorStage) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]

/-- The denominator ratio at the transported target remains the later Pell
parameter built into that explicit pair basis. -/
theorem transportedDenominatorRatio_eq (targetStage : Nat) :
    RFAP.DirichletWindow.denominatorRatio
        (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
        (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) =
      RFAP.TwoParameterCylinder.denominatorRatio
        (RFAP.FiniteWindowSharpness.pellParameter targetStage) := by
  rw [RFAP.FiniteWindowSharpness.criticalPair_denominatorRatio,
    criticalDenominatorRatio_eq_twoParameter]

/-- The normalized determinant gap of a transported same-source window is
the exact two-parameter rational gap. -/
theorem TransportedNormalForm.normalizedGap_eq
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (1 - RFAP.DirichletWindow.denominatorRatio
            (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
            (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) *
          RFAP.DirichletWindow.errorRatio source.value
            (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
            (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)) =
      RFAP.TwoParameterCylinder.gap
        (RFAP.FiniteWindowSharpness.pellParameter errorStage)
        (RFAP.FiniteWindowSharpness.pellParameter targetStage) := by
  rw [normal.errorRatio_eq, transportedDenominatorRatio_eq]
  rfl

/-- Exact index-one product identity for every transported finite window. -/
theorem TransportedNormalForm.window_mul_gap_eq_one
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) :
    dirichletWindowQuadrance source.value
          (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
          (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) *
        RFAP.TwoParameterCylinder.gap
          (RFAP.FiniteWindowSharpness.pellParameter errorStage)
          (RFAP.FiniteWindowSharpness.pellParameter targetStage) = 1 := by
  have consecutive := normal.strictExteriorCertificate.areConsecutiveBest
  have identity :=
    RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindow_mul_normalizedGap_eq_index
      consecutive
  rw [normal.normalizedGap_eq,
    RFAP.FiniteWindowSharpness.criticalPair_indexOne] at identity
  exact identity

/-- A threshold strictly above the exact transported gap is violated by the
corresponding displayed same-source Dirichlet window. -/
theorem TransportedNormalForm.one_lt_threshold_mul_window
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (threshold : Coordinate)
    (gapStrict :
      RFAP.TwoParameterCylinder.gap
          (RFAP.FiniteWindowSharpness.pellParameter errorStage)
          (RFAP.FiniteWindowSharpness.pellParameter targetStage) < threshold) :
    1 < threshold * dirichletWindowQuadrance source.value
      (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
      (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) := by
  let window := dirichletWindowQuadrance source.value
    (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
    (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)
  let gap := RFAP.TwoParameterCylinder.gap
    (RFAP.FiniteWindowSharpness.pellParameter errorStage)
    (RFAP.FiniteWindowSharpness.pellParameter targetStage)
  have productIdentity : window * gap = 1 := by
    simpa only [window, gap] using normal.window_mul_gap_eq_one
  have gapNonnegative : (0 : Coordinate) ≤ gap := by
    dsimp only [gap, RFAP.TwoParameterCylinder.gap]
    exact RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  have gapTimesWindowPositive : 0 < gap * window := by
    calc
      (0 : Coordinate) < 1 := by decide
      _ = gap * window := by rw [RFAP.ConstructiveFraction.mul_comm,
        productIdentity]
  have windowPositive : 0 < window :=
    RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
      gapTimesWindowPositive gapNonnegative
  calc
    (1 : Coordinate) = gap * window := by
      rw [RFAP.ConstructiveFraction.mul_comm, productIdentity]
    _ < threshold * window :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        (by simpa only [gap] using gapStrict) windowPositive

/-- Once the earlier error stage lies beyond the explicit sharpness stage,
every later transported denominator stage has gap below the same proposed
sharper threshold. -/
theorem transportedGap_lt_sharperThreshold
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale backwardStage targetStage : Nat)
    (backwardBeyond :
      RFAP.FiniteWindowSharpness.sharpnessStage threshold requestedScale ≤
        backwardStage)
    (targetBeyond : backwardStage ≤ targetStage) :
    RFAP.TwoParameterCylinder.gap
        (RFAP.FiniteWindowSharpness.pellParameter backwardStage)
        (RFAP.FiniteWindowSharpness.pellParameter targetStage) < threshold := by
  let baseStage :=
    RFAP.FiniteWindowSharpness.sharpnessStage threshold requestedScale
  have errorParameterOrder :
      RFAP.FiniteWindowSharpness.pellParameter baseStage ≤
        RFAP.FiniteWindowSharpness.pellParameter backwardStage :=
    RFAP.CriticalBranch.pellParameter_le_of_le backwardBeyond
  have denominatorStageOrder : baseStage ≤ targetStage :=
    backwardBeyond.trans targetBeyond
  have denominatorParameterOrder :
      RFAP.FiniteWindowSharpness.pellParameter baseStage ≤
        RFAP.FiniteWindowSharpness.pellParameter targetStage :=
    RFAP.CriticalBranch.pellParameter_le_of_le denominatorStageOrder
  have mixedGapBound := RFAP.TwoParameterCylinder.gap_antitone
    (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical backwardStage)
    (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical baseStage)
    (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical targetStage)
    errorParameterOrder denominatorParameterOrder
  calc
    RFAP.TwoParameterCylinder.gap
          (RFAP.FiniteWindowSharpness.pellParameter backwardStage)
          (RFAP.FiniteWindowSharpness.pellParameter targetStage) ≤
        RFAP.TwoParameterCylinder.gap
          (RFAP.FiniteWindowSharpness.pellParameter baseStage)
          (RFAP.FiniteWindowSharpness.pellParameter baseStage) := mixedGapBound
    _ = RFAP.FiniteWindowSharpness.criticalGap
        (RFAP.FiniteWindowSharpness.pellParameter baseStage) :=
      RFAP.TwoParameterCylinder.diagonalGap_eq_criticalGap _
    _ < threshold := by
      simpa only [baseStage] using
        RFAP.FiniteWindowSharpness.criticalGap_lt_sharperThreshold
          certificate requestedScale

/-- An arbitrary supplied finite transport depth yields a genuine
consecutive-best window at the later target stage for one fixed rational
source. -/
theorem transportedPairs_areConsecutiveBest
    (backwardStage steps : Nat) :
    AreConsecutiveBest
      (RFAP.FiniteWindowSharpness.criticalSource
        (backwardStage + steps)).value
      (RFAP.FiniteWindowSharpness.criticalLowerPair
        (backwardStage + 2 * steps))
      (RFAP.FiniteWindowSharpness.criticalUpperPair
        (backwardStage + 2 * steps)) :=
  (transportedNormalForm backwardStage steps).strictExteriorCertificate
    |>.areConsecutiveBest

private theorem next_lowerError_normSq_pos (stage : Nat) :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
        lowerErrorScale stage) := by
  rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (criticalLowerError_normSq_pos (stage + 1))
    (lowerErrorScale_normSq_pos stage)

private theorem next_upperDenominator_normSq_pos (stage : Nat) :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (toGaussian
        (RFAP.FiniteWindowSharpness.criticalUpperPair
          (stage + 2)).denominator) := by
  apply RFAP.ConstructiveGaussian.Gaussian.normSq_pos
  intro zero
  exact RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero
    (stage + 2) (toGaussian_eq_zero.mp zero)

/-- The exact strict-basis certificate for the window immediately after the
native window of a supplied positive critical stage. -/
theorem nextStrictExteriorCertificate (stage : Nat) :
    RFAP.BasisCylinder.StrictExteriorCertificate
      (RFAP.FiniteWindowSharpness.criticalSource (stage + 1)).value
      (RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 2))
      (RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 2)) := by
  refine
    { indexOne :=
        RFAP.FiniteWindowSharpness.criticalPair_indexOne (stage + 2)
      lowerDenominatorNonzero :=
        RFAP.FiniteWindowSharpness.criticalLower_denominator_ne_zero
          (stage + 2)
      upperDenominatorNonzero :=
        RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero
          (stage + 2)
      errorOrder := ?_
      denominatorOrder :=
        RFAP.FiniteWindowSharpness.critical_denominatorQuadrance_ordered
          (stage + 2)
      bothNonzeroExterior := ?_ }
  · unfold errorQuadrance
    rw [next_error_lower, next_error_upper]
    have ratioStrict :=
      RFAP.TwoParameterCylinder.normSq_errorRatio_lt_one
        (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical stage)
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
              lowerErrorScale stage) *
            RFAP.TwoParameterCylinder.errorRatio
              (RFAP.FiniteWindowSharpness.pellParameter stage)) =
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
              lowerErrorScale stage) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.TwoParameterCylinder.errorRatio
              (RFAP.FiniteWindowSharpness.pellParameter stage)) := by
        rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
      _ < RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
              lowerErrorScale stage) * 1 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (next_lowerError_normSq_pos stage) ratioStrict
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
            lowerErrorScale stage) := by ring1
  · intro left right leftNonzero rightNonzero
    rcases RFAP.TwoParameterCylinder.strictExterior
        (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical stage)
        (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical
          (stage + 2)) left right leftNonzero rightNonzero with
      errorExterior | denominatorExterior
    · left
      unfold errorQuadrance
      rw [next_error_lower, next_error_linearCombination]
      calc
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
              lowerErrorScale stage) =
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
                lowerErrorScale stage) * 1 := by ring1
        _ < RFAP.ConstructiveGaussian.Gaussian.normSq
              (RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
                lowerErrorScale stage) *
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (RFAP.TwoParameterCylinder.normalizedError
                (RFAP.FiniteWindowSharpness.pellParameter stage)
                left right) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            (next_lowerError_normSq_pos stage) errorExterior
        _ = RFAP.ConstructiveGaussian.Gaussian.normSq
            ((RFAP.FiniteWindowSharpness.criticalLowerError (stage + 1) *
                lowerErrorScale stage) *
              RFAP.TwoParameterCylinder.normalizedError
                (RFAP.FiniteWindowSharpness.pellParameter stage)
                left right) := by
          exact (RFAP.ConstructiveGaussian.Gaussian.normSq_mul _ _).symm
    · right
      apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
      unfold denominatorQuadrance
      rw [← normSq_toGaussian, ← normSq_toGaussian,
        next_denominator_linearCombination]
      calc
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (toGaussian
              (RFAP.FiniteWindowSharpness.criticalUpperPair
                (stage + 2)).denominator) =
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (toGaussian
                (RFAP.FiniteWindowSharpness.criticalUpperPair
                  (stage + 2)).denominator) * 1 := by ring1
        _ < RFAP.ConstructiveGaussian.Gaussian.normSq
              (toGaussian
                (RFAP.FiniteWindowSharpness.criticalUpperPair
                  (stage + 2)).denominator) *
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (RFAP.TwoParameterCylinder.normalizedDenominator
                (RFAP.FiniteWindowSharpness.pellParameter (stage + 2))
                left right) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            (next_upperDenominator_normSq_pos stage) denominatorExterior
        _ = RFAP.ConstructiveGaussian.Gaussian.normSq
            (toGaussian
                (RFAP.FiniteWindowSharpness.criticalUpperPair
                  (stage + 2)).denominator *
              RFAP.TwoParameterCylinder.normalizedDenominator
                (RFAP.FiniteWindowSharpness.pellParameter (stage + 2))
                left right) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]

/-- The next critical pair basis is a genuine consecutive-best window for
the same rational source as the native window at stage `stage + 1`. -/
theorem nextPairs_areConsecutiveBest (stage : Nat) :
    AreConsecutiveBest
      (RFAP.FiniteWindowSharpness.criticalSource (stage + 1)).value
      (RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 2))
      (RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 2)) :=
  (nextStrictExteriorCertificate stage).areConsecutiveBest

/-- At every supplied finite stage, one displayed rational source supports
its native critical window and the immediately following, strictly
scale-separated critical window. -/
theorem criticalSource_succ_supports_two_windows (stage : Nat) :
    AreConsecutiveBest
        (RFAP.FiniteWindowSharpness.criticalSource (stage + 1)).value
        (RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 1))
        (RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 1)) ∧
      AreConsecutiveBest
        (RFAP.FiniteWindowSharpness.criticalSource (stage + 1)).value
        (RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 2))
        (RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 2)) ∧
      denominatorQuadrance
          (RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 1)) <
        denominatorQuadrance
          (RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 2)) :=
  ⟨RFAP.FiniteWindowSharpness.criticalPairs_areConsecutiveBest (stage + 1),
    nextPairs_areConsecutiveBest stage,
    RFAP.CriticalBranch.criticalUpper_lt_nextLower_denominatorQuadrance
      (stage + 1)⟩

/-- Positive-stage form of the adjacent-window theorem, convenient when the
current stage was computed from a threshold and requested scale. -/
theorem criticalSource_supports_next_of_pos
    (currentStage : Nat) (positive : 0 < currentStage) :
    AreConsecutiveBest
        (RFAP.FiniteWindowSharpness.criticalSource currentStage).value
        (RFAP.FiniteWindowSharpness.criticalLowerPair currentStage)
        (RFAP.FiniteWindowSharpness.criticalUpperPair currentStage) ∧
      AreConsecutiveBest
        (RFAP.FiniteWindowSharpness.criticalSource currentStage).value
        (RFAP.FiniteWindowSharpness.criticalLowerPair (currentStage + 1))
        (RFAP.FiniteWindowSharpness.criticalUpperPair (currentStage + 1)) ∧
      denominatorQuadrance
          (RFAP.FiniteWindowSharpness.criticalUpperPair currentStage) <
        denominatorQuadrance
          (RFAP.FiniteWindowSharpness.criticalLowerPair (currentStage + 1)) := by
  obtain ⟨stage, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simpa only [Nat.succ_eq_add_one] using
    criticalSource_succ_supports_two_windows stage

end RFAP.CriticalTwoWindowTower
