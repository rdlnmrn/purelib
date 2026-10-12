module
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.NatCast
import Purelib.Data.GaussianInt.Pair.Basic
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Pair.Basis
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.NumberTheory.Approximation.Best.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Parameter
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.Basic
import Purelib.NumberTheory.Pell.FiniteBranch
import Purelib.Data.GaussianInt.Conjugate
import Purelib.Data.GaussianInt.Embedding
import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Tactic.Ring

public section

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

open Purelib.NumberTheory

section

/-!
# Pell-indexed Gaussian pairs

The finite Pell denominator and numerator determine the original lower and upper
Gaussian pairs. Their determinant, normalized coordinate ratios and exact
cylinder certificates retain the same stage and source data.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair

/-! ## Concrete Gaussian pairs and their displayed source -/

/-- Lower coefficient pair for the stage-`k` critical window. -/
@[expose] def criticalLowerPair (stage : Nat) :
  GaussianInt.Pair.Basic.ConvergentPair :=
  { numerator :=
      ⟨-2 * (Pell.FiniteBranch.pellNumerator stage : Int), 0⟩
    denominator :=
      ⟨(Pell.FiniteBranch.pellNumerator stage : Int),
        -(Pell.FiniteBranch.pellDenominator stage : Int)⟩ }

/-- Upper coefficient pair for the stage-`k` critical window. -/
@[expose] def criticalUpperPair (stage : Nat) :
  GaussianInt.Pair.Basic.ConvergentPair :=
  { numerator :=
      ⟨-(Pell.FiniteBranch.pellNumerator stage : Int),
        -(Pell.FiniteBranch.pellDenominator stage : Int)⟩
    denominator :=
      ⟨2 * (Pell.FiniteBranch.pellDenominator stage : Int), 0⟩ }

/-- The displayed lower and upper Pell pairs have Gaussian determinant one.

The real determinant coordinate is the finite Pell equation; its imaginary coordinate vanishes by direct arithmetic. -/
theorem criticalPair_determinant (stage : Nat) :
    GaussianInt.Pair.LinearCombination.coefficientDeterminant (criticalLowerPair stage)
      (criticalUpperPair stage) = 1 := by
  have castEquation := congrArg (fun value : Nat => (value : Int))
    (Pell.FiniteBranch.pellEquation stage)
  simp only [Algebra.NatCast.add, Algebra.NatCast.mul, Algebra.NatCast.pow, Nat.cast_ofNat, -eq_self, -iff_self]
    at castEquation
  apply GaussianInt.ext
  · simp only [GaussianInt.Pair.LinearCombination.coefficientDeterminant, GaussianInt.Pair.Basis.determinant,
      criticalLowerPair,
      criticalUpperPair,
      GaussianInt.sub_re,
      GaussianInt.mul_re,
      GaussianInt.one_re, -eq_self, -iff_self]
    calc
      (-2 * (Pell.FiniteBranch.pellNumerator stage : Int)) *
              (2 * (Pell.FiniteBranch.pellDenominator stage : Int)) - 0 * 0 -
            (-(Pell.FiniteBranch.pellNumerator stage : Int) *
                (Pell.FiniteBranch.pellNumerator stage : Int) -
              -(Pell.FiniteBranch.pellDenominator stage : Int) *
                -(Pell.FiniteBranch.pellDenominator stage : Int)) =
          (Pell.FiniteBranch.pellNumerator stage : Int) ^ 2 +
              (Pell.FiniteBranch.pellDenominator stage : Int) ^ 2 -
            4 * (Pell.FiniteBranch.pellNumerator stage : Int) *
              (Pell.FiniteBranch.pellDenominator stage : Int) := by ring1
      _ = 1 := by rw [castEquation]; ring1
  · simp only [GaussianInt.Pair.LinearCombination.coefficientDeterminant, GaussianInt.Pair.Basis.determinant,
      criticalLowerPair,
      criticalUpperPair,
      GaussianInt.sub_im,
      GaussianInt.mul_im,
      GaussianInt.one_im, -eq_self, -iff_self]
    ring1

/-- The critical pair basis has coefficient-index quadrance one at every finite stage. -/
theorem criticalPair_indexOne (stage : Nat) :
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance (criticalLowerPair stage)
      (criticalUpperPair stage) = 1 := by
  unfold GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance
  rw [criticalPair_determinant]
  rfl

section
open Purelib.Data Purelib.NumberTheory
open Purelib.NumberTheory.Approximation

/-- The lower critical denominator has the sum of the two Pell component squares.

The real component retains the stage numerator and the imaginary component
retains the negated stage denominator; negation preserves its natural magnitude. -/
theorem criticalLower_denominatorQuadrance (stage :
  Nat) :
    Best.Error.denominatorQuadrance (criticalLowerPair stage) =
      Pell.FiniteBranch.pellNumerator stage ^ 2 + Pell.FiniteBranch.pellDenominator stage ^ 2 := by
  unfold Best.Error.denominatorQuadrance criticalLowerPair
  rw [GaussianInt.Norm.Basic.normNat_eq_component_squares]
  rw [Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast]
  change (1 * Pell.FiniteBranch.pellNumerator stage) *
        Pell.FiniteBranch.pellNumerator stage +
      (1 * Pell.FiniteBranch.pellDenominator stage) *
        Pell.FiniteBranch.pellDenominator stage = _
  rw [Nat.one_mul, Nat.one_mul, pow_two, pow_two]

/-- The upper critical denominator has four times the Pell denominator square.

Its real component is twice the retained stage denominator and its imaginary
component is zero, so the quadrance is the square of that doubled magnitude. -/
theorem criticalUpper_denominatorQuadrance (stage :
  Nat) :
    Best.Error.denominatorQuadrance (criticalUpperPair stage) =
      4 * Pell.FiniteBranch.pellDenominator stage ^ 2 := by
  unfold Best.Error.denominatorQuadrance criticalUpperPair
  rw [GaussianInt.Norm.Basic.normNat_eq_component_squares]
  rw [Int.Arithmetic.natAbs_mul, Int.natAbs_natCast,
    Int.natAbs_zero]
  change (1 * (2 * Pell.FiniteBranch.pellDenominator stage)) *
        (2 * Pell.FiniteBranch.pellDenominator stage) +
      (1 * 0) * 0 = _
  rw [Nat.one_mul, Nat.mul_zero, Nat.add_zero, pow_two]
  ring1

end

/-- Each next critical upper denominator quadrance strictly exceeds nine times the current one.

The upper denominator quadrance is four times the Pell denominator
square. The finite denominator recurrence grows by more than a factor of
three, and the owned square-comparison law squares that strict growth.
-/
theorem nine_mul_upperQuadrance_lt_succ
    (stage : Nat) :
    9 * Best.Error.denominatorQuadrance (criticalUpperPair stage) <
      Best.Error.denominatorQuadrance (criticalUpperPair (stage + 1)) := by
  rewrite [criticalUpper_denominatorQuadrance, criticalUpper_denominatorQuadrance]
  have squareStrict := Pell.FiniteBranch.natMulSelf_lt_natMulSelf
    (Pell.FiniteBranch.three_mul_pellDenominator_lt_succ stage)
  calc
    9 * (4 * Pell.FiniteBranch.pellDenominator stage ^ 2) =
        4 * ((3 * Pell.FiniteBranch.pellDenominator stage) * (3 * Pell.FiniteBranch.pellDenominator stage)) := by ring1
    _ < 4 * (Pell.FiniteBranch.pellDenominator (stage + 1) * Pell.FiniteBranch.pellDenominator (stage + 1)) :=
      Nat.mul_lt_mul_of_pos_left squareStrict (by decide)
    _ = _ := by ring1

/-- The lower critical pair has nonzero denominator at every finite stage. -/
theorem criticalLower_denominator_ne_zero (stage :
  Nat) :
    (criticalLowerPair stage).denominator ≠ 0 := by
  intro zero
  have imaginaryZero := congrArg
    GaussianInt.im zero
  simp only [criticalLowerPair,
    GaussianInt.zero_im, -eq_self, -iff_self] at imaginaryZero
  have denominatorZero : Pell.FiniteBranch.pellDenominator stage = 0 := by
    have castZero : (Pell.FiniteBranch.pellDenominator stage : Int) = 0 :=
      by
        have negated := congrArg (fun value : Int => -value) imaginaryZero
        rw [Int.neg_neg] at negated
        exact negated
    exact Int.ofNat_eq_zero.mp castZero
  exact (Nat.ne_of_gt (Pell.FiniteBranch.pellDenominator_pos stage)) denominatorZero

/-- The upper critical pair has nonzero denominator at every finite stage. -/
theorem criticalUpper_denominator_ne_zero (stage :
  Nat) :
    (criticalUpperPair stage).denominator ≠ 0 := by
  intro zero
  have realZero := congrArg
    GaussianInt.re zero
  simp only [criticalUpperPair,
    GaussianInt.zero_re, -eq_self, -iff_self] at realZero
  have doubledPositive : 0 < 2 * Pell.FiniteBranch.pellDenominator stage :=
    Nat.mul_pos (by decide) (Pell.FiniteBranch.pellDenominator_pos stage)
  exact (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt doubledPositive)) realZero

/-- The critical upper denominator quadrance strictly exceeds the lower one. -/
theorem critical_denominatorQuadrance_ordered (stage :
  Nat) :
    Best.Error.denominatorQuadrance (criticalLowerPair stage) <
      Best.Error.denominatorQuadrance (criticalUpperPair stage) := by
  rw [criticalLower_denominatorQuadrance,
    criticalUpper_denominatorQuadrance]
  have numeratorLtDenominator :
      Pell.FiniteBranch.pellNumerator stage < Pell.FiniteBranch.pellDenominator stage := by
    unfold Pell.FiniteBranch.pellDenominator
    simpa only [Nat.add_zero, -eq_self, -iff_self] using
      Nat.add_lt_add_left (Pell.FiniteBranch.pellDifference_pos stage) (Pell.FiniteBranch.pellNumerator stage)
  have squareStrict : Pell.FiniteBranch.pellNumerator stage ^ 2 <
      Pell.FiniteBranch.pellDenominator stage ^ 2 := by
    simpa only [pow_two, -eq_self, -iff_self] using
      Pell.FiniteBranch.natMulSelf_lt_natMulSelf numeratorLtDenominator
  have denominatorSquarePositive : 0 < Pell.FiniteBranch.pellDenominator stage ^ 2 :=
    by
      simpa only [pow_two, -eq_self, -iff_self] using
        Nat.mul_pos (Pell.FiniteBranch.pellDenominator_pos stage) (Pell.FiniteBranch.pellDenominator_pos stage)
  calc
    Pell.FiniteBranch.pellNumerator stage ^ 2 + Pell.FiniteBranch.pellDenominator stage ^ 2 <
        Pell.FiniteBranch.pellDenominator stage ^ 2 + Pell.FiniteBranch.pellDenominator stage ^ 2 :=
      Nat.add_lt_add_right squareStrict _
    _ = 2 * Pell.FiniteBranch.pellDenominator stage ^ 2 := by ring1
    _ < 4 * Pell.FiniteBranch.pellDenominator stage ^ 2 :=
      Nat.mul_lt_mul_of_pos_right (by decide) denominatorSquarePositive

/-- The embedded lower critical denominator is nonzero. -/
private theorem
  criticalLower_denominatorGaussian_ne_zero (stage :
  Nat) :
    GaussianInt.toGaussian (criticalLowerPair stage).denominator ≠ 0 := by
  intro zero
  exact criticalLower_denominator_ne_zero stage (GaussianInt.toGaussian_eq_zero.mp zero)

/-- The embedded upper critical denominator is nonzero. -/
theorem criticalUpper_denominatorGaussian_ne_zero
  (stage : Nat) :
    GaussianInt.toGaussian (criticalUpperPair stage).denominator ≠ 0 := by
  intro zero
  exact criticalUpper_denominator_ne_zero stage (GaussianInt.toGaussian_eq_zero.mp zero)

/-- The prescribed critical denominator ratio times the upper denominator equals the lower denominator. -/
private theorem criticalDenominatorRatio_mul_upper
  (stage : Nat) :
    Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio (Dirichlet.Critical.Parameter.pellParameter stage) *
        GaussianInt.toGaussian (criticalUpperPair stage).denominator =
      GaussianInt.toGaussian (criticalLowerPair stage).denominator := open Purelib.Algebra in by
  have castNeg := Ring.IntCast.sub (R := Fraction.Rational) (0 : Int)
    (Pell.FiniteBranch.pellDenominator stage : Int)
  rw [Int.Arithmetic.zero_sub, Ring.IntCast.cast_zero, Int.cast_natCast] at castNeg
  have simplifyZero : (0 : Fraction.Rational) - (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) =
      -(Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) := by ring1
  rw [simplifyZero] at castNeg
  apply Gaussian.Basic.ext
  · simp only [Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio, criticalUpperPair,
      criticalLowerPair, GaussianInt.toGaussian,
      Gaussian.Basic.mul_re,
      Ring.IntCast.intCast_mul, Int.cast_ofNat, Int.cast_natCast, Algebra.Ring.IntCast.cast_zero,
      -eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    calc
      Dirichlet.Critical.Cylinder.Basic.half * Dirichlet.Critical.Parameter.pellParameter stage *
            (2 * (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational)) -
              -Dirichlet.Critical.Cylinder.Basic.half * 0 =
          (2 * Dirichlet.Critical.Cylinder.Basic.half) *
            (Dirichlet.Critical.Parameter.pellParameter stage * (Pell.FiniteBranch.pellDenominator stage :
              Fraction.Rational)) := by
        ring1
      _ = (Pell.FiniteBranch.pellNumerator stage : Fraction.Rational) := by
        rw [Dirichlet.Critical.Cylinder.Basic.two_mul_half, Dirichlet.Critical.Parameter.pellParameter_mul_denominator]
        ring1
  · simp only [Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio, criticalUpperPair,
      criticalLowerPair, GaussianInt.toGaussian,
      Gaussian.Basic.mul_im, castNeg,
      Ring.IntCast.intCast_mul, Int.cast_ofNat, Int.cast_natCast, Algebra.Ring.IntCast.cast_zero,
      -eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    calc
      Dirichlet.Critical.Cylinder.Basic.half * Dirichlet.Critical.Parameter.pellParameter stage * 0 +
            -Dirichlet.Critical.Cylinder.Basic.half * (2 * (Pell.FiniteBranch.pellDenominator stage :
              Fraction.Rational)) =
          -(2 * Dirichlet.Critical.Cylinder.Basic.half) * (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational)
            := by ring1
      _ = -(Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) := by
        rw [Dirichlet.Critical.Cylinder.Basic.two_mul_half]
        ring1

/-- The concrete pair denominators have exactly the prescribed normalized
critical ratio. -/
theorem criticalPair_denominatorRatio (stage : Nat) :
    Dirichlet.Window.Basic.denominatorRatio
        (criticalLowerPair stage) (criticalUpperPair stage) =
      Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio (Dirichlet.Critical.Parameter.pellParameter stage) :=
        by
  apply Gaussian.Field.mul_right_cancel_of_ne
    (criticalUpper_denominatorGaussian_ne_zero stage)
  calc
    Dirichlet.Window.Basic.denominatorRatio
          (criticalLowerPair stage) (criticalUpperPair stage) *
        GaussianInt.toGaussian (criticalUpperPair stage).denominator =
      GaussianInt.toGaussian (criticalLowerPair stage).denominator := by
        unfold Dirichlet.Window.Basic.denominatorRatio
        rw [Gaussian.Basic.mul_assoc,
          Gaussian.Field.inv_mul _
            (criticalUpper_denominatorGaussian_ne_zero stage),
          Gaussian.Basic.mul_one]
    _ = Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio (Dirichlet.Critical.Parameter.pellParameter stage) *
        GaussianInt.toGaussian (criticalUpperPair stage).denominator :=
      (criticalDenominatorRatio_mul_upper stage).symm

/-- The displayed normalized determinant factor. -/
@[expose] def criticalGapVector (value :
  Fraction.Rational) : GaussianInt.Gaussian :=
  1 - Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio value *
    Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio value

/-- The normalized critical determinant vector has quadrance equal to the retained critical gap. -/
@[simp] theorem normSq_criticalGapVector (value :
  Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq (criticalGapVector value) =
      Dirichlet.Critical.Cylinder.Basic.criticalGap value := rfl

/-- The critical determinant vector is nonzero throughout the parameter chamber. -/
theorem criticalGapVector_ne_zero
    {value : Fraction.Rational} (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    criticalGapVector value ≠ 0 := by
  intro zero
  have normZero := congrArg Data.Gaussian.Norm.Basic.normSq zero
  rw [normSq_criticalGapVector, Gaussian.Norm.Basic.normSq_zero] at normZero
  exact (ne_of_gt (Dirichlet.Critical.Cylinder.Basic.criticalGap_pos certificate)) normZero

/-- The lower error is chosen by one displayed inverse so that the basis
determinant identity is exactly one. -/
@[expose] def criticalLowerError (stage : Nat) :
  GaussianInt.Gaussian :=
  -Data.Gaussian.Field.inv
    (GaussianInt.toGaussian (criticalUpperPair stage).denominator *
      criticalGapVector (Dirichlet.Critical.Parameter.pellParameter stage))

/-- Exact Gaussian-rational source determined by the lower pair and its
displayed nonzero error. -/
@[expose] def criticalSourceValue (stage : Nat) :
  GaussianInt.Gaussian :=
  (GaussianInt.toGaussian (criticalLowerPair stage).numerator +
      criticalLowerError stage) *
    Data.Gaussian.Field.inv
      (GaussianInt.toGaussian (criticalLowerPair stage).denominator)

/-- Executable common-denominator presentation of the critical source. -/
@[expose] def criticalSource (stage : Nat) :
  GaussianInt.Fraction :=
  (Gaussian.Basic.Canonical.Fraction.NaturalDenominator.ofGaussian
    (criticalSourceValue stage)).toDisplayed

/-- The common-denominator source record represents the constructed critical Gaussian value exactly. -/
@[simp] theorem criticalSource_value (stage : Nat) :
    (criticalSource stage).value = criticalSourceValue stage := by
  rw [criticalSource, Gaussian.Basic.Canonical.Fraction.NaturalDenominator.toDisplayed_value,
    Gaussian.Basic.Canonical.Fraction.NaturalDenominator.ofGaussian_value]

/-- The chosen inverse expression defining the critical lower error is nonzero. -/
private theorem criticalLowerError_ne_zero (stage :
  Nat) :
    criticalLowerError stage ≠ 0 := by
  unfold criticalLowerError
  apply Gaussian.Field.neg_ne_zero_direct
  rw [← Gaussian.Field.inv_eq]
  apply Gaussian.Field.inv_ne_zero_direct
  exact Gaussian.Field.mul_ne_zero_direct
    (criticalUpper_denominatorGaussian_ne_zero stage)
    (criticalGapVector_ne_zero (Dirichlet.Critical.Parameter.pellParameter_isCritical stage))

/-- The constructed source has the chosen lower division-free error. -/
theorem criticalSource_error_lower (stage : Nat) :
    Best.Error.error (criticalSource stage).value (criticalLowerPair
      stage) =
      criticalLowerError stage := by
  rw [criticalSource_value]
  unfold Best.Error.error criticalSourceValue
  calc
    ((GaussianInt.toGaussian (criticalLowerPair stage).numerator +
          criticalLowerError stage) *
        Data.Gaussian.Field.inv
          (GaussianInt.toGaussian (criticalLowerPair stage).denominator)) *
          GaussianInt.toGaussian (criticalLowerPair stage).denominator -
        GaussianInt.toGaussian (criticalLowerPair stage).numerator =
      (GaussianInt.toGaussian (criticalLowerPair stage).numerator +
          criticalLowerError stage) *
        (Data.Gaussian.Field.inv
            (GaussianInt.toGaussian (criticalLowerPair stage).denominator) *
          GaussianInt.toGaussian (criticalLowerPair stage).denominator) -
        GaussianInt.toGaussian (criticalLowerPair stage).numerator := by
      rw [Gaussian.Basic.mul_assoc]
    _ = (GaussianInt.toGaussian (criticalLowerPair stage).numerator +
          criticalLowerError stage) * 1 -
        GaussianInt.toGaussian (criticalLowerPair stage).numerator := by
      rw [Gaussian.Field.inv_mul _
        (criticalLower_denominatorGaussian_ne_zero stage)]
    _ = criticalLowerError stage := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im, -eq_self, -iff_self] <;>
        ring1

/-- The chosen lower error and prescribed upper error have the determinant identity one.

The upper denominator and normalized gap vector are both nonzero, permitting cancellation of the displayed inverse. -/
private theorem criticalDesiredErrors_determinant
  (stage : Nat) :
    GaussianInt.toGaussian (criticalLowerPair stage).denominator *
          (criticalLowerError stage *
            Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio (Dirichlet.Critical.Parameter.pellParameter stage)) -
        GaussianInt.toGaussian (criticalUpperPair stage).denominator *
          criticalLowerError stage = 1 := by
  have upperGapNonzero :
      GaussianInt.toGaussian (criticalUpperPair stage).denominator *
          criticalGapVector (Dirichlet.Critical.Parameter.pellParameter stage) ≠ 0 :=
    Gaussian.Field.mul_ne_zero_direct
      (criticalUpper_denominatorGaussian_ne_zero stage)
      (criticalGapVector_ne_zero (Dirichlet.Critical.Parameter.pellParameter_isCritical stage))
  calc
    GaussianInt.toGaussian (criticalLowerPair stage).denominator *
          (criticalLowerError stage *
            Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio (Dirichlet.Critical.Parameter.pellParameter stage)) -
        GaussianInt.toGaussian (criticalUpperPair stage).denominator *
          criticalLowerError stage =
      GaussianInt.toGaussian (criticalUpperPair stage).denominator *
        (Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio (Dirichlet.Critical.Parameter.pellParameter stage) *
            Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio (Dirichlet.Critical.Parameter.pellParameter stage) - 1)
              *
          criticalLowerError stage := by
      rw [← criticalDenominatorRatio_mul_upper]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im, -eq_self, -iff_self] <;>
        ring1
    _ =
      (GaussianInt.toGaussian (criticalUpperPair stage).denominator *
          criticalGapVector (Dirichlet.Critical.Parameter.pellParameter stage)) *
        Data.Gaussian.Field.inv
          (GaussianInt.toGaussian (criticalUpperPair stage).denominator *
            criticalGapVector (Dirichlet.Critical.Parameter.pellParameter stage)) := by
      unfold criticalLowerError criticalGapVector
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.neg_re,
          Gaussian.Basic.neg_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im, -eq_self, -iff_self] <;>
        ring1
    _ = 1 :=
      Gaussian.Field.mul_inv _ upperGapNonzero

/-- The upper division-free error has exactly the prescribed normalized
critical ratio. -/
theorem criticalSource_error_upper (stage : Nat) :
    Best.Error.error (criticalSource stage).value (criticalUpperPair
      stage) =
      criticalLowerError stage *
        Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio (Dirichlet.Critical.Parameter.pellParameter stage) := by
  have determinantIdentity :=
    Best.Error.toGaussian_coefficientDeterminant (criticalSource stage).value
      (criticalLowerPair stage) (criticalUpperPair stage)
  rw [criticalPair_determinant, GaussianInt.toGaussian_one,
    criticalSource_error_lower] at determinantIdentity
  have desiredIdentity := criticalDesiredErrors_determinant stage
  have scaledEquality :
      GaussianInt.toGaussian (criticalLowerPair stage).denominator *
          Best.Error.error (criticalSource stage).value
            (criticalUpperPair stage) =
        GaussianInt.toGaussian (criticalLowerPair stage).denominator *
          (criticalLowerError stage *
            Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio (Dirichlet.Critical.Parameter.pellParameter stage)) :=
              by
    calc
      GaussianInt.toGaussian (criticalLowerPair stage).denominator *
          Best.Error.error (criticalSource stage).value
            (criticalUpperPair stage) =
        (GaussianInt.toGaussian (criticalLowerPair stage).denominator *
              Best.Error.error (criticalSource stage).value
                (criticalUpperPair stage) -
            GaussianInt.toGaussian (criticalUpperPair stage).denominator *
              criticalLowerError stage) +
          GaussianInt.toGaussian (criticalUpperPair stage).denominator *
            criticalLowerError stage := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im, -eq_self, -iff_self] <;>
          ring1
      _ = 1 + GaussianInt.toGaussian (criticalUpperPair stage).denominator *
          criticalLowerError stage := by rw [← determinantIdentity]
      _ =
        (GaussianInt.toGaussian (criticalLowerPair stage).denominator *
              (criticalLowerError stage *
                Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio (Dirichlet.Critical.Parameter.pellParameter stage))
                  -
            GaussianInt.toGaussian (criticalUpperPair stage).denominator *
              criticalLowerError stage) +
          GaussianInt.toGaussian (criticalUpperPair stage).denominator *
            criticalLowerError stage := by rw [desiredIdentity]
      _ = GaussianInt.toGaussian (criticalLowerPair stage).denominator *
          (criticalLowerError stage *
            Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio (Dirichlet.Critical.Parameter.pellParameter stage)) :=
              by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im, -eq_self, -iff_self] <;>
          ring1
  apply Gaussian.Field.mul_right_cancel_of_ne
    (criticalLower_denominatorGaussian_ne_zero stage)
  calc
    Best.Error.error (criticalSource stage).value (criticalUpperPair
      stage) *
          GaussianInt.toGaussian (criticalLowerPair stage).denominator =
        GaussianInt.toGaussian (criticalLowerPair stage).denominator *
          Best.Error.error (criticalSource stage).value
            (criticalUpperPair stage) := by
      rw [Gaussian.Basic.mul_comm]
    _ = GaussianInt.toGaussian (criticalLowerPair stage).denominator *
        (criticalLowerError stage *
          Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio (Dirichlet.Critical.Parameter.pellParameter stage)) :=
            scaledEquality
    _ = (criticalLowerError stage *
          Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio (Dirichlet.Critical.Parameter.pellParameter stage)) *
        GaussianInt.toGaussian (criticalLowerPair stage).denominator := by
      rw [Gaussian.Basic.mul_comm]

/-- A nonzero coefficient pair inside the lower normalized critical cylinder lies on both boundaries.

The finite coefficient bound excludes two nonzero coefficients; the remaining unit multiple forces both quadrance
equalities. -/
private theorem criticalLower_normalized_boundary
    {value : Fraction.Rational} (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value)
    (left right : GaussianInt) (coefficientNonzero : left ≠ 0 ∨ right ≠ 0)
    (errorBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio value) ≤ 1)
    (denominatorBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio value +
        GaussianInt.toGaussian right) ≤ Dirichlet.Critical.Cylinder.Basic.criticalCoordinateNorm value) :
    Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio value) = 1 ∧
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio value +
        GaussianInt.toGaussian right) = Dirichlet.Critical.Cylinder.Basic.criticalCoordinateNorm value := by
  have coordinateLtOne := Dirichlet.Critical.Cylinder.Basic.criticalCoordinateNorm_lt_one certificate
  have denominatorBoundOne :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio value +
        GaussianInt.toGaussian right) ≤ 1 := denominatorBound.trans coordinateLtOne.le
  have small := Dirichlet.Critical.Cylinder.Basic.coefficient_normNat_lt_four_of_critical_inside
    certificate left right errorBound denominatorBoundOne
  by_cases leftZero : left = 0
  · have rightNonzero : right ≠ 0 := by
      rcases coefficientNonzero with impossible | rightNonzero
      · exact (impossible leftZero).elim
      · exact rightNonzero
    have oneLeRight : 1 ≤ GaussianInt.normNat right :=
      GaussianInt.normNat_pos rightNonzero
    have oneLeDenominator :
        (1 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
            Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio value +
            GaussianInt.toGaussian right) := by
      rw [leftZero, GaussianInt.toGaussian_zero,
        Gaussian.Basic.zero_mul,
        Gaussian.Basic.zero_add, GaussianInt.normSq_toGaussian]
      exact Fraction.Cast.Order.natCast_le_direct oneLeRight
    exact (not_lt_of_ge
      (oneLeDenominator.trans denominatorBound) coordinateLtOne).elim
  · by_cases rightZero : right = 0
    · have oneLeLeft : 1 ≤ GaussianInt.normNat left :=
        GaussianInt.normNat_pos leftZero
      have castLeftLeOne : (GaussianInt.normNat left : Fraction.Rational) ≤ 1 := by
        simpa only [rightZero, GaussianInt.toGaussian_zero,
          Gaussian.Basic.zero_mul,
          Gaussian.Basic.add_zero,
          GaussianInt.normSq_toGaussian, -eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt] using errorBound
      have leftLeOne : GaussianInt.normNat left ≤ 1 :=
        (Fraction.Cast.Order.natCast_le_iff_direct).1 castLeftLeOne
      have leftNorm : GaussianInt.normNat left = 1 :=
        Nat.le_antisymm leftLeOne oneLeLeft
      constructor
      · rw [rightZero, GaussianInt.toGaussian_zero,
          Gaussian.Basic.zero_mul,
          Gaussian.Basic.add_zero, GaussianInt.normSq_toGaussian,
          leftNorm, Nat.cast_one]
      · rw [rightZero, GaussianInt.toGaussian_zero,
          Gaussian.Basic.add_zero, Gaussian.Norm.Basic.normSq_mul,
          GaussianInt.normSq_toGaussian, Dirichlet.Critical.Cylinder.Basic.normSq_criticalDenominatorRatio, leftNorm]
        ring1
    · rcases Dirichlet.Critical.Cylinder.Basic.small_nonzero_coefficients_strictly_exterior
          certificate left right leftZero rightZero small.1 small.2 with
        errorExterior | denominatorExterior
      · exact (not_lt_of_ge errorBound errorExterior).elim
      · exact (not_lt_of_ge
          (denominatorBound.trans coordinateLtOne.le)
          denominatorExterior).elim

/-- A nonzero coefficient pair inside the upper normalized critical cylinder lies on both boundaries.

The finite coefficient bound excludes two nonzero coefficients; the remaining unit multiple forces both quadrance
equalities. -/
private theorem criticalUpper_normalized_boundary
    {value : Fraction.Rational} (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value)
    (left right : GaussianInt) (coefficientNonzero : left ≠ 0 ∨ right ≠ 0)
    (errorBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio value) ≤
          Dirichlet.Critical.Cylinder.Basic.criticalCoordinateNorm value)
    (denominatorBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio value +
        GaussianInt.toGaussian right) ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio value) =
          Dirichlet.Critical.Cylinder.Basic.criticalCoordinateNorm value ∧
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio value +
        GaussianInt.toGaussian right) = 1 := by
  have coordinateLtOne := Dirichlet.Critical.Cylinder.Basic.criticalCoordinateNorm_lt_one certificate
  have errorBoundOne :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio value) ≤ 1 :=
    errorBound.trans coordinateLtOne.le
  have small := Dirichlet.Critical.Cylinder.Basic.coefficient_normNat_lt_four_of_critical_inside
    certificate left right errorBoundOne denominatorBound
  by_cases rightZero : right = 0
  · have leftNonzero : left ≠ 0 := by
      rcases coefficientNonzero with leftNonzero | impossible
      · exact leftNonzero
      · exact (impossible rightZero).elim
    have oneLeLeft : 1 ≤ GaussianInt.normNat left :=
      GaussianInt.normNat_pos leftNonzero
    have oneLeError :
        (1 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
            GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio value) := by
      rw [rightZero, GaussianInt.toGaussian_zero,
        Gaussian.Basic.zero_mul,
        Gaussian.Basic.add_zero, GaussianInt.normSq_toGaussian]
      exact Fraction.Cast.Order.natCast_le_direct oneLeLeft
    exact (not_lt_of_ge
      (oneLeError.trans errorBound) coordinateLtOne).elim
  · by_cases leftZero : left = 0
    · have oneLeRight : 1 ≤ GaussianInt.normNat right :=
        GaussianInt.normNat_pos rightZero
      have castRightLeOne : (GaussianInt.normNat right : Fraction.Rational) ≤ 1 := by
        simpa only [leftZero, GaussianInt.toGaussian_zero,
          Gaussian.Basic.zero_mul,
          Gaussian.Basic.zero_add,
          GaussianInt.normSq_toGaussian, -eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt] using
            denominatorBound
      have rightLeOne : GaussianInt.normNat right ≤ 1 :=
        (Fraction.Cast.Order.natCast_le_iff_direct).1 castRightLeOne
      have rightNorm : GaussianInt.normNat right = 1 :=
        Nat.le_antisymm rightLeOne oneLeRight
      constructor
      · rw [leftZero, GaussianInt.toGaussian_zero,
          Gaussian.Basic.zero_add, Gaussian.Norm.Basic.normSq_mul,
          GaussianInt.normSq_toGaussian, Dirichlet.Critical.Cylinder.Basic.normSq_criticalErrorRatio, rightNorm]
        ring1
      · rw [leftZero, GaussianInt.toGaussian_zero,
          Gaussian.Basic.zero_mul,
          Gaussian.Basic.zero_add, GaussianInt.normSq_toGaussian,
          rightNorm, Nat.cast_one]
    · rcases Dirichlet.Critical.Cylinder.Basic.small_nonzero_coefficients_strictly_exterior
          certificate left right leftZero rightZero small.1 small.2 with
        errorExterior | denominatorExterior
      · exact (not_lt_of_ge
          (errorBound.trans coordinateLtOne.le) errorExterior).elim
      · exact (not_lt_of_ge denominatorBound denominatorExterior).elim

/-- The error of a critical basis combination factors through the retained lower error and normalized critical error
ratio. -/
private theorem critical_error_linearCombination
    (stage : Nat) (left right : GaussianInt) :
    Best.Error.error (criticalSource stage).value
        (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
          (criticalUpperPair stage) left right) =
      criticalLowerError stage *
        (GaussianInt.toGaussian left + GaussianInt.toGaussian right *
          Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio (Dirichlet.Critical.Parameter.pellParameter stage)) := by
  rw [Best.Error.error_linearCombination, criticalSource_error_lower,
    criticalSource_error_upper]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im, -eq_self, -iff_self] <;>
    ring1

/-- The denominator of a critical basis combination factors through the retained upper denominator and normalized
denominator ratio. -/
private theorem critical_denominator_linearCombination
    (stage : Nat) (left right : GaussianInt) :
    GaussianInt.toGaussian
        (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
          (criticalUpperPair stage) left right).denominator =
      GaussianInt.toGaussian (criticalUpperPair stage).denominator *
        (GaussianInt.toGaussian left * Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio
          (Dirichlet.Critical.Parameter.pellParameter stage) +
          GaussianInt.toGaussian right) := by
  simp only [GaussianInt.Pair.LinearCombination.linearCombination, GaussianInt.toGaussian_add,
    GaussianInt.toGaussian_mul, -eq_self, -iff_self]
  rw [← criticalDenominatorRatio_mul_upper]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im, -eq_self, -iff_self] <;>
    ring1

/-- A nonzero pair expanded in the critical basis has at least one nonzero coefficient. -/
private theorem coefficientNonzero_of_expansion
    (stage : Nat) (candidate : GaussianInt.Pair.Basic.ConvergentPair) (candidateNonzero :
      GaussianInt.Pair.LinearCombination.PairNonzero candidate)
    (left right : GaussianInt)
    (expansion :
      GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
        (criticalUpperPair stage) left right = candidate) :
    left ≠ 0 ∨ right ≠ 0 := by
  by_cases leftZero : left = 0
  · right
    intro rightZero
    have candidateZero : candidate = GaussianInt.Pair.LinearCombination.zeroPair := by
      calc
        candidate = GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair
          stage)
            (criticalUpperPair stage) left right := expansion.symm
        _ = GaussianInt.Pair.LinearCombination.zeroPair := by
          rw [leftZero, rightZero]
          apply GaussianInt.Pair.LinearCombination.pair_ext <;>
            apply GaussianInt.ext <;>
              simp only [GaussianInt.Pair.LinearCombination.linearCombination,
                GaussianInt.Pair.LinearCombination.zeroPair,
                GaussianInt.zero_re,
                GaussianInt.zero_im,
                GaussianInt.mul_re,
                GaussianInt.mul_im,
                GaussianInt.add_re,
                GaussianInt.add_im, -eq_self, -iff_self] <;>
              ring1
    rcases candidateNonzero with numeratorNonzero | denominatorNonzero
    · exact numeratorNonzero
        (congrArg (fun pair : GaussianInt.Pair.Basic.ConvergentPair => pair.numerator) candidateZero)
    · exact denominatorNonzero
        (congrArg (fun pair : GaussianInt.Pair.Basic.ConvergentPair => pair.denominator) candidateZero)
  · exact Or.inl leftZero

/-- An integral critical basis combination inside the lower cylinder lies on its boundary.

Positive error and denominator scales transport the normalized boundary equalities to the original pair quadrances. -/
private theorem
  criticalLower_linearCombination_boundary
    (stage : Nat) (left right : GaussianInt)
    (coefficientNonzero : left ≠ 0 ∨ right ≠ 0)
    (errorInside :
      Best.Error.errorQuadrance (criticalSource stage).value
          (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        Best.Error.errorQuadrance (criticalSource stage).value
          (criticalLowerPair stage))
    (denominatorInside :
      Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        Best.Error.denominatorQuadrance (criticalLowerPair stage)) :
    Best.Basic.OnCylinderBoundary (criticalSource stage).value
      (criticalLowerPair stage)
      (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
        (criticalUpperPair stage) left right) := by
  have lowerErrorPositive : 0 < Data.Gaussian.Norm.Basic.normSq (criticalLowerError stage)
    :=
    Gaussian.Norm.Basic.normSq_pos (criticalLowerError_ne_zero stage)
  have upperDenominatorPositive :
      0 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
        stage).denominator) :=
    Gaussian.Norm.Basic.normSq_pos (criticalUpper_denominatorGaussian_ne_zero stage)
  have normalizedErrorBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
          (Dirichlet.Critical.Parameter.pellParameter stage)) ≤ 1 := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq (criticalLowerError stage))
    · calc
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
              GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
                (Dirichlet.Critical.Parameter.pellParameter stage)) *
            Data.Gaussian.Norm.Basic.normSq (criticalLowerError stage) =
          Best.Error.errorQuadrance (criticalSource stage).value
            (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) := by
            unfold Best.Error.errorQuadrance
            rw [critical_error_linearCombination, Gaussian.Norm.Basic.normSq_mul]
            ring1
        _ ≤ Best.Error.errorQuadrance (criticalSource stage).value
            (criticalLowerPair stage) := errorInside
        _ = (1 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (criticalLowerError
          stage) := by
          unfold Best.Error.errorQuadrance
          rw [criticalSource_error_lower]
          ring1
    · exact lowerErrorPositive
  have normalizedDenominatorBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
          Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio (Dirichlet.Critical.Parameter.pellParameter stage)
            + GaussianInt.toGaussian right) ≤
        Dirichlet.Critical.Cylinder.Basic.criticalCoordinateNorm (Dirichlet.Critical.Parameter.pellParameter stage) :=
          by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
        stage).denominator))
    · calc
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
              Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio (Dirichlet.Critical.Parameter.pellParameter
                stage) +
            GaussianInt.toGaussian right) *
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
              stage).denominator) =
          (Best.Error.denominatorQuadrance
            (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) : Fraction.Rational) := by
            unfold Best.Error.denominatorQuadrance
            rw [← GaussianInt.normSq_toGaussian,
              critical_denominator_linearCombination, Gaussian.Norm.Basic.normSq_mul]
            ring1
        _ ≤ (Best.Error.denominatorQuadrance (criticalLowerPair stage) : Fraction.Rational) :=
          Fraction.Cast.Order.natCast_le_direct denominatorInside
        _ = Dirichlet.Critical.Cylinder.Basic.criticalCoordinateNorm (Dirichlet.Critical.Parameter.pellParameter stage)
          *
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
              stage).denominator) := by
          unfold Best.Error.denominatorQuadrance
          rw [← GaussianInt.normSq_toGaussian,
            ← criticalDenominatorRatio_mul_upper, Gaussian.Norm.Basic.normSq_mul,
            Dirichlet.Critical.Cylinder.Basic.normSq_criticalDenominatorRatio]
    · exact upperDenominatorPositive
  have normalizedBoundary := criticalLower_normalized_boundary
    (Dirichlet.Critical.Parameter.pellParameter_isCritical stage) left right coefficientNonzero
      normalizedErrorBound normalizedDenominatorBound
  constructor
  · unfold Best.Error.errorQuadrance
    rw [critical_error_linearCombination, criticalSource_error_lower,
      Gaussian.Norm.Basic.normSq_mul, normalizedBoundary.1]
    ring1
  · apply Fraction.Cast.Compatibility.natCast_injective_direct
    unfold Best.Error.denominatorQuadrance
    rw [← GaussianInt.normSq_toGaussian, ← GaussianInt.normSq_toGaussian,
      critical_denominator_linearCombination,
      ← criticalDenominatorRatio_mul_upper,
      Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul,
        Dirichlet.Critical.Cylinder.Basic.normSq_criticalDenominatorRatio,
      normalizedBoundary.2]
    ring1

/-- An integral critical basis combination inside the upper cylinder lies on its boundary.

Positive error and denominator scales transport the normalized boundary equalities to the original pair quadrances. -/
private theorem
  criticalUpper_linearCombination_boundary
    (stage : Nat) (left right : GaussianInt)
    (coefficientNonzero : left ≠ 0 ∨ right ≠ 0)
    (errorInside :
      Best.Error.errorQuadrance (criticalSource stage).value
          (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        Best.Error.errorQuadrance (criticalSource stage).value
          (criticalUpperPair stage))
    (denominatorInside :
      Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        Best.Error.denominatorQuadrance (criticalUpperPair stage)) :
    Best.Basic.OnCylinderBoundary (criticalSource stage).value
      (criticalUpperPair stage)
      (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
        (criticalUpperPair stage) left right) := by
  have lowerErrorPositive : 0 < Data.Gaussian.Norm.Basic.normSq (criticalLowerError stage)
    :=
    Gaussian.Norm.Basic.normSq_pos (criticalLowerError_ne_zero stage)
  have upperDenominatorPositive :
      0 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
        stage).denominator) :=
    Gaussian.Norm.Basic.normSq_pos (criticalUpper_denominatorGaussian_ne_zero stage)
  have normalizedErrorBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
          (Dirichlet.Critical.Parameter.pellParameter stage)) ≤
          Dirichlet.Critical.Cylinder.Basic.criticalCoordinateNorm (Dirichlet.Critical.Parameter.pellParameter stage) :=
            by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq (criticalLowerError stage))
    · calc
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
              GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
                (Dirichlet.Critical.Parameter.pellParameter stage)) *
            Data.Gaussian.Norm.Basic.normSq (criticalLowerError stage) =
          Best.Error.errorQuadrance (criticalSource stage).value
            (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) := by
            unfold Best.Error.errorQuadrance
            rw [critical_error_linearCombination, Gaussian.Norm.Basic.normSq_mul]
            ring1
        _ ≤ Best.Error.errorQuadrance (criticalSource stage).value
            (criticalUpperPair stage) := errorInside
        _ = Dirichlet.Critical.Cylinder.Basic.criticalCoordinateNorm (Dirichlet.Critical.Parameter.pellParameter stage)
          *
            Data.Gaussian.Norm.Basic.normSq (criticalLowerError stage) := by
          unfold Best.Error.errorQuadrance
          rw [criticalSource_error_upper, Gaussian.Norm.Basic.normSq_mul,
            Dirichlet.Critical.Cylinder.Basic.normSq_criticalErrorRatio]
          ring1
    · exact lowerErrorPositive
  have normalizedDenominatorBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
          Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio (Dirichlet.Critical.Parameter.pellParameter stage)
            + GaussianInt.toGaussian right) ≤
        1 := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
        stage).denominator))
    · calc
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
              Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio (Dirichlet.Critical.Parameter.pellParameter
                stage) +
            GaussianInt.toGaussian right) *
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
              stage).denominator) =
          (Best.Error.denominatorQuadrance
            (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) : Fraction.Rational) := by
            unfold Best.Error.denominatorQuadrance
            rw [← GaussianInt.normSq_toGaussian,
              critical_denominator_linearCombination, Gaussian.Norm.Basic.normSq_mul]
            ring1
        _ ≤ (Best.Error.denominatorQuadrance (criticalUpperPair stage) : Fraction.Rational) :=
          Fraction.Cast.Order.natCast_le_direct denominatorInside
        _ = (1 : Fraction.Rational) *
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
              stage).denominator) := by
          unfold Best.Error.denominatorQuadrance
          rw [← GaussianInt.normSq_toGaussian]
          ring1
    · exact upperDenominatorPositive
  have normalizedBoundary := criticalUpper_normalized_boundary
    (Dirichlet.Critical.Parameter.pellParameter_isCritical stage) left right coefficientNonzero
      normalizedErrorBound normalizedDenominatorBound
  constructor
  · unfold Best.Error.errorQuadrance
    rw [critical_error_linearCombination, criticalSource_error_upper,
      Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul,
        Dirichlet.Critical.Cylinder.Basic.normSq_criticalErrorRatio,
      normalizedBoundary.1]
  · apply Fraction.Cast.Compatibility.natCast_injective_direct
    unfold Best.Error.denominatorQuadrance
    rw [← GaussianInt.normSq_toGaussian, ← GaussianInt.normSq_toGaussian,
      critical_denominator_linearCombination, Gaussian.Norm.Basic.normSq_mul,
      normalizedBoundary.2]
    ring1

/-- Every Gaussian integer pair admits a coefficient expansion in the critical index-one basis.

The witnesses are the explicit Cramer determinants multiplied by the conjugate basis determinant. -/
private theorem exists_critical_coefficients (stage :
  Nat) (candidate : GaussianInt.Pair.Basic.ConvergentPair) :
    ∃ left right : GaussianInt,
      GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
        (criticalUpperPair stage) left right = candidate := by
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant
    (criticalLowerPair stage) (criticalUpperPair stage)
  refine ⟨GaussianInt.conj determinantValue *
      GaussianInt.Pair.LinearCombination.coefficientDeterminant candidate (criticalUpperPair
        stage),
    GaussianInt.conj determinantValue *
      GaussianInt.Pair.LinearCombination.coefficientDeterminant (criticalLowerPair stage)
        candidate, ?_⟩
  exact GaussianInt.Pair.LinearCombination.linearCombination_cramer_of_index_one
    (criticalLowerPair stage) (criticalUpperPair stage) candidate
      (criticalPair_indexOne stage)

/-- The lower endpoint of every finite critical window is a genuine best
approximation in the two-tier sense. -/
theorem criticalLower_isBest (stage : Nat) :
    Best.Basic.IsBest (criticalSource stage).value (criticalLowerPair
      stage) := by
  apply (Best.Basic.isBest_iff_isGaussLatticeMinimal
    (criticalSource stage).value (criticalLowerPair stage)).2
  refine ⟨criticalLower_denominator_ne_zero stage, ?_⟩
  intro candidate candidateNonzero inside
  rcases exists_critical_coefficients stage candidate with
    ⟨left, right, expansion⟩
  have coefficientNonzero := coefficientNonzero_of_expansion
    stage candidate candidateNonzero left right expansion
  have errorInside :
      Best.Error.errorQuadrance (criticalSource stage).value
          (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        Best.Error.errorQuadrance (criticalSource stage).value
          (criticalLowerPair stage) := by
    rw [expansion]
    exact inside.1
  have denominatorInside :
      Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        Best.Error.denominatorQuadrance (criticalLowerPair stage) := by
    rw [expansion]
    exact inside.2
  have boundary := criticalLower_linearCombination_boundary stage left right
    coefficientNonzero errorInside denominatorInside
  rw [expansion] at boundary
  exact boundary

/-- The upper endpoint of every finite critical window is also best. -/
theorem criticalUpper_isBest (stage : Nat) :
    Best.Basic.IsBest (criticalSource stage).value (criticalUpperPair
      stage) := by
  apply (Best.Basic.isBest_iff_isGaussLatticeMinimal
    (criticalSource stage).value (criticalUpperPair stage)).2
  refine ⟨criticalUpper_denominator_ne_zero stage, ?_⟩
  intro candidate candidateNonzero inside
  rcases exists_critical_coefficients stage candidate with
    ⟨left, right, expansion⟩
  have coefficientNonzero := coefficientNonzero_of_expansion
    stage candidate candidateNonzero left right expansion
  have errorInside :
      Best.Error.errorQuadrance (criticalSource stage).value
          (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        Best.Error.errorQuadrance (criticalSource stage).value
          (criticalUpperPair stage) := by
    rw [expansion]
    exact inside.1
  have denominatorInside :
      Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        Best.Error.denominatorQuadrance (criticalUpperPair stage) := by
    rw [expansion]
    exact inside.2
  have boundary := criticalUpper_linearCombination_boundary stage left right
    coefficientNonzero errorInside denominatorInside
  rw [expansion] at boundary
  exact boundary

/-- The critical lower-error and upper-denominator mixed cylinder contains no nonzero pair.

An index-one basis expansion reduces any candidate to the certified normalized critical-cylinder exterior. -/
private theorem critical_mixedCylinderEmpty (stage :
  Nat) :
    Best.Consecutive.Basic.MixedCylinderEmpty (criticalSource stage).value
      (criticalLowerPair stage) (criticalUpperPair stage) := by
  intro candidate candidateNonzero inside
  rcases exists_critical_coefficients stage candidate with
    ⟨left, right, expansion⟩
  have coefficientNonzero := coefficientNonzero_of_expansion
    stage candidate candidateNonzero left right expansion
  have lowerErrorPositive : 0 < Data.Gaussian.Norm.Basic.normSq (criticalLowerError stage)
    :=
    Gaussian.Norm.Basic.normSq_pos (criticalLowerError_ne_zero stage)
  have upperDenominatorPositive :
      0 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
        stage).denominator) :=
    Gaussian.Norm.Basic.normSq_pos (criticalUpper_denominatorGaussian_ne_zero stage)
  have normalizedErrorInside :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
          (Dirichlet.Critical.Parameter.pellParameter stage)) < 1 := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq (criticalLowerError stage))
    · calc
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
              GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.Basic.criticalErrorRatio
                (Dirichlet.Critical.Parameter.pellParameter stage)) *
            Data.Gaussian.Norm.Basic.normSq (criticalLowerError stage) =
          Best.Error.errorQuadrance (criticalSource stage).value
            (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) := by
            unfold Best.Error.errorQuadrance
            rw [critical_error_linearCombination, Gaussian.Norm.Basic.normSq_mul]
            ring1
        _ = Best.Error.errorQuadrance (criticalSource stage).value candidate := by
          rw [expansion]
        _ < Best.Error.errorQuadrance (criticalSource stage).value
            (criticalLowerPair stage) := inside.1
        _ = (1 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (criticalLowerError
          stage) := by
          unfold Best.Error.errorQuadrance
          rw [criticalSource_error_lower]
          ring1
    · exact lowerErrorPositive
  have normalizedDenominatorInside :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio (Dirichlet.Critical.Parameter.pellParameter stage) +
          GaussianInt.toGaussian right) <
          1 := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
        stage).denominator))
    · calc
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
              Dirichlet.Critical.Cylinder.Basic.criticalDenominatorRatio (Dirichlet.Critical.Parameter.pellParameter
                stage) +
            GaussianInt.toGaussian right) *
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
              stage).denominator) =
          (Best.Error.denominatorQuadrance
            (GaussianInt.Pair.LinearCombination.linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) : Fraction.Rational) := by
            unfold Best.Error.denominatorQuadrance
            rw [← GaussianInt.normSq_toGaussian,
              critical_denominator_linearCombination, Gaussian.Norm.Basic.normSq_mul]
            ring1
        _ = (Best.Error.denominatorQuadrance candidate : Fraction.Rational) := by rw [expansion]
        _ < (Best.Error.denominatorQuadrance (criticalUpperPair stage) : Fraction.Rational) :=
          Fraction.Cast.Order.natCast_lt_direct inside.2
        _ = (1 : Fraction.Rational) *
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (criticalUpperPair
              stage).denominator) := by
          unfold Best.Error.denominatorQuadrance
          rw [← GaussianInt.normSq_toGaussian]
          ring1
    · exact upperDenominatorPositive
  rcases Dirichlet.Critical.Cylinder.Basic.criticalCylinderExterior
    (Dirichlet.Critical.Parameter.pellParameter_isCritical stage)
      left right coefficientNonzero with errorExterior | denominatorExterior
  · exact (not_lt_of_ge errorExterior normalizedErrorInside)
  · exact (not_lt_of_ge denominatorExterior normalizedDenominatorInside)

/-- Each displayed Pell stage is an actual consecutive pair of best
approximations for its explicitly constructed rational source. -/
theorem criticalPairs_areConsecutiveBest (stage : Nat)
  :
    Best.Consecutive.Basic.AreConsecutiveBest (criticalSource stage).value
      (criticalLowerPair stage) (criticalUpperPair stage) := by
  apply (Best.Consecutive.Basic.areConsecutiveBest_iff_mixedCylinderEmpty
    (criticalSource stage) (criticalLowerPair stage)
      (criticalUpperPair stage)).2
  exact ⟨criticalLower_isBest stage, criticalUpper_isBest stage,
    critical_denominatorQuadrance_ordered stage,
    critical_mixedCylinderEmpty stage⟩
end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair

end
