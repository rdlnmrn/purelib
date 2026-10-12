module
import Purelib.Algebra.NatCast
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Parameter
import Purelib.NumberTheory.Pell.FiniteBranch

import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

open Purelib.NumberTheory

public section

/-!
# Finite recurrence of the critical Pell branch

The critical sharpness pairs are not unrelated witnesses.  Successive pair
bases are connected by one fixed Gaussian-integral unimodular matrix.  This
is the finite algebraic dynamics underlying the candidate coherent critical
branch; it introduces neither its omitted irrational endpoint nor an
infinite sequence object beyond evaluation at a supplied natural stage.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Transition

open Purelib.Algebra

/-- The Gaussian integer coefficient type of the critical pair transition. -/
abbrev GaussianInt := Data.GaussianInt
/-- The retained Gaussian integer numerator-denominator pair type. -/
abbrev Pair := Data.GaussianInt.Pair.Basic.ConvergentPair

/-- Coefficient of the old lower pair in the next lower pair. -/
@[expose] def lowerFromLower : GaussianInt := ⟨0, 1⟩

/-- Coefficient of the old upper pair in the next lower pair. -/
@[expose] def lowerFromUpper : GaussianInt := ⟨0, -2⟩

/-- Coefficient of the old lower pair in the next upper pair. -/
@[expose] def upperFromLower : GaussianInt := ⟨-2, 0⟩

/-- Coefficient of the old upper pair in the next upper pair. -/
@[expose] def upperFromUpper : GaussianInt := ⟨4, -1⟩

/-- The fixed critical-branch coefficient matrix has Gaussian determinant
one. -/
theorem transitionDeterminant :
    Dirichlet.Critical.Transition.lowerFromLower * Dirichlet.Critical.Transition.upperFromUpper -
      Dirichlet.Critical.Transition.lowerFromUpper * Dirichlet.Critical.Transition.upperFromLower = 1 := by
  apply Data.GaussianInt.ext <;>
    simp only [-eq_self, -iff_self, Dirichlet.Critical.Transition.lowerFromLower,
      Dirichlet.Critical.Transition.lowerFromUpper, Dirichlet.Critical.Transition.upperFromLower,
      Dirichlet.Critical.Transition.upperFromUpper,
      Data.GaussianInt.sub_re,
      Data.GaussianInt.sub_im,
      Data.GaussianInt.mul_re,
      Data.GaussianInt.mul_im,
      Data.GaussianInt.one_re,
      Data.GaussianInt.one_im] <;>
    ring1

/-- The next lower critical pair is the same fixed Gaussian-integral linear
combination of the preceding pair basis at every supplied stage. -/
theorem criticalLowerPair_succ (stage : Nat) :
    Dirichlet.Critical.Pair.criticalLowerPair (stage + 1) =
      Data.GaussianInt.Pair.LinearCombination.linearCombination
        (Dirichlet.Critical.Pair.criticalLowerPair stage)
        (Dirichlet.Critical.Pair.criticalUpperPair stage)
        Dirichlet.Critical.Transition.lowerFromLower lowerFromUpper := by
  apply Data.GaussianInt.Pair.LinearCombination.pair_ext <;>
    apply Data.GaussianInt.ext <;>
    simp only [-eq_self, -iff_self, Dirichlet.Critical.Pair.criticalLowerPair,
      Dirichlet.Critical.Pair.criticalUpperPair, Data.GaussianInt.Pair.LinearCombination.linearCombination,
      Dirichlet.Critical.Transition.lowerFromLower, Dirichlet.Critical.Transition.lowerFromUpper,
      Pell.FiniteBranch.pellNumerator_succ,
      Pell.FiniteBranch.pellDifference_succ,
      Pell.FiniteBranch.pellDenominator,
      NatCast.add, NatCast.mul, Nat.cast_ofNat,
      Data.GaussianInt.add_re,
      Data.GaussianInt.add_im,
      Data.GaussianInt.mul_re,
      Data.GaussianInt.mul_im] <;>
    ring1

/-- The next upper critical pair is the same fixed Gaussian-integral linear
combination of the preceding pair basis at every supplied stage. -/
theorem criticalUpperPair_succ (stage : Nat) :
    Dirichlet.Critical.Pair.criticalUpperPair (stage + 1) =
      Data.GaussianInt.Pair.LinearCombination.linearCombination
        (Dirichlet.Critical.Pair.criticalLowerPair stage)
        (Dirichlet.Critical.Pair.criticalUpperPair stage)
        Dirichlet.Critical.Transition.upperFromLower upperFromUpper := by
  apply Data.GaussianInt.Pair.LinearCombination.pair_ext <;>
    apply Data.GaussianInt.ext <;>
    simp only [-eq_self, -iff_self, Dirichlet.Critical.Pair.criticalLowerPair,
      Dirichlet.Critical.Pair.criticalUpperPair, Data.GaussianInt.Pair.LinearCombination.linearCombination,
      Dirichlet.Critical.Transition.upperFromLower, Dirichlet.Critical.Transition.upperFromUpper,
      Pell.FiniteBranch.pellNumerator_succ,
      Pell.FiniteBranch.pellDifference_succ,
      Pell.FiniteBranch.pellDenominator,
      NatCast.add, NatCast.mul, Nat.cast_ofNat,
      Data.GaussianInt.add_re,
      Data.GaussianInt.add_im,
      Data.GaussianInt.mul_re,
      Data.GaussianInt.mul_im] <;>
    ring1

/-- The next Pell numerator is the current denominator. -/
theorem pellNumerator_succ_eq_denominator (stage : Nat) :
    Pell.FiniteBranch.pellNumerator (stage + 1) =
      Pell.FiniteBranch.pellDenominator stage := by
  rw [Pell.FiniteBranch.pellNumerator_succ]
  rfl

/-- Subtraction-free denominator form of `n_(k+1)=4n_k-m_k`. -/
theorem pellDenominator_succ_add_numerator (stage : Nat) :
    Pell.FiniteBranch.pellDenominator (stage + 1) +
        Pell.FiniteBranch.pellNumerator stage =
      4 * Pell.FiniteBranch.pellDenominator stage := by
  unfold Pell.FiniteBranch.pellDenominator
  rw [Pell.FiniteBranch.pellNumerator_succ,
    Pell.FiniteBranch.pellDifference_succ]
  ring1

/-- Division-free form of the finite Pell parameter transition. -/
theorem four_sub_parameter_mul_denominator (stage : Nat) :
    (4 - Dirichlet.Critical.Parameter.pellParameter stage) *
        (Pell.FiniteBranch.pellDenominator stage :
          Fraction.Rational) =
      (Pell.FiniteBranch.pellDenominator (stage + 1) :
        Fraction.Rational) := by
  have castIdentity := congrArg
    (fun value : Nat => (value : Fraction.Rational))
    (Dirichlet.Critical.Transition.pellDenominator_succ_add_numerator stage)
  simp only [-eq_self, -iff_self, NatCast.add, NatCast.mul, Nat.cast_ofNat] at castIdentity
  calc
    (4 - Dirichlet.Critical.Parameter.pellParameter stage) *
          (Pell.FiniteBranch.pellDenominator stage :
            Fraction.Rational) =
        4 * (Pell.FiniteBranch.pellDenominator stage :
            Fraction.Rational) -
          Dirichlet.Critical.Parameter.pellParameter stage *
            (Pell.FiniteBranch.pellDenominator stage :
              Fraction.Rational) := by ring1
    _ = 4 * (Pell.FiniteBranch.pellDenominator stage :
            Fraction.Rational) -
          (Pell.FiniteBranch.pellNumerator stage :
            Fraction.Rational) := by
      rw [Dirichlet.Critical.Parameter.pellParameter_mul_denominator]
    _ = ((Pell.FiniteBranch.pellDenominator (stage + 1) : Nat) :
          Fraction.Rational) := by
      rw [← castIdentity]
      ring1

/-- Exact Möbius recurrence for the supplied finite Pell parameter. -/
theorem pellParameter_succ_mul_four_sub (stage : Nat) :
    Dirichlet.Critical.Parameter.pellParameter (stage + 1) *
        (4 - Dirichlet.Critical.Parameter.pellParameter stage) = 1 := by
  have denominatorPositive :
      (0 : Fraction.Rational) <
        (Pell.FiniteBranch.pellDenominator stage :
          Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      (Pell.FiniteBranch.pellDenominator_pos stage)
  apply Fraction.Field.mul_right_cancel_of_ne
    denominatorPositive.ne'
  calc
    (Dirichlet.Critical.Parameter.pellParameter (stage + 1) *
          (4 - Dirichlet.Critical.Parameter.pellParameter stage)) *
        (Pell.FiniteBranch.pellDenominator stage :
          Fraction.Rational) =
      Dirichlet.Critical.Parameter.pellParameter (stage + 1) *
        ((4 - Dirichlet.Critical.Parameter.pellParameter stage) *
          (Pell.FiniteBranch.pellDenominator stage :
            Fraction.Rational)) := by ring1
    _ = Dirichlet.Critical.Parameter.pellParameter (stage + 1) *
        (Pell.FiniteBranch.pellDenominator (stage + 1) :
          Fraction.Rational) := by
      rw [Dirichlet.Critical.Transition.four_sub_parameter_mul_denominator]
    _ = (Pell.FiniteBranch.pellNumerator (stage + 1) :
          Fraction.Rational) :=
      Dirichlet.Critical.Parameter.pellParameter_mul_denominator (stage + 1)
    _ = (Pell.FiniteBranch.pellDenominator stage :
          Fraction.Rational) := by
      rw [Dirichlet.Critical.Transition.pellNumerator_succ_eq_denominator]
    _ = 1 * (Pell.FiniteBranch.pellDenominator stage :
          Fraction.Rational) := by ring1

/-- Polynomial form of the inverse parameter transition, used by the error
coordinate of the next pair basis. -/
theorem four_mul_pellParameter_succ_sub_one (stage : Nat) :
    4 * Dirichlet.Critical.Parameter.pellParameter (stage + 1) - 1 =
      Dirichlet.Critical.Parameter.pellParameter (stage + 1) *
        Dirichlet.Critical.Parameter.pellParameter stage := by
  calc
    4 * Dirichlet.Critical.Parameter.pellParameter (stage + 1) - 1 =
        4 * Dirichlet.Critical.Parameter.pellParameter (stage + 1) -
          Dirichlet.Critical.Parameter.pellParameter (stage + 1) *
            (4 - Dirichlet.Critical.Parameter.pellParameter stage) := by
      rw [Dirichlet.Critical.Transition.pellParameter_succ_mul_four_sub]
    _ = Dirichlet.Critical.Parameter.pellParameter (stage + 1) *
        Dirichlet.Critical.Parameter.pellParameter stage := by ring1

/-- The finite Pell parameters increase strictly at each supplied stage. -/
theorem pellParameter_lt_succ (stage : Nat) :
    Dirichlet.Critical.Parameter.pellParameter stage <
      Dirichlet.Critical.Parameter.pellParameter (stage + 1) := by
  let current := Dirichlet.Critical.Parameter.pellParameter stage
  let next := Dirichlet.Critical.Parameter.pellParameter (stage + 1)
  have factorPositive : (0 : Fraction.Rational) <
      4 - current := by
    apply Fraction.Order.Arithmetic.sub_pos_direct
    exact (Dirichlet.Critical.Parameter.pellParameter_lt_oneThird stage).trans
      (by decide)
  have productPositive :
      (0 : Fraction.Rational) <
        (4 - current) * (next - current) := by
    calc
      (0 : Fraction.Rational) <
          Dirichlet.Critical.Cylinder.Basic.parameterPolynomial current := by
        exact Dirichlet.Critical.Parameter.parameterPolynomial_pellParameter_pos
          stage
      _ = 1 - current * (4 - current) := by
        unfold Dirichlet.Critical.Cylinder.Basic.parameterPolynomial
        ring1
      _ = next * (4 - current) - current * (4 - current) := by
        dsimp only [current, next]
        rw [Dirichlet.Critical.Transition.pellParameter_succ_mul_four_sub]
      _ = (4 - current) * (next - current) := by ring1
  exact Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    (Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
      productPositive factorPositive.le)

/-- Pointwise monotonicity of finite Pell evaluation, proved by induction on
the supplied natural-stage comparison. -/
theorem pellParameter_le_of_le {first second : Nat}
    (stageOrder : first ≤ second) :
    Dirichlet.Critical.Parameter.pellParameter first ≤
      Dirichlet.Critical.Parameter.pellParameter second := by
  induction stageOrder with
  | refl => exact le_refl _
  | @step second stageOrder inductionHypothesis =>
      exact inductionHypothesis.trans
        (Dirichlet.Critical.Transition.pellParameter_lt_succ second).le

/-- The upper scale of one critical window lies strictly below the lower
scale of the next.  Together with the within-stage ordering, this makes the
finite Pell branch strictly ordered without an appeal to a limit. -/
theorem criticalUpper_lt_nextLower_denominatorQuadrance (stage : Nat) :
    Best.Error.denominatorQuadrance
        (Dirichlet.Critical.Pair.criticalUpperPair stage) <
      Best.Error.denominatorQuadrance
        (Dirichlet.Critical.Pair.criticalLowerPair (stage + 1)) := by
  have numeratorPositive :=
    Pell.FiniteBranch.pellNumerator_pos stage
  have differencePositive :=
    Pell.FiniteBranch.pellDifference_pos stage
  have numeratorLtDouble :
      Pell.FiniteBranch.pellNumerator stage <
        2 * Pell.FiniteBranch.pellNumerator stage := by
    simpa only [-eq_self, -iff_self, one_mul] using
      Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) numeratorPositive
  have differenceLtTriple :
      Pell.FiniteBranch.pellDifference stage <
        3 * Pell.FiniteBranch.pellDifference stage := by
    simpa only [-eq_self, -iff_self, one_mul] using
      Nat.mul_lt_mul_of_pos_right (by decide : 1 < 3) differencePositive
  have denominatorLtDifferenceSucc :
      Pell.FiniteBranch.pellNumerator stage +
          Pell.FiniteBranch.pellDifference stage <
        2 * Pell.FiniteBranch.pellNumerator stage +
          3 * Pell.FiniteBranch.pellDifference stage :=
    Nat.add_lt_add numeratorLtDouble differenceLtTriple
  have doubledDenominatorLtNext :
      2 * Pell.FiniteBranch.pellDenominator stage <
        Pell.FiniteBranch.pellDenominator (stage + 1) := by
    unfold Pell.FiniteBranch.pellDenominator
    rw [Pell.FiniteBranch.pellNumerator_succ,
      Pell.FiniteBranch.pellDifference_succ]
    calc
      2 * (Pell.FiniteBranch.pellNumerator stage +
          Pell.FiniteBranch.pellDifference stage) =
          (Pell.FiniteBranch.pellNumerator stage +
              Pell.FiniteBranch.pellDifference stage) +
            (Pell.FiniteBranch.pellNumerator stage +
              Pell.FiniteBranch.pellDifference stage) := by ring1
      _ < (Pell.FiniteBranch.pellNumerator stage +
              Pell.FiniteBranch.pellDifference stage) +
            (2 * Pell.FiniteBranch.pellNumerator stage +
              3 * Pell.FiniteBranch.pellDifference stage) :=
        Nat.add_lt_add_left denominatorLtDifferenceSucc _
  have squareStrict :
      (2 * Pell.FiniteBranch.pellDenominator stage) ^ 2 <
        Pell.FiniteBranch.pellDenominator (stage + 1) ^ 2 := by
    simpa only [-eq_self, -iff_self, pow_two] using
      Pell.FiniteBranch.natMulSelf_lt_natMulSelf
        doubledDenominatorLtNext
  rw [Dirichlet.Critical.Pair.criticalUpper_denominatorQuadrance,
    Dirichlet.Critical.Pair.criticalLower_denominatorQuadrance]
  calc
    4 * Pell.FiniteBranch.pellDenominator stage ^ 2 =
        (2 * Pell.FiniteBranch.pellDenominator stage) ^ 2 := by
      ring1
    _ < Pell.FiniteBranch.pellDenominator (stage + 1) ^ 2 :=
      squareStrict
    _ ≤ Pell.FiniteBranch.pellNumerator (stage + 1) ^ 2 +
          Pell.FiniteBranch.pellDenominator (stage + 1) ^ 2 :=
      Nat.le_add_left _ _

/-- Upper critical-window scales increase at every finite branch step. -/
theorem criticalUpper_denominatorQuadrance_lt_succ (stage : Nat) :
    Best.Error.denominatorQuadrance
        (Dirichlet.Critical.Pair.criticalUpperPair stage) <
      Best.Error.denominatorQuadrance
        (Dirichlet.Critical.Pair.criticalUpperPair (stage + 1)) :=
  (Dirichlet.Critical.Transition.criticalUpper_lt_nextLower_denominatorQuadrance stage).trans
    (Dirichlet.Critical.Pair.critical_denominatorQuadrance_ordered
      (stage + 1))

/-- Monotonicity of upper critical-window scale between two supplied finite
stages. -/
theorem criticalUpper_denominatorQuadrance_le_of_le
    {first second : Nat} (stageOrder : first ≤ second) :
    Best.Error.denominatorQuadrance
        (Dirichlet.Critical.Pair.criticalUpperPair first) ≤
      Best.Error.denominatorQuadrance
        (Dirichlet.Critical.Pair.criticalUpperPair second) := by
  induction stageOrder with
  | refl => exact le_refl _
  | @step second stageOrder inductionHypothesis =>
      exact inductionHypothesis.trans
        (Dirichlet.Critical.Transition.criticalUpper_denominatorQuadrance_lt_succ second).le

/-- Any later critical upper denominator quadrance strictly exceeds nine times the earlier one. -/
theorem nine_mul_upperQuadrance_lt_of_lt {first second : Nat} (stageOrder : first < second) :
    9 * Best.Error.denominatorQuadrance (Dirichlet.Critical.Pair.criticalUpperPair first) <
      Best.Error.denominatorQuadrance (Dirichlet.Critical.Pair.criticalUpperPair second) :=
  (Dirichlet.Critical.Pair.nine_mul_upperQuadrance_lt_succ first).trans_le
    (criticalUpper_denominatorQuadrance_le_of_le stageOrder)

/-- Strict upper-scale growth between strictly ordered finite stages. -/
theorem criticalUpper_denominatorQuadrance_lt_of_lt
    {first second : Nat} (stageOrder : first < second) :
    Best.Error.denominatorQuadrance
        (Dirichlet.Critical.Pair.criticalUpperPair first) <
      Best.Error.denominatorQuadrance
        (Dirichlet.Critical.Pair.criticalUpperPair second) :=
  (Dirichlet.Critical.Transition.criticalUpper_denominatorQuadrance_lt_succ first).trans_le
    (Dirichlet.Critical.Transition.criticalUpper_denominatorQuadrance_le_of_le stageOrder)

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Transition
