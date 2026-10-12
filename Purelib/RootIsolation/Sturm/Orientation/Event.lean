module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.Jump
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.Neutral
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
public import Purelib.RootIsolation.Sturm.Count.Basic
import Purelib.RootIsolation.Sturm.Count.Squarefree
public import Purelib.RootIsolation.Sturm.Orientation.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

namespace Purelib.RootIsolation.Sturm.Orientation.Event

/-- A displayed rational root in a squarefree, Taylor-resolved cell forces a
nonzero doubled Sturm event.  Endpoint roots contribute one and interior
roots contribute two; the proof does not appeal to a global root-counting
theorem. -/
theorem sturmRootCount2_ne_zero_of_root
    (p : Dense.Rational.Basic.CoordinatePolynomial)
    (squarefree : Dense.Rational.Bezout.Basic.CoprimeCertificate p
      (Dense.Derivative.derivative p))
    {root interval : Data.Rat.Interval.Bounds}
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      Sturm.Orientation.Basic.rootOrientationWidth p squarefree root)
    (resolution : Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
      (Dense.Rational.Pair.Reduction.reducedNumerator
        (Dense.Derivative.derivative p) p)
      (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative p) p)
      interval)
    (parameter : Fraction.Rational) (parameterInside : interval.Contains parameter)
    (rootZero : p.eval parameter = 0) :
    Sturm.Count.Basic.sturmRootCount2 p
      interval.lower interval.upper ≠ 0 := by
  let numerator := Dense.Rational.Pair.Reduction.reducedNumerator
    (Dense.Derivative.derivative p) p
  let denominator := Dense.Rational.Pair.Reduction.reducedDenominator
    (Dense.Derivative.derivative p) p
  have denominatorRoot : denominator.eval parameter = 0 := by
    by_cases denominatorZero : denominator.eval parameter = 0
    · exact denominatorZero
    · have originalNonzero :=
        Sturm.Count.Squarefree.denominator_eval_ne_zero_of_reduced_of_coprime
            squarefree (by
              simpa only [denominator] using denominatorZero)
      exact (originalNonzero rootZero).elim
  cases resolution with
  | neutral denominatorStable _chain =>
      have impossible := denominatorStable.eval_ne_zero parameterInside
      exact (impossible (by simpa only [denominator] using denominatorRoot)).elim
  | numerator numeratorStable tail =>
      intro countZero
      have orientation := Sturm.Orientation.Basic.rootEndpointOrientation p squarefree refines proper
        widthSmall parameter parameterInside rootZero
      have countFormula :
          Sturm.Count.Basic.sturmRootCount2 p
              interval.lower interval.upper =
            (Data.Rat.Sign.Jump.signJump
                (denominator.eval interval.lower)
                (numerator.eval interval.lower) : Int) -
              Data.Rat.Sign.Jump.signJump
                (denominator.eval interval.upper)
                (numerator.eval interval.upper) := by
        unfold Sturm.Count.Basic.sturmRootCount2
          Dense.Rational.CauchyIndex.Reduced.reducedCauchyIndex2
        exact Dense.Rational.CauchyIndex.Events.Signs.Neutral.cauchyIndex2_eq_firstJumps_of_neutralTail
            numeratorStable.polynomial_nonzero tail
      rcases orientation.lower with lowerRoot | lowerNegative
      · rcases orientation.upper with upperRoot | upperPositive
        · rw [lowerRoot, upperRoot] at proper
          exact (lt_irrefl parameter proper).elim
        · have lowerDenominator : denominator.eval interval.lower = 0 := by
            rw [lowerRoot]
            exact denominatorRoot
          have lowerNumerator : numerator.eval interval.lower ≠ 0 :=
            numeratorStable.eval_ne_zero ⟨le_rfl, interval.valid⟩
          have lowerJump : Data.Rat.Sign.Jump.signJump
              (denominator.eval interval.lower)
              (numerator.eval interval.lower) = 1 := by
            rw [lowerDenominator]
            exact Data.Rat.Sign.Jump.signJump_zero_of_ne lowerNumerator
          have reducedPositive :=
            Dense.Rational.Pair.Reduction.reduced_product_pos_of_original
              squarefree (by
                  simpa only [Fraction.Field.mul_comm]
                    using upperPositive)
          have upperJump : Data.Rat.Sign.Jump.signJump
              (denominator.eval interval.upper)
              (numerator.eval interval.upper) = 0 :=
            Data.Rat.Sign.Jump.signJump_eq_zero_of_mul_pos (by
              simpa only [numerator, denominator,
                Fraction.Field.mul_comm] using reducedPositive)
          rw [lowerJump, upperJump] at countFormula
          rw [countZero] at countFormula
          exact (by decide : (0 : Int) ≠ 1 - 0) countFormula
      · rcases orientation.upper with upperRoot | upperPositive
        · have upperDenominator : denominator.eval interval.upper = 0 := by
            rw [upperRoot]
            exact denominatorRoot
          have upperNumerator : numerator.eval interval.upper ≠ 0 :=
            numeratorStable.eval_ne_zero ⟨interval.valid, le_rfl⟩
          have reducedNegative :=
            Dense.Rational.Pair.Reduction.reduced_product_neg_of_original
              squarefree (by
                  simpa only [Fraction.Field.mul_comm]
                    using lowerNegative)
          have lowerJump : Data.Rat.Sign.Jump.signJump
              (denominator.eval interval.lower)
              (numerator.eval interval.lower) = 2 :=
            Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg (by
              simpa only [numerator, denominator,
                Fraction.Field.mul_comm] using reducedNegative)
          have upperJump : Data.Rat.Sign.Jump.signJump
              (denominator.eval interval.upper)
              (numerator.eval interval.upper) = 1 := by
            rw [upperDenominator]
            exact Data.Rat.Sign.Jump.signJump_zero_of_ne upperNumerator
          rw [lowerJump, upperJump] at countFormula
          rw [countZero] at countFormula
          exact (by decide : (0 : Int) ≠ 2 - 1) countFormula
        · have reducedNegative :=
            Dense.Rational.Pair.Reduction.reduced_product_neg_of_original
              squarefree (by
                  simpa only [Fraction.Field.mul_comm]
                    using lowerNegative)
          have reducedPositive :=
            Dense.Rational.Pair.Reduction.reduced_product_pos_of_original
              squarefree (by
                  simpa only [Fraction.Field.mul_comm]
                    using upperPositive)
          have lowerJump : Data.Rat.Sign.Jump.signJump
              (denominator.eval interval.lower)
              (numerator.eval interval.lower) = 2 :=
            Data.Rat.Sign.Jump.signJump_eq_two_of_mul_neg (by
              simpa only [numerator, denominator,
                Fraction.Field.mul_comm] using reducedNegative)
          have upperJump : Data.Rat.Sign.Jump.signJump
              (denominator.eval interval.upper)
              (numerator.eval interval.upper) = 0 :=
            Data.Rat.Sign.Jump.signJump_eq_zero_of_mul_pos (by
              simpa only [numerator, denominator,
                Fraction.Field.mul_comm] using reducedPositive)
          rw [lowerJump, upperJump] at countFormula
          rw [countZero] at countFormula
          exact (by decide : (0 : Int) ≠ 2 - 0) countFormula

end Purelib.RootIsolation.Sturm.Orientation.Event

end
