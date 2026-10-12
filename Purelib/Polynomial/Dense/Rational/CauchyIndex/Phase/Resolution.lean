module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Rational.Contraction
public import Purelib.Approximation.Rational.Grid.CentralThird
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Event
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius
public import Mathlib.Algebra.Field.Defs
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Pair.Operations
import Purelib.Tactic.Ring

/-!
# Resolving phase formulas by finite interval contraction

The retained clearance and signed-chain radius bound the admissible leaf width.
Central-third subdivision follows the supplied finite depth, retaining both
subinterval phase certificates and composing their exact integer turn counts.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Resolution

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

/-- A sufficiently narrow subinterval is resolved by the finite event
scanner and therefore has a modulo-four phase formula.

The supplied refinement and strict width bound control the retained sample radius. The finite event scanner supplies the
phase certificate on the same two interval endpoints. -/
@[expose] public def phaseFormulaOfRefinedWidth
    {R S : Dense.Rational.Basic.CoordinatePolynomial}
    {root interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate R S root)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      min 1 (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap)) :
    Dense.Rational.CauchyIndex.Phase.Basic.PhaseFormula R S interval.lower interval.upper := by
  have radius : Data.Rat.Interval.Radius.sampleRadiusSq interval interval.lower <
      Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap :=
    Data.Rat.Interval.Radius.Partition.radius_lt_of_width_lt proper widthSmall
  exact Dense.Rational.CauchyIndex.Phase.Event.phaseFormulaOfEvent
    (Dense.Rational.CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq clearance.swap refines radius)

/-- Fixed-depth central-third subdivision for the modulo-four phase law.

The supplied depth bounds the geometric contraction of the original width. Each successor retains the original
central-third cut and composes its left and right phase formulas at that common endpoint. -/
@[expose] public def phaseFormulaAtDepth
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate R S root)
    (fuel : Nat) (interval : Data.Rat.Interval.Bounds)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (sufficient : (2 / 3 : Fraction.Rational) ^ fuel *
      (interval.upper - interval.lower) <
        min 1 (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap)) :
    Dense.Rational.CauchyIndex.Phase.Basic.PhaseFormula R S interval.lower interval.upper := open Purelib.Algebra.Field
      in by
  induction fuel generalizing interval with
  | zero =>
      exact Dense.Rational.CauchyIndex.Phase.Resolution.phaseFormulaOfRefinedWidth clearance refines proper
        (by
            simpa only [pow_zero, Fraction.Field.one_mul]
              using sufficient)
  | succ fuel inductionHypothesis =>
      let cut := Approximation.Rational.Grid.CentralThird.centralLower
        interval.lower interval.upper
      have bounds := Approximation.Rational.Grid.CentralThird.centralBounds proper
      have cutLower : interval.lower < cut := by
        simpa only [cut] using bounds.1
      have cutUpper : cut < interval.upper := by
        exact (by simpa only [cut] using bounds.2.1.trans bounds.2.2)
      let leftInterval : Data.Rat.Interval.Bounds :=
        { lower := interval.lower
          upper := cut
          valid := cutLower.le }
      let rightInterval : Data.Rat.Interval.Bounds :=
        { lower := cut
          upper := interval.upper
          valid := cutUpper.le }
      have leftRefines : leftInterval.Refines root :=
        ⟨refines.1, cutUpper.le.trans refines.2⟩
      have rightRefines : rightInterval.Refines root :=
        ⟨refines.1.trans cutLower.le, refines.2⟩
      have widthPositive : 0 < interval.upper - interval.lower :=
        Fraction.Order.Arithmetic.sub_pos_direct proper
      have leftContraction :
          leftInterval.upper - leftInterval.lower ≤
            (2 / 3 : Fraction.Rational) *
              (interval.upper - interval.lower) := by
        dsimp only [leftInterval, cut]
        simp only [Approximation.Rational.Grid.CentralThird.centralLower,
          Fraction.Arithmetic.normalizedAdd_eq,
          Fraction.Arithmetic.normalizedDiv_eq,
          Fraction.Arithmetic.normalizedSub_eq]
        have scaled :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (show (1 / 3 : Fraction.Rational) ≤ 2 / 3 by decide)
            widthPositive.le
        calc
          interval.lower + (interval.upper - interval.lower) / 3 -
                interval.lower =
              (1 / 3 : Fraction.Rational) *
                (interval.upper - interval.lower) := by
            rw [ExplicitField.div_eq_mul_inv,
              ExplicitField.div_eq_mul_inv]
            ring1
          _ ≤ (2 / 3 : Fraction.Rational) *
                (interval.upper - interval.lower) := scaled
      have rightContraction :
          rightInterval.upper - rightInterval.lower =
            (2 / 3 : Fraction.Rational) *
              (interval.upper - interval.lower) := by
        dsimp only [rightInterval, cut]
        simp only [Approximation.Rational.Grid.CentralThird.centralLower,
          Fraction.Arithmetic.normalizedAdd_eq,
          Fraction.Arithmetic.normalizedDiv_eq,
          Fraction.Arithmetic.normalizedSub_eq]
        have scaled : (3 : Fraction.Rational) *
            ((interval.upper - interval.lower) / 3) =
              interval.upper - interval.lower := by
          rw [Fraction.Field.mul_comm]
          exact Fraction.Field.div_mul_cancel_of_ne
            (interval.upper - interval.lower) 3 (by decide)
        rw [Approximation.Rational.Grid.CentralThird.sub_add_eq_twice_of_three_mul
          interval.lower interval.upper
          ((interval.upper - interval.lower) / 3) scaled]
        rw [ExplicitField.div_eq_mul_inv,
          ExplicitField.div_eq_mul_inv]
        ring1
      have powerNonnegative : 0 ≤ (2 / 3 : Fraction.Rational) ^ fuel :=
        Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) fuel
      have leftSufficient : (2 / 3 : Fraction.Rational) ^ fuel *
          (leftInterval.upper - leftInterval.lower) <
            min 1 (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap) := by
        calc
          (2 / 3 : Fraction.Rational) ^ fuel *
              (leftInterval.upper - leftInterval.lower) ≤
              (2 / 3 : Fraction.Rational) ^ fuel *
                ((2 / 3 : Fraction.Rational) *
                  (interval.upper - interval.lower)) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              leftContraction powerNonnegative
          _ = (2 / 3 : Fraction.Rational) ^ Nat.succ fuel *
              (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < min 1 (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap) :=
            sufficient
      have rightSufficient : (2 / 3 : Fraction.Rational) ^ fuel *
          (rightInterval.upper - rightInterval.lower) <
            min 1 (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap) := by
        rw [rightContraction]
        calc
          (2 / 3 : Fraction.Rational) ^ fuel *
              ((2 / 3 : Fraction.Rational) *
                (interval.upper - interval.lower)) =
              (2 / 3 : Fraction.Rational) ^ Nat.succ fuel *
                (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < min 1 (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap) :=
            sufficient
      exact (inductionHypothesis leftInterval leftRefines cutLower
        leftSufficient).add
        (inductionHypothesis rightInterval rightRefines cutUpper
          rightSufficient)

/-- Every proper polynomial path carrying an explicit nonvanishing clearance
certificate has an integer modulo-four phase formula.

The positive signed-chain radius determines a retained target width and geometric depth. Applying the same depth-indexed
subdivision yields a phase certificate for the original proper interval. -/
@[expose] public def phaseFormulaOfClearance
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate R S root)
    (proper : root.lower < root.upper) :
    Dense.Rational.CauchyIndex.Phase.Basic.PhaseFormula R S root.lower root.upper := open Purelib.Algebra.Field in by
  let leafWidth := min 1
    (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap)
  have leafWidthPositive : 0 < leafWidth :=
    Fraction.Order.Basic.lt_min (by decide)
      (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_pos S R clearance.swap)
  let depth := Approximation.Rational.Contraction.geometricDepth
    (root.upper - root.lower) (leafWidth / 2)
  have geometric : (2 / 3 : Fraction.Rational) ^ depth *
      (root.upper - root.lower) ≤ leafWidth / 2 := by
    simpa only [depth] using Approximation.Rational.Contraction.geometricDepth_sufficient
      (width := root.upper - root.lower) (epsilon := leafWidth / 2)
      (Fraction.Order.Arithmetic.sub_pos_direct proper).le
      (Fraction.Order.Field.div_pos_direct leafWidthPositive (by decide))
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Fraction.Rational) < 1 by decide) leafWidthPositive
    rw [ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Fraction.Rational)⁻¹ = 1 / 2 := by
      rw [ExplicitField.div_eq_mul_inv]
      exact (Fraction.Field.one_mul _).symm
    rw [halfInverse]
    simpa only [Fraction.Field.mul_comm,
      Fraction.Field.one_mul] using scaled
  exact Dense.Rational.CauchyIndex.Phase.Resolution.phaseFormulaAtDepth clearance depth root ⟨le_rfl, le_rfl⟩ proper
    (by simpa only [leafWidth] using geometric.trans_lt halfBelow)
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Resolution
