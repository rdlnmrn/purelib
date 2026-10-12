module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Contraction
public import Purelib.Approximation.Rational.Grid.CentralThird
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Rat.Sign.CauchyIndex.HalfPlane
import Purelib.Data.Rat.Sign.Jump
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Sign.CauchyIndex.HalfPlane
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Pair.Operations
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Pair.Basic (Certificate)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

public section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane

/-- The Cauchy index is the difference of the retained endpoint jumps.

The displayed rational coordinate polynomials and endpoints determine the exact
index and both signed products. This proposition retains those same inputs. -/
@[expose] def Formula (R S : CoordinatePolynomial) (a b : Fraction.Rational) : Prop :=
  Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S a b =
    (Data.Rat.Sign.Jump.signJump 1 (R.eval a * S.eval a) : Int) -
      Data.Rat.Sign.Jump.signJump 1 (R.eval b * S.eval b)

/-- Compose endpoint-jump formulas meeting at the same retained endpoint.

The common jump cancels using scalar index additivity. Both coordinate
polynomials and the three supplied rational endpoints remain fixed. -/
theorem Formula.add {R S : CoordinatePolynomial} {a b c : Fraction.Rational}
    (left : Formula R S a b) (right : Formula R S b c) :
    Formula R S a c := by
  unfold Formula at left right ⊢
  rw [Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add R S a b c, left, right]
  ring1

/-- Reverse the two endpoints of an endpoint-jump formula.

Scalar reversal of the same Cauchy index exchanges the two retained endpoint
jumps without changing the coordinate polynomials. -/
theorem Formula.reverse {R S : CoordinatePolynomial} {a b : Fraction.Rational}
    (formula : Formula R S a b) : Formula R S b a := by
  unfold Formula at formula ⊢
  rw [Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse, formula]
  ring1

/-- A resolved event with positive real coordinate has the endpoint-jump formula.

Positivity holds throughout the retained interval. The same resolved event is
recentered with its positive real sign and original denominator sign. -/
theorem formula_of_event
    {R S : CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (event : Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns R S interval)
    (realPositive : ∀ x : Fraction.Rational, interval.Contains x → 0 < R.eval x) :
    Formula R S interval.lower interval.upper := by
  have lowerPositive := realPositive interval.lower
    ⟨le_rfl, interval.valid⟩
  have upperPositive := realPositive interval.upper
    ⟨interval.valid, le_rfl⟩
  let centered := event.recenter .positive event.denominator
    (Or.inl (by decide))
    (Or.inr (Data.Sign.ofCoordinate_of_pos lowerPositive).symm)
    event.denominatorLowerStable
    (Or.inr (Data.Sign.ofCoordinate_of_pos upperPositive).symm)
    event.denominatorUpperStable
  have index := centered.index
  unfold Formula
  rw [index]
  dsimp only [centered, Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns.recenter]
  rw [Data.Sign.ofCoordinate_of_pos lowerPositive,
    Data.Sign.ofCoordinate_of_pos upperPositive]
  rw [Data.Sign.CauchyIndex.HalfPlane.sign_eventIndex2_positive _ _ _
      event.denominatorLowerStable event.denominatorUpperStable,
    Purelib.Data.Rat.Sign.CauchyIndex.HalfPlane.jump_positive_eq_signJump_mul lowerPositive,
    Purelib.Data.Rat.Sign.CauchyIndex.HalfPlane.jump_positive_eq_signJump_mul upperPositive]

/-- A sufficiently narrow retained subinterval has the right-half-plane formula.

The subinterval refines the original clearance interval, has positive width and
stays below the retained resolution threshold. Its real coordinate is positive. -/
theorem formula_of_refined_width
    {R S : CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (clearance : Certificate R S root)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      min 1 (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap))
    (realPositive : ∀ x : Fraction.Rational, root.Contains x → 0 < R.eval x) :
    Formula R S interval.lower interval.upper := by
  have radius : Data.Rat.Interval.Radius.sampleRadiusSq interval interval.lower <
      Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap :=
    Data.Rat.Interval.Radius.Partition.radius_lt_of_width_lt
      proper widthSmall
  let event := Dense.Rational.CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq clearance.swap refines
    radius
  apply formula_of_event event
  intro x inside
  exact realPositive x
    ⟨refines.1.trans inside.1, inside.2.trans refines.2⟩

/-- Sufficient fixed-depth central-third subdivision proves the half-plane formula.

The retained clearance and positive real coordinate apply on the original root
interval. A displayed depth bound makes every recursively retained leaf narrow
enough for its finite event certificate, and their endpoint jumps telescope. -/
theorem formulaAtDepth
    {R S : CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (clearance : Certificate R S root)
    (realPositive : ∀ x : Fraction.Rational, root.Contains x → 0 < R.eval x)
    (fuel : Nat) (interval : Data.Rat.Interval.Bounds)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (sufficient : (2 / 3 : Fraction.Rational) ^ fuel *
      (interval.upper - interval.lower) <
        min 1 (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap)) :
    Formula R S interval.lower interval.upper := open Purelib.Algebra.Field in by
  induction fuel generalizing interval with
  | zero =>
      apply formula_of_refined_width clearance refines proper
      · simpa only [pow_zero, one_mul] using sufficient
      · exact realPositive
  | succ fuel inductionHypothesis =>
      let cut := Approximation.Rational.Grid.CentralThird.centralLower interval.lower interval.upper
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
            rw [show interval.lower + (interval.upper - interval.lower) / 3 -
                interval.lower = (interval.upper - interval.lower) / 3 by ring1]
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
        rw [Approximation.Rational.Grid.CentralThird.sub_add_eq_twice_of_three_mul interval.lower interval.upper
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

/-- A positive real coordinate and retained clearance give the half-plane formula.

The original proper rational interval has a positive real coordinate everywhere.
Its exact resolution radius supplies a finite sufficient subdivision depth. -/
theorem formula_of_positive_real
    {R S : CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (clearance : Certificate R S root)
    (proper : root.lower < root.upper)
    (realPositive : ∀ x : Fraction.Rational, root.Contains x → 0 < R.eval x) :
    Formula R S root.lower root.upper := open Purelib.Algebra.Field in by
  let leafWidth := min 1 (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance.swap)
  have leafWidthPositive : 0 < leafWidth :=
    Fraction.Order.Basic.lt_min (by decide)
      (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_pos S R clearance.swap)
  let depth := Approximation.Rational.Contraction.geometricDepth (root.upper - root.lower) (leafWidth / 2)
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
      exact (_root_.one_mul _).symm
    rw [halfInverse]
    simpa only [Fraction.Field.mul_comm, one_mul] using scaled
  apply formulaAtDepth clearance realPositive depth root
    ⟨le_rfl, le_rfl⟩ proper
  simpa only [leafWidth] using geometric.trans_lt halfBelow
end Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
