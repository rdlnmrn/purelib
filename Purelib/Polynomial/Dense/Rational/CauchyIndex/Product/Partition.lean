module
import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Contraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint.Resolution
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Guard
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Partition.Bounds
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Resolution
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Pair.Basic (Certificate)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

/-!
# Finite guarded product partitions

The original finite guard scan selects every retained central-third cut.
Positive local thresholds resolve each leaf and telescope the product formulas.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Partition

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product
open Purelib

/-- A sufficiently narrow guarded subinterval satisfies the auxiliary product formula.

The supplied subinterval refines the original root interval, has positive
width below the common threshold, and cannot meet both outer endpoints.
The retained guard observations select an interior or one-sided endpoint
formula using those same factor clearances and coordinate identities. -/
public theorem auxiliaryProductFormula_of_guarded_leaf
    {A B C D E H : CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (left : Certificate A B root)
    (right : Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      Partition.Bounds.completeProductLeafWidth left right realIdentity imagIdentity)
    (lowerGuard : interval.lower = root.lower ∨
      (Guard.productEventGuard A B C D E H).eval interval.lower ≠ 0)
    (upperGuard : interval.upper = root.upper ∨
      (Guard.productEventGuard A B C D E H).eval interval.upper ≠ 0)
    (separated : ¬(interval.lower = root.lower ∧
      interval.upper = root.upper))
    (leftRootStart : A.eval root.lower ≠ 0 ∨ B.eval root.lower ≠ 0)
    (rightRootStart : C.eval root.lower ≠ 0 ∨ D.eval root.lower ≠ 0)
    (leftRootStop : A.eval root.upper ≠ 0 ∨ B.eval root.upper ≠ 0)
    (rightRootStop : C.eval root.upper ≠ 0 ∨ D.eval root.upper ≠ 0) :
    Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      Partition.Bounds.completeProductResolutionRadiusSq left right
        realIdentity imagIdentity :=
    Interval.Radius.Partition.radius_lt_of_width_lt proper widthSmall
  by_cases lowerAtRoot : interval.lower = root.lower
  · have upperNotRoot : interval.upper ≠ root.upper := by
      intro upperAtRoot
      exact separated ⟨lowerAtRoot, upperAtRoot⟩
    have upperClear := upperGuard.resolve_left upperNotRoot
    rcases Guard.productEventGuard_eval_ne_zero_components
        A B C D E H interval.upper upperClear with
      ⟨_AUpper, BUpper, _CUpper, DUpper, _EUpper, HUpper⟩
    apply Endpoint.Resolution.auxiliaryProductFormula_of_leftEndpoint_refined_radiusSq
      left right realIdentity imagIdentity refines
    · simpa only [lowerAtRoot] using
        radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
    · simpa only [lowerAtRoot] using leftRootStart
    · simpa only [lowerAtRoot] using rightRootStart
    · exact BUpper
    · exact DUpper
    · exact HUpper
  · have lowerClear := lowerGuard.resolve_left lowerAtRoot
    rcases Guard.productEventGuard_eval_ne_zero_components
        A B C D E H interval.lower lowerClear with
      ⟨ALower, BLower, CLower, DLower, ELower, HLower⟩
    by_cases upperAtRoot : interval.upper = root.upper
    · apply Endpoint.Resolution.auxiliaryProductFormula_of_rightEndpoint_refined_radiusSq
        left right realIdentity imagIdentity refines
      · simpa only [upperAtRoot] using
          radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))
      · simpa only [upperAtRoot] using leftRootStop
      · simpa only [upperAtRoot] using rightRootStop
      · exact BLower
      · exact DLower
      · exact HLower
    · have upperClear := upperGuard.resolve_left upperAtRoot
      rcases Guard.productEventGuard_eval_ne_zero_components
          A B C D E H interval.upper upperClear with
        ⟨AUpper, BUpper, CUpper, DUpper, EUpper, HUpper⟩
      apply Resolution.auxiliaryProductFormula_of_refined_radiusSq
        left right realIdentity imagIdentity refines
      · exact radius.trans_le (Fraction.Order.Basic.min_le_left _ _)
      · exact ALower
      · exact BLower
      · exact CLower
      · exact DLower
      · exact ELower
      · exact HLower
      · exact AUpper
      · exact BUpper
      · exact CUpper
      · exact DUpper
      · exact EUpper
      · exact HUpper

/-- The bounded central-third subdivision certifies the auxiliary product formula.

All six coordinate polynomials are nonzero, and the supplied geometric
width bound is small enough at the retained finite depth. Each original
central-third guard scan selects the same cut, refinement witnesses and
endpoint data; the two recursive formulas telescope on that selected cut. -/
public theorem auxiliaryProductFormulaAtDepth
    {A B C D E H : CoordinatePolynomial}
    (A_nonzero : A.isZero = false) (B_nonzero : B.isZero = false)
    (C_nonzero : C.isZero = false) (D_nonzero : D.isZero = false)
    (E_nonzero : E.isZero = false) (H_nonzero : H.isZero = false)
    {root : Data.Rat.Interval.Bounds}
    (left : Certificate A B root)
    (right : Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (leftRootStart : A.eval root.lower ≠ 0 ∨ B.eval root.lower ≠ 0)
    (rightRootStart : C.eval root.lower ≠ 0 ∨ D.eval root.lower ≠ 0)
    (leftRootStop : A.eval root.upper ≠ 0 ∨ B.eval root.upper ≠ 0)
    (rightRootStop : C.eval root.upper ≠ 0 ∨ D.eval root.upper ≠ 0)
    (fuel : Nat) (interval : Data.Rat.Interval.Bounds)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (lowerGuard : interval.lower = root.lower ∨
      (Guard.productEventGuard A B C D E H).eval interval.lower ≠ 0)
    (upperGuard : interval.upper = root.upper ∨
      (Guard.productEventGuard A B C D E H).eval interval.upper ≠ 0)
    (separated : fuel ≠ 0 ∨
      ¬(interval.lower = root.lower ∧ interval.upper = root.upper))
    (sufficient : (2 / 3 : Fraction.Rational) ^ fuel *
      (interval.upper - interval.lower) <
        Partition.Bounds.completeProductLeafWidth left right realIdentity imagIdentity) :
    Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  induction fuel generalizing interval with
  | zero =>
      rcases separated with fuelNonzero | separated
      · exact (fuelNonzero rfl).elim
      · apply auxiliaryProductFormula_of_guarded_leaf
          left right realIdentity imagIdentity refines proper
        · simpa only [pow_zero, one_mul] using sufficient
        · exact lowerGuard
        · exact upperGuard
        · exact separated
        · exact leftRootStart
        · exact rightRootStart
        · exact leftRootStop
        · exact rightRootStop
  | succ fuel inductionHypothesis =>
      let guard := Guard.productEventGuard A B C D E H
      have guardNonzero : guard.isZero = false :=
        Guard.productEventGuard_isZero_false A_nonzero B_nonzero
          C_nonzero D_nonzero E_nonzero H_nonzero
      let cut := Dense.Rational.Nonzero.Search.Central.centralSearchValue guard guard.natDegree proper
        guardNonzero le_rfl
      have cutSpec : guard.eval cut ≠ 0 ∧
          interval.lower < cut ∧ cut < interval.upper := by
        simpa only [guard, cut] using Dense.Rational.Nonzero.Search.Central.centralSearchValue_spec
          guard guard.natDegree proper guardNonzero le_rfl
      have contraction : cut - interval.lower <
            (2 / 3 : Fraction.Rational) *
              (interval.upper - interval.lower) ∧
          interval.upper - cut <
            (2 / 3 : Fraction.Rational) *
              (interval.upper - interval.lower) := by
        simpa only [guard, cut] using Dense.Rational.Nonzero.Search.Central.centralSearchValue_contraction
          guard guard.natDegree proper guardNonzero le_rfl
      let leftInterval : Data.Rat.Interval.Bounds :=
        { lower := interval.lower
          upper := cut
          valid := cutSpec.2.1.le }
      let rightInterval : Data.Rat.Interval.Bounds :=
        { lower := cut
          upper := interval.upper
          valid := cutSpec.2.2.le }
      have leftRefines : leftInterval.Refines root := by
        exact ⟨refines.1, cutSpec.2.2.le.trans refines.2⟩
      have rightRefines : rightInterval.Refines root := by
        exact ⟨refines.1.trans cutSpec.2.1.le, refines.2⟩
      have leftSeparated :
          ¬(leftInterval.lower = root.lower ∧
            leftInterval.upper = root.upper) := by
        intro both
        have cutAtUpper : cut = root.upper := by
          simpa only [leftInterval] using both.2
        have upperBound : interval.upper ≤ cut := by
          rw [cutAtUpper]
          exact refines.2
        exact (not_lt_of_ge upperBound) cutSpec.2.2
      have rightSeparated :
          ¬(rightInterval.lower = root.lower ∧
            rightInterval.upper = root.upper) := by
        intro both
        have cutAtLower : cut = root.lower := by
          simpa only [rightInterval] using both.1
        have lowerBound : cut ≤ interval.lower := by
          rw [cutAtLower]
          exact refines.1
        exact (not_lt_of_ge lowerBound) cutSpec.2.1
      have powerPositive : 0 < (2 / 3 : Fraction.Rational) ^ fuel :=
        Fraction.Order.Arithmetic.pow_pos_direct (by decide) fuel
      have leftSufficient : (2 / 3 : Fraction.Rational) ^ fuel *
          (leftInterval.upper - leftInterval.lower) <
            Partition.Bounds.completeProductLeafWidth left right realIdentity imagIdentity := by
        calc
          (2 / 3 : Fraction.Rational) ^ fuel *
              (leftInterval.upper - leftInterval.lower) <
              (2 / 3 : Fraction.Rational) ^ fuel *
                ((2 / 3 : Fraction.Rational) *
                  (interval.upper - interval.lower)) :=
            Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              powerPositive
              (by simpa only [leftInterval] using contraction.1)
          _ = (2 / 3 : Fraction.Rational) ^ Nat.succ fuel *
              (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < Partition.Bounds.completeProductLeafWidth left right
              realIdentity imagIdentity := sufficient
      have rightSufficient : (2 / 3 : Fraction.Rational) ^ fuel *
          (rightInterval.upper - rightInterval.lower) <
            Partition.Bounds.completeProductLeafWidth left right realIdentity imagIdentity := by
        calc
          (2 / 3 : Fraction.Rational) ^ fuel *
              (rightInterval.upper - rightInterval.lower) <
              (2 / 3 : Fraction.Rational) ^ fuel *
                ((2 / 3 : Fraction.Rational) *
                  (interval.upper - interval.lower)) :=
            Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              powerPositive
              (by simpa only [rightInterval] using contraction.2)
          _ = (2 / 3 : Fraction.Rational) ^ Nat.succ fuel *
              (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < Partition.Bounds.completeProductLeafWidth left right
              realIdentity imagIdentity := sufficient
      have leftFormula := inductionHypothesis leftInterval leftRefines
        (by simpa only [leftInterval] using cutSpec.2.1)
        (by simpa only [leftInterval] using lowerGuard)
        (Or.inr (by simpa only [leftInterval, guard] using cutSpec.1))
        (Or.inr leftSeparated) leftSufficient
      have rightFormula := inductionHypothesis rightInterval rightRefines
        (by simpa only [rightInterval] using cutSpec.2.2)
        (Or.inr (by simpa only [rightInterval, guard] using cutSpec.1))
        (by simpa only [rightInterval] using upperGuard)
        (Or.inr rightSeparated) rightSufficient
      exact leftFormula.add rightFormula

/-- Six nonzero coordinates certify the complete auxiliary product formula.

The six nonzero coordinates and supplied factor clearances retain the
same real and imaginary product identities. Their common positive width
threshold determines the original geometric depth; the finite guard-cut
subdivision then certifies the complete original endpoint formula. -/
public theorem auxiliaryProductFormula_of_nondegenerate_coordinates
    {A B C D E H : CoordinatePolynomial}
    (A_nonzero : A.isZero = false) (B_nonzero : B.isZero = false)
    (C_nonzero : C.isZero = false) (D_nonzero : D.isZero = false)
    (E_nonzero : E.isZero = false) (H_nonzero : H.isZero = false)
    {root : Data.Rat.Interval.Bounds} (proper : root.lower < root.upper)
    (left : Certificate A B root)
    (right : Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (leftRootStart : A.eval root.lower ≠ 0 ∨ B.eval root.lower ≠ 0)
    (rightRootStart : C.eval root.lower ≠ 0 ∨ D.eval root.lower ≠ 0)
    (leftRootStop : A.eval root.upper ≠ 0 ∨ B.eval root.upper ≠ 0)
    (rightRootStop : C.eval root.upper ≠ 0 ∨ D.eval root.upper ≠ 0) :
    Basic.AuxiliaryProductFormula A B C D E H root.lower root.upper := open Purelib.Algebra.Field in by
  let leafWidth := Partition.Bounds.completeProductLeafWidth
    left right realIdentity imagIdentity
  have leafWidthPositive : 0 < leafWidth := by
    simpa only [leafWidth] using
      Partition.Bounds.completeProductLeafWidth_pos left right realIdentity imagIdentity
  let depth := Approximation.Rational.Contraction.geometricDepth (root.upper - root.lower) (leafWidth / 2)
  have geometric : (2 / 3 : Fraction.Rational) ^ depth *
      (root.upper - root.lower) ≤ leafWidth / 2 := by
    simpa only [depth] using
      (Approximation.Rational.Contraction.geometricDepth_sufficient
        (width := root.upper - root.lower) (epsilon := leafWidth / 2)
        (show 0 ≤ root.upper - root.lower from
          (Fraction.Order.Arithmetic.sub_pos_direct proper).le)
        (Fraction.Order.Field.div_pos_direct leafWidthPositive
          (show (0 : Fraction.Rational) < 2 by decide)))
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Fraction.Rational) < 1 by decide) leafWidthPositive
    rw [ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Fraction.Rational)⁻¹ = 1 / 2 := by
      rw [ExplicitField.div_eq_mul_inv]
      exact (_root_.one_mul _).symm
    rw [halfInverse]
    simpa only [Fraction.Field.mul_comm, one_mul] using scaled
  have baseSufficient : (2 / 3 : Fraction.Rational) ^ depth *
      (root.upper - root.lower) < leafWidth :=
    geometric.trans_lt halfBelow
  have widthNonnegative : 0 ≤ root.upper - root.lower :=
    (Fraction.Order.Arithmetic.sub_pos_direct proper).le
  have contractionLeOne : (2 / 3 : Fraction.Rational) ≤ 1 := by decide
  have contractionWidthLe : (2 / 3 : Fraction.Rational) *
      (root.upper - root.lower) ≤ root.upper - root.lower := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      contractionLeOne widthNonnegative
    simpa only [one_mul] using scaled
  have depthPowerNonnegative : 0 ≤ (2 / 3 : Fraction.Rational) ^ depth :=
    Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth
  have sufficient : (2 / 3 : Fraction.Rational) ^ Nat.succ depth *
      (root.upper - root.lower) < leafWidth := by
    calc
      (2 / 3 : Fraction.Rational) ^ Nat.succ depth *
          (root.upper - root.lower) =
          (2 / 3 : Fraction.Rational) ^ depth *
            ((2 / 3 : Fraction.Rational) *
              (root.upper - root.lower)) := by
        rw [pow_succ]
        ring1
      _ ≤ (2 / 3 : Fraction.Rational) ^ depth *
          (root.upper - root.lower) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          contractionWidthLe depthPowerNonnegative
      _ < leafWidth := baseSufficient
  exact auxiliaryProductFormulaAtDepth
    A_nonzero B_nonzero C_nonzero D_nonzero E_nonzero H_nonzero
    left right realIdentity imagIdentity
    leftRootStart rightRootStart leftRootStop rightRootStop
    (Nat.succ depth) root ⟨le_rfl, le_rfl⟩ proper
    (Or.inl rfl) (Or.inl rfl) (Or.inl (fun impossible => Nat.noConfusion impossible))
    (by simpa only [leafWidth] using sufficient)

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Partition
