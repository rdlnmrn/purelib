module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Contraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Bounds
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Resolution
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Resolution
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
import Purelib.Polynomial.Clearance.Pair.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Pair.Basic (Certificate)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Partition

section
/-- The constant-one polynomial used by the finite central-third cut selector. -/
private def unitGuard :
  CoordinatePolynomial := Dense.Basic.DensePolynomial.constant 1
/-- The constant-one guard is nonzero. -/
private theorem
  unitGuard_nonzero :
  Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Partition.unitGuard.isZero = false := by decide
end

/-- Fixed-depth central-third subdivision for every degenerate coordinate
branch.  Since pair-level event data permits axis endpoints, the cuts need
not avoid any individual coordinate roots. -/
theorem auxiliaryProductFormulaAtDepth
    {A B C D E H : CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Certificate A B root) (right : Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (degenerate : B.isZero = true ∨ D.isZero = true ∨
      A.isZero = true ∨ C.isZero = true ∨
      H.isZero = true ∨ E.isZero = true)
    (fuel : Nat) (interval : Data.Rat.Interval.Bounds)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (sufficient : (2 / 3 : Fraction.Rational) ^ fuel *
      (interval.upper - interval.lower) <
        Dense.Rational.CauchyIndex.Product.Degenerate.Bounds.degenerateProductLeafWidth left right
          realIdentity imagIdentity) :
    Dense.Rational.CauchyIndex.Product.Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  induction fuel generalizing interval with
  | zero =>
      have widthSmall : interval.upper - interval.lower <
          Dense.Rational.CauchyIndex.Product.Degenerate.Bounds.degenerateProductLeafWidth left right
            realIdentity imagIdentity := by
        simpa only [pow_zero, one_mul] using sufficient
      have radius : Data.Rat.Interval.Radius.sampleRadiusSq interval interval.lower <
          Dense.Rational.CauchyIndex.Product.Resolution.localProductResolutionRadiusSq left right
            realIdentity imagIdentity := by
        apply Data.Rat.Interval.Radius.Partition.radius_lt_of_width_lt proper
        simpa only [Dense.Rational.CauchyIndex.Product.Degenerate.Bounds.degenerateProductLeafWidth] using widthSmall
      exact
        Dense.Rational.CauchyIndex.Product.Degenerate.Resolution.auxiliaryProductFormula_of_degenerate_refined_radiusSq
        left right realIdentity imagIdentity refines radius degenerate
  | succ fuel inductionHypothesis =>
      let cut := Dense.Rational.Nonzero.Search.Central.centralSearchValue
        unitGuard
        Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Partition.unitGuard.natDegree proper
        unitGuard_nonzero le_rfl
      have cutSpec : interval.lower < cut ∧ cut < interval.upper := by
        have specification := Dense.Rational.Nonzero.Search.Central.centralSearchValue_spec
          unitGuard
          Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Partition.unitGuard.natDegree proper
            unitGuard_nonzero le_rfl
        exact specification.2
      have contraction : cut - interval.lower <
            (2 / 3 : Fraction.Rational) *
              (interval.upper - interval.lower) ∧
          interval.upper - cut <
            (2 / 3 : Fraction.Rational) *
              (interval.upper - interval.lower) := by
        simpa only [cut] using Dense.Rational.Nonzero.Search.Central.centralSearchValue_contraction
          unitGuard
          Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Partition.unitGuard.natDegree proper
            unitGuard_nonzero le_rfl
      let leftInterval : Data.Rat.Interval.Bounds :=
        { lower := interval.lower
          upper := cut
          valid := cutSpec.1.le }
      let rightInterval : Data.Rat.Interval.Bounds :=
        { lower := cut
          upper := interval.upper
          valid := cutSpec.2.le }
      have leftRefines : leftInterval.Refines root :=
        ⟨refines.1, cutSpec.2.le.trans refines.2⟩
      have rightRefines : rightInterval.Refines root :=
        ⟨refines.1.trans cutSpec.1.le, refines.2⟩
      have powerPositive : 0 < (2 / 3 : Fraction.Rational) ^ fuel :=
        Fraction.Order.Arithmetic.pow_pos_direct (by decide) fuel
      have leftSufficient : (2 / 3 : Fraction.Rational) ^ fuel *
          (leftInterval.upper - leftInterval.lower) <
            Dense.Rational.CauchyIndex.Product.Degenerate.Bounds.degenerateProductLeafWidth left right
              realIdentity imagIdentity := by
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
          _ < Dense.Rational.CauchyIndex.Product.Degenerate.Bounds.degenerateProductLeafWidth left right
              realIdentity imagIdentity := sufficient
      have rightSufficient : (2 / 3 : Fraction.Rational) ^ fuel *
          (rightInterval.upper - rightInterval.lower) <
            Dense.Rational.CauchyIndex.Product.Degenerate.Bounds.degenerateProductLeafWidth left right
              realIdentity imagIdentity := by
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
          _ < Dense.Rational.CauchyIndex.Product.Degenerate.Bounds.degenerateProductLeafWidth left right
              realIdentity imagIdentity := sufficient
      have leftFormula := inductionHypothesis leftInterval leftRefines
        (by simpa only [leftInterval] using cutSpec.1) leftSufficient
      have rightFormula := inductionHypothesis rightInterval rightRefines
        (by simpa only [rightInterval] using cutSpec.2) rightSufficient
      exact leftFormula.add rightFormula

/-- Complete auxiliary product formula for the union of all six decidable
coordinate-degenerate branches. -/
theorem
  auxiliaryProductFormula_of_degenerate_coordinates
    {A B C D E H : CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (proper : root.lower < root.upper)
    (left : Certificate A B root) (right : Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (degenerate : B.isZero = true ∨ D.isZero = true ∨
      A.isZero = true ∨ C.isZero = true ∨
      H.isZero = true ∨ E.isZero = true) :
    Dense.Rational.CauchyIndex.Product.Basic.AuxiliaryProductFormula A B C D E H root.lower root.upper := open
      Purelib.Algebra.Field in by
  let leafWidth := Dense.Rational.CauchyIndex.Product.Degenerate.Bounds.degenerateProductLeafWidth
    left right realIdentity imagIdentity
  have leafWidthPositive : 0 < leafWidth := by
    simpa only [leafWidth] using
      Dense.Rational.CauchyIndex.Product.Degenerate.Bounds.degenerateProductLeafWidth_pos left right realIdentity
        imagIdentity
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
  have sufficient : (2 / 3 : Fraction.Rational) ^ depth *
      (root.upper - root.lower) < leafWidth :=
    geometric.trans_lt halfBelow
  exact auxiliaryProductFormulaAtDepth
    left right realIdentity imagIdentity degenerate depth root
    ⟨le_rfl, le_rfl⟩ proper
    (by simpa only [leafWidth] using sufficient)

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Partition

end
