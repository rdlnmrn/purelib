module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Rational.Grid.CentralThird
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Interval

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Bounded nonzero search in the central third

The original finite interval search is applied to the retained middle-third
endpoints. Its same selected value carries nonzero evaluation, strict interior
bounds and the corresponding two-thirds width contraction.
-/

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Approximation.Rational
open Fraction.Order

namespace Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central

/-- Total bounded search for a nonzero polynomial value in the middle third
of a proper interval.

The original interior scan is applied to the displayed middle-third
endpoints with their strict-order certificate. Its same successful
Option projection supplies the retained nonzero rational value. -/
@[expose] public def centralSearchValue (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) : Fraction.Rational :=
  Interval.interiorSearchValue p degreeBound (Grid.CentralThird.centralBounds less).2.1 nonzero degree

/-- The bounded central-third search returns a nonroot strictly inside the original proper interval.

The selected point lies strictly between the original middle-third
endpoints and has nonzero evaluation. Those endpoint comparisons
place that same retained value inside the original proper interval. -/
public theorem centralSearchValue_spec (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    p.eval (centralSearchValue p degreeBound less nonzero degree) ≠ 0 ∧
      a < centralSearchValue p degreeBound less nonzero degree ∧
      centralSearchValue p degreeBound less nonzero degree < b := by
  have selected := Interval.interiorSearchValue_spec p degreeBound
    (Grid.CentralThird.centralBounds less).2.1 nonzero degree
  have selected' :
      p.eval (centralSearchValue p degreeBound less nonzero degree) ≠ 0 ∧
        Grid.CentralThird.centralLower a b <
          centralSearchValue p degreeBound less nonzero degree ∧
        centralSearchValue p degreeBound less nonzero degree <
          Grid.CentralThird.centralUpper a b := by
    simpa only [centralSearchValue] using selected
  exact ⟨selected'.1,
    (Grid.CentralThird.centralBounds less).1.trans selected'.2.1,
    selected'.2.2.trans (Grid.CentralThird.centralBounds less).2.2⟩

/-- A central-third safe cut contracts both child widths by the uniform
factor `2/3`, independently of the polynomial degree.

The retained value lies in the original middle third of the displayed
proper interval. Translating those endpoint inequalities bounds both
child widths by two thirds of the same original width. -/
public theorem centralSearchValue_contraction
    (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    centralSearchValue p degreeBound less nonzero degree - a <
        (2 / 3 : Fraction.Rational) * (b - a) ∧
      b - centralSearchValue p degreeBound less nonzero degree <
        (2 / 3 : Fraction.Rational) * (b - a) := open Purelib.Algebra.Field in by
  have selected := Interval.interiorSearchValue_spec p degreeBound
    (Grid.CentralThird.centralBounds less).2.1 nonzero degree
  have selected' :
      p.eval (centralSearchValue p degreeBound less nonzero degree) ≠ 0 ∧
        Grid.CentralThird.centralLower a b <
          centralSearchValue p degreeBound less nonzero degree ∧
        centralSearchValue p degreeBound less nonzero degree <
          Grid.CentralThird.centralUpper a b := by
    simpa only [centralSearchValue] using selected
  constructor
  · have shifted := Arithmetic.add_lt_add_right_direct
      selected'.2.2 (-a)
    calc
      centralSearchValue p degreeBound less nonzero degree - a <
          Grid.CentralThird.centralUpper a b - a := by simpa only [sub_eq_add_neg] using shifted
      _ = (2 / 3 : Fraction.Rational) * (b - a) := by
        simp only [Grid.CentralThird.centralUpper,
          Fraction.Arithmetic.normalizedAdd_eq,
          Fraction.Arithmetic.normalizedMul_eq,
          Fraction.Arithmetic.normalizedDiv_eq,
          Fraction.Arithmetic.normalizedSub_eq]
        rw [Grid.CentralThird.add_twice_sub_left]
        rw [ExplicitField.div_eq_mul_inv,
          ExplicitField.div_eq_mul_inv]
        ring1
  · have reversed := Arithmetic.neg_lt_neg_direct
      selected'.2.1
    have shifted := Arithmetic.add_lt_add_left_direct
      reversed b
    calc
      b - centralSearchValue p degreeBound less nonzero degree <
          b - Grid.CentralThird.centralLower a b := by simpa only [sub_eq_add_neg] using shifted
      _ = (2 / 3 : Fraction.Rational) * (b - a) := by
        simp only [Grid.CentralThird.centralLower,
          Fraction.Arithmetic.normalizedAdd_eq,
          Fraction.Arithmetic.normalizedDiv_eq,
          Fraction.Arithmetic.normalizedSub_eq]
        have scaled : (3 : Fraction.Rational) * ((b - a) / 3) = b - a := by
          rw [Fraction.Field.mul_comm]
          exact Fraction.Field.div_mul_cancel_of_ne
            (b - a) 3 (by decide)
        rw [Grid.CentralThird.sub_add_eq_twice_of_three_mul a b ((b - a) / 3) scaled]
        rw [ExplicitField.div_eq_mul_inv,
          ExplicitField.div_eq_mul_inv]
        ring1

end Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
