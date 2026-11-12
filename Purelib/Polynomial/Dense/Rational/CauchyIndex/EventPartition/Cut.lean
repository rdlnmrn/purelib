module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.SafeCut
import Purelib.Data.Rat.Interval.Width
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Cut

set_option genInjectivity false in
/-- Proof-bearing safe split of one parameter cell. -/
structure SafeSplit (numerator denominator :
  CoordinatePolynomial) (cell : Interval.Proper.Cell) where
  /-- The retained rational cut coordinate. -/ cut : Fraction.Rational
  /-- The cut is strictly above the original lower endpoint. -/ lowerLt : cell.interval.lower < cut
  /-- The cut is strictly below the original upper endpoint. -/ upperLt : cut < cell.interval.upper
  /-- The reduced signed-chain product guard is nonzero at the retained cut. -/ guardNonzero :
    (SignedRemainder.SafeCut.chainGuard numerator denominator).eval cut ≠ 0
  /-- The left child width is strictly less than two thirds of the original width. -/ leftContracts :
    cut - cell.interval.lower < (2 / 3 : Fraction.Rational) * (Interval.Bounds.width cell.interval)
  /-- The right child width is strictly less than two thirds of the original width. -/ rightContracts :
    cell.interval.upper - cut < (2 / 3 : Fraction.Rational) * (Interval.Bounds.width cell.interval)

constructive_injectivity SafeSplit

namespace SafeSplit

/-- The proper left child interval ending at the retained safe cut. -/
def leftCell {numerator denominator :
  CoordinatePolynomial} {cell : Interval.Proper.Cell}
    (split : SafeSplit numerator denominator cell) :
      Interval.Proper.Cell :=
  cell.left split.cut split.lowerLt

/-- The proper right child interval beginning at the retained safe cut. -/
def rightCell {numerator denominator :
  CoordinatePolynomial} {cell : Interval.Proper.Cell}
    (split : SafeSplit numerator denominator cell) :
      Interval.Proper.Cell :=
  cell.right split.cut split.upperLt

end SafeSplit

/-- Compute a certified central-third split avoiding every reduced signed-chain event.

A nonzero denominator supplies a nonzero guard; the result retains the exact cut, strict containment and both fixed
contraction bounds. -/
def safeSplit
    (numerator denominator : CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (cell : Interval.Proper.Cell) : SafeSplit numerator
      denominator cell := by
  let cut := SignedRemainder.SafeCut.safeCut numerator denominator
    denominatorNonzero cell.interval cell.proper
  have specification :=
    SignedRemainder.SafeCut.safeCut_spec numerator denominator
      denominatorNonzero cell.interval cell.proper
  have contraction :=
    SignedRemainder.SafeCut.safeCut_contraction numerator denominator
      denominatorNonzero cell.interval cell.proper
  exact
    { cut := cut
      lowerLt := specification.2.1
      upperLt := specification.2.2
      guardNonzero := specification.1
      leftContracts := contraction.1
      rightContracts := contraction.2 }
end Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Cut

end
