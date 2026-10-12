module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Rational.Contraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Clearance.Pair.Bezout
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Subdivision
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius
import Purelib.Data.Rat.Interval.Width
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Resolution

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

/-- Construct interval clearance for the gcd-reduced polynomial pair.

The reduced pair's explicit Bézout certificate supplies a quantitative bound on the original requested root interval. -/
@[expose] public def reducedClearance
    (numerator denominator : CoordinatePolynomial) (root : Interval.Proper.Cell) :
    Clearance.Pair.Basic.Certificate
      (Pair.Reduction.reducedDenominator numerator denominator)
      (Pair.Reduction.reducedNumerator numerator denominator) root.interval :=
  Clearance.Pair.Bezout.certificateOfCoprime
    (Pair.Reduction.reducedPairCoprime numerator denominator) root.interval

/-- Compute the signed-chain resolution threshold for the gcd-reduced pair.

The bound uses the interval clearance of the same reduced denominator and numerator. -/
@[expose] public def resolutionRadiusSq
    (numerator denominator : CoordinatePolynomial) (root : Interval.Proper.Cell) :
      Fraction.Rational :=
  SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq
    (Pair.Reduction.reducedDenominator numerator denominator)
    (Pair.Reduction.reducedNumerator numerator denominator)
    (reducedClearance numerator denominator root)

/-- The gcd-reduced signed-chain resolution threshold is strictly positive.

The reduced denominator and numerator have the retained explicit
interval clearance. Positivity of their same finite signed-chain radius
gives positivity of the displayed coefficient-computed threshold. -/
public theorem resolutionRadiusSq_pos
    (numerator denominator : CoordinatePolynomial) (root : Interval.Proper.Cell) :
    0 < resolutionRadiusSq numerator denominator root :=
  SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_pos
    (Pair.Reduction.reducedDenominator numerator denominator)
    (Pair.Reduction.reducedNumerator numerator denominator)
    (reducedClearance numerator denominator root)

/-- Width threshold that turns an unsquared interval estimate into the
squared-radius estimate consumed by the finite event scanner.

The original coefficient-count squared radius is retained together with
the constant one. Their minimum permits the same interval width to
control its squared lower-endpoint displacement. -/
@[expose] public def eventLeafWidth
    (numerator denominator : CoordinatePolynomial) (root : Interval.Proper.Cell) :
      Fraction.Rational :=
  min 1 (resolutionRadiusSq numerator denominator root)

/-- The event-resolution leaf width is strictly positive.

Both the constant one and original signed-chain squared radius are
strictly positive. Their retained rational minimum is therefore positive. -/
public theorem eventLeafWidth_pos
    (numerator denominator : CoordinatePolynomial) (root : Interval.Proper.Cell) :
    0 < eventLeafWidth numerator denominator root :=
  Fraction.Order.Basic.lt_min (by decide) (resolutionRadiusSq_pos numerator denominator root)

/-- Compute enough central-third subdivision rounds to fall below half the event leaf width.

The natural depth is obtained from the original interval width and the coefficient-derived positive threshold. -/
@[expose] public def eventDepth
    (numerator denominator : CoordinatePolynomial) (root : Interval.Proper.Cell) : Nat :=
  Approximation.Rational.Contraction.geometricDepth (Bounds.width root.interval)
    (eventLeafWidth numerator denominator root / 2)

/-- Build the finite safe subdivision at the computed event-resolution depth.

The supplied nonzero denominator supports each safe cut; the root cell and all resulting cut certificates are retained.
-/
@[expose] public def eventSubdivision
    (numerator denominator : CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root : Interval.Proper.Cell) : Subdivision numerator denominator :=
  Subdivision.build numerator denominator denominatorNonzero
    (eventDepth numerator denominator root) root

/-- Every cell in the computed event subdivision refines the original root interval.

The subdivision is the original safe-cut builder at the retained
coefficient-computed event depth. Its exact leaf occurrence gives the
same recursively certified interval refinement. -/
public theorem eventSubdivision_leaf_refines
    (numerator denominator : CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root leaf : Interval.Proper.Cell)
    (member : leaf ∈
      (eventSubdivision numerator denominator denominatorNonzero root).leaves) :
    leaf.interval.Refines root.interval := by
  exact Subdivision.build_leaf_refines numerator denominator
    denominatorNonzero (eventDepth numerator denominator root) root member

/-- Every computed event leaf is strictly narrower than the coefficient-derived event-resolution threshold.

The retained geometric depth bounds the original safe-cut leaf width
by half the same positive event threshold. That half is strictly smaller
than the threshold, giving the displayed leaf comparison. -/
public theorem eventSubdivision_leaf_width_lt
    (numerator denominator : CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root leaf : Interval.Proper.Cell)
    (member : leaf ∈
      (eventSubdivision numerator denominator denominatorNonzero root).leaves) :
    (Bounds.width leaf.interval) < eventLeafWidth numerator denominator root := open
      Purelib.Algebra.Field in by
  let leafWidth := eventLeafWidth numerator denominator root
  have leafWidthPositive : 0 < leafWidth := by
    simpa only [leafWidth] using
      eventLeafWidth_pos numerator denominator root
  have geometric :=
    Approximation.Rational.Contraction.geometricDepth_sufficient
      (width := (Bounds.width root.interval)) (epsilon := leafWidth / 2)
      (Bounds.width_nonneg root.interval)
      (Fraction.Order.Field.div_pos_direct leafWidthPositive
        (show (0 : Fraction.Rational) < 2 by decide))
  have geometric' :
      (2 / 3 : Fraction.Rational) ^ eventDepth numerator denominator root *
          (Bounds.width root.interval) ≤ leafWidth / 2 := by
    simpa only [eventDepth] using geometric
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Fraction.Rational) < 1 by decide) leafWidthPositive
    rw [ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Fraction.Rational)⁻¹ = 1 / 2 := by
      rw [ExplicitField.div_eq_mul_inv]
      exact (_root_.one_mul _).symm
    rw [halfInverse]
    simpa only [Fraction.Field.mul_comm, one_mul] using scaled
  exact (Subdivision.build_leaf_width_le numerator denominator
    denominatorNonzero (eventDepth numerator denominator root) root member).trans_lt
      (geometric'.trans_lt halfBelow)

end Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Resolution
