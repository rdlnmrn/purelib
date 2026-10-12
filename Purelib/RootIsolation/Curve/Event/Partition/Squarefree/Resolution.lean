module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Contraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RootIsolation.Curve.Event.Partition.Resolution
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision
import Purelib.RootIsolation.Sturm.Count.Basic
public import Purelib.RootIsolation.Sturm.Orientation.Basic
import Purelib.Data.Rat.Interval.Width
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Data.Rat.Interval.Proper (Cell)
open Purelib.Polynomial.Dense.Basic (RationalPolynomial)
open Purelib.Polynomial.Dense.Rational.Squarefree.BoundaryPartition (SquarefreeCertificate)
open Purelib.RootIsolation.Curve.Event.Partition (Subdivision)

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

public section

/-!
# Common finite event partitions for curve roots and box edges

The root-event polynomial of a boundary chart and the four cleared box-edge
polynomials must be classified on the same parameter cells.  This module
forms one product of their complete reduced-chain guards, uses it for every
central-third cut, and chooses a coefficient-computed depth below all of the
individual event-resolution widths.

Consequently every emitted leaf has, simultaneously:

* a finite Cauchy--Sturm event record for the chart root polynomial; and
* a finite event record for every nontrivial box-edge condition.

Identically-zero box conditions are retained separately by
`CurveBoxConditions.condition_zero_or_active`; they never make
the common cut guard vanish.
-/

namespace Purelib.RootIsolation.Curve.Event.Partition.Squarefree

/-- The ordinary simultaneous event width, further restricted by the finite
Taylor orientation radius for the squarefree root-event polynomial.

The minimum retains both the common event width and the squarefree orientation width for the same root interval. -/
@[expose] def squarefreeLeafWidth
    (event : RationalPolynomial) (squarefree :
      SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) : Fraction.Rational
      :=
  min (Curve.Event.Partition.commonLeafWidth event curve box root)
    (Sturm.Orientation.Basic.rootOrientationWidth
      event squarefree root.interval)

/-- The common squarefree event-resolution width is strictly positive.

Both retained widths are positive; the original rational minimum therefore remains positive. -/
theorem squarefreeLeafWidth_pos
    (event : RationalPolynomial) (squarefree :
      SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) :
    0 < squarefreeLeafWidth event squarefree curve box root :=
  Fraction.Order.Basic.lt_min (Curve.Event.Partition.commonLeafWidth_pos event curve box root)
    (Sturm.Orientation.Basic.rootOrientationWidth_pos
      event squarefree root.interval)

/-- The squarefree width meets the original simultaneous event-resolution budget.

The original rational minimum bounds the common width for the same event, curve, box and root interval. -/
theorem squarefreeLeafWidth_le_common
    (event : RationalPolynomial) (squarefree :
      SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) :
    squarefreeLeafWidth event squarefree curve box root ≤
      Curve.Event.Partition.commonLeafWidth event curve box root :=
  Fraction.Order.Basic.min_le_left _ _

/-- The squarefree width meets the original Taylor orientation budget.

The original rational minimum bounds the orientation width of the same squarefree event on the retained interval. -/
theorem squarefreeLeafWidth_le_orientation
    (event : RationalPolynomial) (squarefree :
      SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) :
    squarefreeLeafWidth event squarefree curve box root ≤
      Sturm.Orientation.Basic.rootOrientationWidth
        event squarefree root.interval :=
  Fraction.Order.Basic.min_le_right _ _

/-- Compute the finite contraction depth reaching half the squarefree event-resolution width.

The depth uses the original interval width and half of the retained minimum, with the same geometric contraction
procedure. -/
@[expose] def squarefreeDepth
    (event : RationalPolynomial) (squarefree :
      SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) : Nat :=
  Approximation.Rational.Contraction.geometricDepth (Bounds.width root.interval)
    (squarefreeLeafWidth event squarefree curve box root / 2)

/-- Build the original safe-cut subdivision at the squarefree orientation depth.

Every retained leaf is selected using the original event polynomial, curve, box and root interval. -/
@[expose] def squarefreeSubdivision
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) :
    Subdivision event curve box :=
  Subdivision.build event eventNonzero curve box
    (squarefreeDepth event squarefree curve box root) root

/-- Every squarefree-resolution leaf refines the original parameter interval. -/
theorem squarefreeSubdivision_leaf_refines
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves) :
    leaf.interval.Refines root.interval :=
  Subdivision.build_leaf_refines event eventNonzero curve box
    (squarefreeDepth event squarefree curve box root) root member

/-- Every retained leaf is strictly narrower than the common squarefree orientation width. -/
theorem squarefreeSubdivision_leaf_width_lt
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves) :
    (Bounds.width leaf.interval) <
      squarefreeLeafWidth event squarefree curve box root := open Purelib.Algebra.Field in by
  let leafWidth := squarefreeLeafWidth event squarefree curve box root
  have leafWidthPositive : 0 < leafWidth := by
    simpa only [leafWidth] using
      squarefreeLeafWidth_pos event squarefree curve box root
  have geometric :=
    Approximation.Rational.Contraction.geometricDepth_sufficient
      (width := (Bounds.width root.interval)) (epsilon := leafWidth / 2)
      (Bounds.width_nonneg root.interval)
      (Fraction.Order.Field.div_pos_direct leafWidthPositive
        (show (0 : Fraction.Rational) < 2 by decide))
  have geometric' :
      (2 / 3 : Fraction.Rational) ^
          squarefreeDepth event squarefree curve box root *
            (Bounds.width root.interval) ≤ leafWidth / 2 := by
    simpa only [squarefreeDepth, leafWidth] using geometric
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Fraction.Rational) < 1 by decide) leafWidthPositive
    rw [ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Fraction.Rational)⁻¹ = 1 / 2 := by
      rw [ExplicitField.div_eq_mul_inv]
      exact (_root_.one_mul _).symm
    rw [halfInverse]
    simpa only [Fraction.Field.mul_comm, one_mul] using scaled
  exact (Subdivision.build_leaf_width_le event eventNonzero curve box
    (squarefreeDepth event squarefree curve box root) root member).trans_lt
      (geometric'.trans_lt halfBelow)

/-- The finer squarefree leaves still telescope to the exact parent event
count. -/
theorem squarefreeSubdivision_eventCount_sum
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (squarefree : SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) :
    Sturm.Count.Basic.cellCount2 event root =
      ((squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves.map
          (Sturm.Count.Basic.cellCount2 event)).sum :=
  Subdivision.build_cellEventCount_sum event eventNonzero curve box
    (squarefreeDepth event squarefree curve box root) root
end Purelib.RootIsolation.Curve.Event.Partition.Squarefree

end
