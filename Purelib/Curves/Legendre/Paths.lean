module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.Fin.Two
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
public import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap

import Purelib.Data.Rat.Fraction.Compatibility
meta import Purelib.Elab.Deriving.Repr
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Event
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Fin

open Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.RootIsolation.Owner

open Purelib.RootIsolation.Progressive.Braid.Projected

open Purelib.RootIsolation.Progressive.Braid.Projected.Overlap

open Purelib.RootIsolation.Progressive.Chamber

open Purelib.Topology.Knot

public section

/-!
# Certified finite paths in the Legendre parameter plane

The Legendre family is represented by the exact dense polynomial
`x * (x - 1) * (x - lambda)`.  Axis-aligned parameter segments carry finite
rational clearances from the singular parameters zero and one.  A certified
segment then adds the existing simple-root chamber overlap, an extracted
three-strand braid word, and a common lower bound for all bridge clearances.
-/

namespace Purelib.Curves.Legendre.Paths

open Purelib.Topology.Knot.Braid

/-- Exact rational coordinates in the Legendre parameter plane. -/
abbrev Coordinate := Fraction.Rational
/-- Exact Gaussian rational parameter values. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- Executable dense Gaussian polynomials for the Legendre family. -/
abbrev GaussianPolynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- A certified finite frame of isolated simple polynomial roots. -/
abbrev ChamberFrame := Frame.ChamberFrame
/-- A certified matching and bridge family between two root frames. -/
abbrev ChamberOverlap := Overlap.ChamberOverlap
/-- An executable finite bijection with inverse laws. -/
abbrev Bijection := Data.Fin.Bijection
/-- A root frame with a certified left-to-right projection order. -/
abbrev ProjectedFrame := Frame.ProjectedFrame
/-- An atomic projected overlap between the two retained ordered root frames. -/
abbrev ProjectedOverlap {strands : Nat}
    (start finish : ProjectedFrame strands) :=
  Overlap.ProjectedOverlap start finish

/-- Construct an exact parameter value from its real and imaginary coordinates. -/
@[expose] def gaussian (real imaginary : Coordinate) : Gaussian :=
  ⟨real, imaginary⟩

/-- Exact high-to-low coefficient representation of `x * (x - 1) * (x - lambda)`. -/
@[expose] def polynomial (lambda : Gaussian) : GaussianPolynomial :=
  ⟨[1, -(1 + lambda), lambda, 0]⟩

/-- The displayed Legendre polynomial is nonzero for every parameter. -/
@[simp] theorem polynomial_isZero (lambda : Gaussian) :
    (polynomial lambda).isZero = false := rfl

/-- The displayed Legendre polynomial has degree three. -/
@[simp] theorem polynomial_natDegree (lambda : Gaussian) :
    (polynomial lambda).natDegree = 3 := rfl

/-- The coefficient representation evaluates to x times x minus one times x minus lambda. -/
theorem polynomial_eval (lambda point : Gaussian) :
    (polynomial lambda).eval point =
      point * (point - 1) * (point - lambda) := by
  unfold polynomial DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- Zero is a root of the displayed Legendre polynomial. -/
@[simp] theorem polynomial_zero (lambda : Gaussian) :
    (polynomial lambda).eval 0 = 0 := by
  rw [polynomial_eval]
  ring1

/-- One is a root of the displayed Legendre polynomial. -/
@[simp] theorem polynomial_one (lambda : Gaussian) :
    (polynomial lambda).eval 1 = 0 := by
  rw [polynomial_eval]
  ring1

/-- The parameter itself is a root of the displayed Legendre polynomial. -/
@[simp] theorem polynomial_lambda (lambda : Gaussian) :
    (polynomial lambda).eval lambda = 0 := by
  rw [polynomial_eval]
  ring1

/-- Logical order of the finite branch points. At a real base parameter between zero and one this is their geometric
order `0, lambda, 1`. -/
@[expose] def branchPoint (lambda : Gaussian) (label : Fin 3) : Gaussian :=
  if label = 0 then 0 else if label = 1 then lambda else 1

/-- Logical branch label zero denotes the root zero. -/
@[simp] theorem branchPoint_zero (lambda : Gaussian) :
    branchPoint lambda 0 = 0 := rfl

/-- Logical branch label one denotes the parameter root. -/
@[simp] theorem branchPoint_one (lambda : Gaussian) :
    branchPoint lambda 1 = lambda := rfl

/-- Logical branch label two denotes the root one. -/
@[simp] theorem branchPoint_two (lambda : Gaussian) :
    branchPoint lambda 2 = 1 := rfl

/-! ## Exact axis-aligned parameter geometry -/

/-- An exact horizontal or vertical segment indexed by its Gaussian endpoints. -/
inductive AxisSegment : Gaussian -> Gaussian -> Type
  /-- A horizontal segment with fixed imaginary coordinate. -/ | horizontal (xStart xFinish y :
    Coordinate) :
      AxisSegment (gaussian xStart y)
        (gaussian xFinish y)
  /-- A vertical segment with fixed real coordinate. -/ | vertical (x yStart yFinish : Coordinate)
    :
      AxisSegment (gaussian x yStart)
        (gaussian x yFinish)

namespace AxisSegment

/-- Evaluate the affine parametrization of the retained axis segment. -/
@[expose] def pointAt {start finish : Curves.Legendre.Paths.Gaussian}
    (segment : Curves.Legendre.Paths.AxisSegment start finish) (parameter : Curves.Legendre.Paths.Coordinate) : Gaussian
      :=
  match segment with
  | .horizontal xStart xFinish y =>
      Curves.Legendre.Paths.gaussian (xStart + (xFinish - xStart) * parameter) y
  | .vertical x yStart yFinish =>
      Curves.Legendre.Paths.gaussian x (yStart + (yFinish - yStart) * parameter)

/-- The axis-segment parametrization starts at its first endpoint. -/
@[simp] theorem pointAt_zero {start finish : Curves.Legendre.Paths.Gaussian}
    (segment : Curves.Legendre.Paths.AxisSegment start finish) : segment.pointAt 0 = start := by
  cases segment with
  | horizontal xStart xFinish y =>
      apply Data.Gaussian.Basic.ext
      · change xStart + (xFinish - xStart) * 0 = xStart
        ring1
      · rfl
  | vertical x yStart yFinish =>
      apply Data.Gaussian.Basic.ext
      · rfl
      · change yStart + (yFinish - yStart) * 0 = yStart
        ring1

/-- The axis-segment parametrization ends at its second endpoint. -/
@[simp] theorem pointAt_one {start finish : Curves.Legendre.Paths.Gaussian}
    (segment : Curves.Legendre.Paths.AxisSegment start finish) : segment.pointAt 1 = finish := by
  cases segment with
  | horizontal xStart xFinish y =>
      apply Data.Gaussian.Basic.ext
      · change xStart + (xFinish - xStart) * 1 = xFinish
        ring1
      · rfl
  | vertical x yStart yFinish =>
      apply Data.Gaussian.Basic.ext
      · rfl
      · change yStart + (yFinish - yStart) * 1 = yFinish
        ring1

/-- Reverse an axis segment by exchanging its endpoints and preserving its fixed coordinate. -/
@[expose] def reverse {start finish : Curves.Legendre.Paths.Gaussian}
    (segment : Curves.Legendre.Paths.AxisSegment start finish) : Curves.Legendre.Paths.AxisSegment finish start :=
  match segment with
  | .horizontal xStart xFinish y => .horizontal xFinish xStart y
  | .vertical x yStart yFinish => .vertical x yFinish yStart

/-- Reversing an axis segment twice restores the exact segment. -/
@[simp] theorem reverse_reverse {start finish : Curves.Legendre.Paths.Gaussian}
    (segment : Curves.Legendre.Paths.AxisSegment start finish) : segment.reverse.reverse = segment := by
  cases segment <;> rfl

/-- Squared fixed-coordinate gap from an excluded point. It is independent of the segment parameter and hence certifies
the entire segment. -/
@[expose] def fixedGapSq {start finish : Curves.Legendre.Paths.Gaussian}
    (segment : Curves.Legendre.Paths.AxisSegment start finish) (excluded : Curves.Legendre.Paths.Gaussian) : Coordinate
      :=
  match segment with
  | .horizontal _ _ y => (y - excluded.im) ^ 2
  | .vertical x _ _ => (x - excluded.re) ^ 2

/-- Segment reversal preserves its fixed-coordinate squared gap. -/
@[simp] theorem fixedGapSq_reverse {start finish : Curves.Legendre.Paths.Gaussian}
    (segment : Curves.Legendre.Paths.AxisSegment start finish) (excluded : Curves.Legendre.Paths.Gaussian) :
    segment.reverse.fixedGapSq excluded = segment.fixedGapSq excluded := by
  cases segment <;> rfl

set_option genInjectivity false in
/-- A positive rational lower bound obtained from the coordinate fixed along an axis-aligned segment. -/
structure Clearance {start finish : Curves.Legendre.Paths.Gaussian}
    (segment : Curves.Legendre.Paths.AxisSegment start finish) (excluded : Curves.Legendre.Paths.Gaussian) where
  /-- The retained rational lower bound for squared distance from the excluded point. -/ bound :
    Curves.Legendre.Paths.Coordinate
  /-- The retained squared clearance is strictly positive. -/ positive : 0 < bound
  /-- The clearance bound does not exceed the fixed-coordinate squared gap. -/ lower : bound <= segment.fixedGapSq
    excluded

constructive_injectivity Clearance

/-- The fixed-coordinate clearance bounds squared distance at every affine parameter. -/
theorem Clearance.normSq_lower {start finish : Curves.Legendre.Paths.Gaussian}
    {segment : Curves.Legendre.Paths.AxisSegment start finish} {excluded : Curves.Legendre.Paths.Gaussian}
    (clearance : Clearance segment excluded) (parameter :
      Curves.Legendre.Paths.Coordinate) :
    clearance.bound <=
      Data.Gaussian.Norm.Basic.normSq
        (segment.pointAt parameter - excluded) := by
  cases segment with
  | horizontal xStart xFinish y =>
      change clearance.bound <=
        (xStart + (xFinish - xStart) * parameter - excluded.re) ^ 2 +
          (y - excluded.im) ^ 2
      exact clearance.lower.trans
        (le_add_of_nonneg_left
          (Fraction.Order.Arithmetic.sq_nonneg_direct
            (xStart + (xFinish - xStart) * parameter - excluded.re)))
  | vertical x yStart yFinish =>
      change clearance.bound <=
        (x - excluded.re) ^ 2 +
          (yStart + (yFinish - yStart) * parameter - excluded.im) ^ 2
      exact clearance.lower.trans
        (le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.sq_nonneg_direct
            (yStart + (yFinish - yStart) * parameter - excluded.im)))

/-- Preserve an excluded-point clearance when reversing its axis segment. -/
@[expose] def Clearance.reverse {start finish : Curves.Legendre.Paths.Gaussian}
    {segment : Curves.Legendre.Paths.AxisSegment start finish} {excluded : Curves.Legendre.Paths.Gaussian}
    (clearance : Clearance segment excluded) :
    Clearance segment.reverse excluded where
  bound := clearance.bound
  positive := clearance.positive
  lower := by rw [fixedGapSq_reverse]; exact clearance.lower

set_option genInjectivity false in
/-- The exact geometric portion of a Legendre segment. -/
structure Safe {start finish : Curves.Legendre.Paths.Gaussian}
    (segment : Curves.Legendre.Paths.AxisSegment start finish) where
  /-- The segment retains a positive squared clearance from the singular parameter zero. -/ avoidsZero :
    Clearance segment 0
  /-- The segment retains a positive squared clearance from the singular parameter one. -/ avoidsOne :
    Clearance segment 1

constructive_injectivity Safe

/-- Reverse both singular-parameter clearance certificates with their segment. -/
@[expose] def Safe.reverse {start finish : Curves.Legendre.Paths.Gaussian}
    {segment : Curves.Legendre.Paths.AxisSegment start finish} (safe : Safe segment) :
    Safe segment.reverse where
  avoidsZero := safe.avoidsZero.reverse
  avoidsOne := safe.avoidsOne.reverse

end AxisSegment

set_option genInjectivity false in
/-- A finite geometric path whose every segment carries exact avoidance of both singular parameters. -/
inductive SafePath : (start finish : Gaussian) -> Type
  /-- The empty geometric path at one exact parameter value. -/ | nil (point : Gaussian) :
    SafePath point point
  /-- Prepend an axis segment and its two clearances to a compatible safe path. -/ | cons {start middle finish :
    Gaussian}
      (segment : AxisSegment start middle)
      (safe : Curves.Legendre.Paths.AxisSegment.Safe segment)
      (remaining : SafePath middle finish) : SafePath start
        finish

constructive_injectivity SafePath

namespace SafePath

/-- Count the finite segments of a geometrically safe path. -/
@[expose] def stepCount : {start finish : Curves.Legendre.Paths.Gaussian} -> Curves.Legendre.Paths.SafePath start finish
  -> Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ _ remaining => remaining.stepCount + 1

/-- Concatenate two safe paths at their common exact endpoint. -/
@[expose] def append {first middle last : Curves.Legendre.Paths.Gaussian}
    (initial : Curves.Legendre.Paths.SafePath first middle) (remaining : Curves.Legendre.Paths.SafePath middle last) :
    Curves.Legendre.Paths.SafePath first last :=
  match initial with
  | .nil _ => remaining
  | .cons segment safe tail => .cons segment safe (tail.append remaining)

/-- Reverse the segment order and every retained geometric clearance of a safe path. -/
@[expose] def reverse : {start finish : Curves.Legendre.Paths.Gaussian} ->
    Curves.Legendre.Paths.SafePath start finish -> Curves.Legendre.Paths.SafePath finish start
  | _, _, .nil point => .nil point
  | start, _, .cons segment safe remaining =>
      remaining.reverse.append
        (.cons segment.reverse safe.reverse (.nil start))

end SafePath

/-! ## Executable rational rectangle examples -/

namespace RectangleExamples

/-- The rational coordinate one quarter. -/
@[expose] def quarter : Coordinate := 1 / 4
/-- The rational coordinate three quarters. -/
@[expose] def threeQuarters : Coordinate := 3 / 4
/-- The rational coordinate five quarters. -/
@[expose] def fiveQuarters : Coordinate := 5 / 4
/-- The rational coordinate minus one quarter. -/
@[expose] def negativeQuarter : Coordinate := -(1 / 4)
/-- The squared clearance constant one sixteenth. -/
@[expose] def sixteenth : Coordinate := 1 / 16

/-- The northeast vertex of the rational square of half-width one quarter centered at zero. -/
@[expose] def zeroNorthEast : Gaussian := Curves.Legendre.Paths.gaussian quarter
  quarter
/-- The northwest vertex of the rational square of half-width one quarter centered at zero. -/
@[expose] def zeroNorthWest : Gaussian := Curves.Legendre.Paths.gaussian
  negativeQuarter quarter
/-- The southwest vertex of the rational square of half-width one quarter centered at zero. -/
@[expose] def zeroSouthWest : Gaussian := Curves.Legendre.Paths.gaussian
  negativeQuarter negativeQuarter
/-- The southeast vertex of the rational square of half-width one quarter centered at zero. -/
@[expose] def zeroSouthEast : Gaussian := Curves.Legendre.Paths.gaussian quarter
  negativeQuarter

/-- The westward top segment of the square centered at zero. -/
@[expose] def zeroTop : Curves.Legendre.Paths.AxisSegment zeroNorthEast
  zeroNorthWest :=
  .horizontal quarter negativeQuarter
    quarter

/-- The southward left segment of the square centered at zero. -/
@[expose] def zeroLeft : Curves.Legendre.Paths.AxisSegment zeroNorthWest
  zeroSouthWest :=
  .vertical negativeQuarter quarter
    negativeQuarter

/-- The eastward bottom segment of the square centered at zero. -/
@[expose] def zeroBottom : Curves.Legendre.Paths.AxisSegment zeroSouthWest
  zeroSouthEast :=
  .horizontal negativeQuarter quarter
    negativeQuarter

/-- The northward right segment of the square centered at zero. -/
@[expose] def zeroRight : Curves.Legendre.Paths.AxisSegment zeroSouthEast
  zeroNorthEast :=
  .vertical quarter negativeQuarter
    quarter

/-- Build a segment clearance from a fixed-coordinate squared gap of at least one sixteenth. -/
@[expose] def clearanceSixteenth {start finish excluded : Curves.Legendre.Paths.Gaussian}
    (segment : Curves.Legendre.Paths.AxisSegment start finish)
    (lower : sixteenth <= segment.fixedGapSq excluded) :
    Curves.Legendre.Paths.AxisSegment.Clearance segment excluded where
  bound := sixteenth
  positive := by decide
  lower := lower

/-- Exact one-sixteenth squared clearances from zero and one along the square's top segment centered at zero. -/
@[expose] def zeroTopSafe : Curves.Legendre.Paths.AxisSegment.Safe zeroTop where
  avoidsZero := clearanceSixteenth
    zeroTop (by decide)
  avoidsOne := clearanceSixteenth
    zeroTop (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's left segment centered at zero. -/
@[expose] def zeroLeftSafe : Curves.Legendre.Paths.AxisSegment.Safe zeroLeft
  where
  avoidsZero := clearanceSixteenth
    zeroLeft (by decide)
  avoidsOne := clearanceSixteenth
    zeroLeft (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's bottom segment centered at zero. -/
@[expose] def zeroBottomSafe : Curves.Legendre.Paths.AxisSegment.Safe zeroBottom
  where
  avoidsZero := clearanceSixteenth
    zeroBottom (by decide)
  avoidsOne := clearanceSixteenth
    zeroBottom (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's right segment centered at zero. -/
@[expose] def zeroRightSafe : Curves.Legendre.Paths.AxisSegment.Safe zeroRight
  where
  avoidsZero := clearanceSixteenth
    zeroRight (by decide)
  avoidsOne := clearanceSixteenth
    zeroRight (by decide)

/-- The four-segment counterclockwise square path centered at zero, with both singular-parameter clearances retained. -/
@[expose] def zeroRectangle : Curves.Legendre.Paths.SafePath zeroNorthEast
  zeroNorthEast :=
  .cons zeroTop zeroTopSafe
    (.cons zeroLeft zeroLeftSafe
      (.cons zeroBottom zeroBottomSafe
        (.cons zeroRight zeroRightSafe
          (.nil zeroNorthEast))))

/-- The displayed square path centered at zero has four segments. -/
@[simp] theorem zeroRectangle_stepCount : Curves.Legendre.Paths.RectangleExamples.zeroRectangle.stepCount = 4 := rfl

/-- The northeast vertex of the rational square of half-width one quarter centered at one. -/
@[expose] def oneNorthEast : Gaussian := Curves.Legendre.Paths.gaussian
  fiveQuarters quarter
/-- The northwest vertex of the rational square of half-width one quarter centered at one. -/
@[expose] def oneNorthWest : Gaussian := Curves.Legendre.Paths.gaussian
  threeQuarters quarter
/-- The southwest vertex of the rational square of half-width one quarter centered at one. -/
@[expose] def oneSouthWest : Gaussian := Curves.Legendre.Paths.gaussian
  threeQuarters negativeQuarter
/-- The southeast vertex of the rational square of half-width one quarter centered at one. -/
@[expose] def oneSouthEast : Gaussian := Curves.Legendre.Paths.gaussian
  fiveQuarters negativeQuarter

/-- The westward top segment of the square centered at one. -/
@[expose] def oneTop : Curves.Legendre.Paths.AxisSegment oneNorthEast
  oneNorthWest :=
  .horizontal fiveQuarters threeQuarters
    quarter

/-- The southward left segment of the square centered at one. -/
@[expose] def oneLeft : Curves.Legendre.Paths.AxisSegment oneNorthWest
  oneSouthWest :=
  .vertical threeQuarters quarter
    negativeQuarter

/-- The eastward bottom segment of the square centered at one. -/
@[expose] def oneBottom : Curves.Legendre.Paths.AxisSegment oneSouthWest
  oneSouthEast :=
  .horizontal threeQuarters fiveQuarters
    negativeQuarter

/-- The northward right segment of the square centered at one. -/
@[expose] def oneRight : Curves.Legendre.Paths.AxisSegment oneSouthEast
  oneNorthEast :=
  .vertical fiveQuarters negativeQuarter
    quarter

/-- Exact one-sixteenth squared clearances from zero and one along the square's top segment centered at one. -/
@[expose] def oneTopSafe : Curves.Legendre.Paths.AxisSegment.Safe oneTop where
  avoidsZero := clearanceSixteenth
    oneTop (by decide)
  avoidsOne := clearanceSixteenth oneTop
    (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's left segment centered at one. -/
@[expose] def oneLeftSafe : Curves.Legendre.Paths.AxisSegment.Safe oneLeft where
  avoidsZero := clearanceSixteenth
    oneLeft (by decide)
  avoidsOne := clearanceSixteenth
    oneLeft (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's bottom segment centered at one. -/
@[expose] def oneBottomSafe : Curves.Legendre.Paths.AxisSegment.Safe oneBottom
  where
  avoidsZero := clearanceSixteenth
    oneBottom (by decide)
  avoidsOne := clearanceSixteenth
    oneBottom (by decide)

/-- Exact one-sixteenth squared clearances from zero and one along the square's right segment centered at one. -/
@[expose] def oneRightSafe : Curves.Legendre.Paths.AxisSegment.Safe oneRight
  where
  avoidsZero := clearanceSixteenth
    oneRight (by decide)
  avoidsOne := clearanceSixteenth
    oneRight (by decide)

/-- The four-segment counterclockwise square path centered at one, with both singular-parameter clearances retained. -/
@[expose] def oneRectangle : Curves.Legendre.Paths.SafePath oneNorthEast
  oneNorthEast :=
  .cons oneTop oneTopSafe
    (.cons oneLeft oneLeftSafe
      (.cons oneBottom oneBottomSafe
        (.cons oneRight oneRightSafe
          (.nil oneNorthEast))))

/-- The displayed square path centered at one has four segments. -/
@[simp] theorem oneRectangle_stepCount : Curves.Legendre.Paths.RectangleExamples.oneRectangle.stepCount = 4 := rfl

/-- Every point of the retained rectangle's top edge satisfies its original certified lower bound on squared distance
from zero. -/
example (parameter : Curves.Legendre.Paths.Coordinate) :
    Curves.Legendre.Paths.RectangleExamples.zeroTopSafe.avoidsZero.bound <=
      Data.Gaussian.Norm.Basic.normSq
      (Curves.Legendre.Paths.RectangleExamples.zeroTop.pointAt parameter) :=
  by
    simpa only [Purelib.Data.Gaussian.Basic.sub_zero] using
      Curves.Legendre.Paths.RectangleExamples.zeroTopSafe.avoidsZero.normSq_lower parameter

/-- Every point of the retained rectangle's top edge satisfies its original certified lower bound on squared distance
from zero. -/
example (parameter : Curves.Legendre.Paths.Coordinate) :
    Curves.Legendre.Paths.RectangleExamples.oneLeftSafe.avoidsOne.bound <=
      Data.Gaussian.Norm.Basic.normSq
      (Curves.Legendre.Paths.RectangleExamples.oneLeft.pointAt parameter - 1) :=
  Curves.Legendre.Paths.RectangleExamples.oneLeftSafe.avoidsOne.normSq_lower parameter

end RectangleExamples

/-! ## Root frames and certified coefficient segments -/

set_option genInjectivity false in
/-- A Legendre chamber frame with a displayed logical identification of its three finite roots as `0`, `lambda`, and
`1`. -/
structure Frame (lambda : Gaussian) where
  /-- The original certified simple-root chamber frame. -/ chamber : ChamberFrame
  /-- The chamber polynomial is the exact displayed Legendre polynomial. -/ polynomial_eq : chamber.polynomial =
    polynomial lambda
  /-- The bijection identifying the three logical branch labels with chamber owners. -/ labels :
    Bijection 3 chamber.degree
  /-- Each logically labelled owner box contains its exact displayed branch point. -/ owner_contains : forall label :
    Fin 3,
    (chamber.owner (labels.forward label)).box.Contains
      (branchPoint lambda label)
  /-- The independent bijection from projection positions to original chamber owners. -/ projectionOrder :
    Bijection 3 chamber.degree
  /-- The certified refined root owner at each projection position. -/ projectionOwner : Fin 3 -> Local.Basic.LocalOwner
    chamber.polynomial
  /-- Each projection sample box refines its original chamber-owner box. -/ projection_refines : forall position : Fin
    3,
    (projectionOwner position).box.Refines
      (chamber.owner (projectionOrder.forward position)).box
  /-- Projection sample boxes are strictly ordered by their real-coordinate intervals. -/ projection_xOrdered : forall
    left right : Fin 3, left.val < right.val ->
    (projectionOwner left).box.xUpper < (projectionOwner right).box.xLower

constructive_injectivity Frame

namespace Frame

/-- The chamber degree is exactly the displayed Legendre cubic degree. -/
theorem degree_eq_three {lambda : Curves.Legendre.Paths.Gaussian} (frame : Curves.Legendre.Paths.Frame lambda) :
    frame.chamber.degree = 3 := by
  calc
    frame.chamber.degree = frame.chamber.polynomial.natDegree :=
      frame.chamber.reference.polynomial_natDegree.symm
    _ = (Curves.Legendre.Paths.polynomial lambda).natDegree :=
      congrArg DensePolynomial.natDegree
        frame.polynomial_eq
    _ = 3 := Curves.Legendre.Paths.polynomial_natDegree lambda

/-- The independently certified left-to-right projection order on this Legendre root frame. -/
@[expose] def projected {lambda : Curves.Legendre.Paths.Gaussian} (frame : Curves.Legendre.Paths.Frame lambda) :
  Curves.Legendre.Paths.ProjectedFrame 3 where
  chamber := frame.chamber
  degree_eq := frame.degree_eq_three
  orderToOwner := frame.projectionOrder
  sampleOwner := frame.projectionOwner
  sample_refines_owner := frame.projection_refines
  xOrdered := frame.projection_xOrdered

/-- Distinct logical branch labels have separated retained root-owner boxes. -/
theorem rootSeparation {lambda : Curves.Legendre.Paths.Gaussian} (frame : Curves.Legendre.Paths.Frame lambda)
    (left right : Fin 3) (different : left ≠ right) :
    (frame.chamber.owner (frame.labels.forward left)).box.Separated
      (frame.chamber.owner (frame.labels.forward right)).box :=
  frame.chamber.pairwiseSeparated _ _
    (fun equal => different (frame.labels.forward_injective equal))

end Frame

set_option genInjectivity false in
/-- A common positive rational lower bound for every owner bridge at both ends of one chamber overlap.

These are the finite square-root continuation clearances retained by the segment. -/
structure BridgeClearance {start finish : Gaussian}
    (left : Frame start) (right : Frame finish)
    (overlap : ChamberOverlap left.chamber right.chamber) where
  /-- The common rational lower bound for all endpoint bridge clearances. -/ bound : Coordinate
  /-- The common bridge bound is strictly positive. -/ positive : 0 < bound
  /-- The common clearance bounds every bridge clearance at the left endpoint. -/ leftLower : forall index :
    left.chamber.Index,
    bound <= (overlap.bridge index).leftClearance.bound
  /-- The common clearance bounds every bridge clearance at the right endpoint. -/ rightLower : forall index :
    left.chamber.Index,
    bound <= (overlap.bridge index).rightClearance.bound

constructive_injectivity BridgeClearance

set_option genInjectivity false in
/-- One fully certified Legendre parameter segment. -/
structure Segment {start finish : Gaussian}
    (left : Frame start) (right : Frame finish) where
  /-- The exact axis-aligned parameter segment joining the two frame parameters. -/ geometry :
    AxisSegment start finish
  /-- The segment clearance certificates for both singular parameter values. -/ safe :
    Curves.Legendre.Paths.AxisSegment.Safe geometry
  /-- The atomic projected root overlap from which the braid event is extracted. -/ projection :
    ProjectedOverlap left.projected right.projected
  /-- The common positive bound for the original overlap bridge clearances. -/ sheetClearance :
    BridgeClearance left right projection.chamberOverlap

constructive_injectivity Segment

namespace Segment

/-- Construct a segment only from an atomic projected overlap.

Its braid word is extracted from the certified stationary/crossing event rather than accepted as an independent
annotation. -/
@[expose] def ofProjectedOverlap {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    (geometry : Curves.Legendre.Paths.AxisSegment start finish) (safe : Curves.Legendre.Paths.AxisSegment.Safe geometry)
    (projection : Curves.Legendre.Paths.ProjectedOverlap left.projected right.projected)
    (clearance : Curves.Legendre.Paths.BridgeClearance left right projection.chamberOverlap) :
    Curves.Legendre.Paths.Segment left right where
  geometry := geometry
  safe := safe
  projection := projection
  sheetClearance := clearance

/-- The root-owner overlap underlying the certified projected event. -/
@[expose] def coefficientOverlap {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    (segment : Curves.Legendre.Paths.Segment left right) : Curves.Legendre.Paths.ChamberOverlap left.chamber
      right.chamber :=
  segment.projection.chamberOverlap

/-- The segment word is the output of its finite projected crossing chart. -/
@[expose] def crossings {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    (segment : Curves.Legendre.Paths.Segment left right) : Braid.Word 3 :=
  segment.projection.word

/-- The source owner at one certified projection position. -/
@[expose] def startOwnerIndex {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    (_segment : Curves.Legendre.Paths.Segment left right) (position : Fin 3) :
    left.chamber.Index :=
  left.projected.ownerIndex position

/-- Reverse a bridge-clearance certificate using the inverse owner matching.

The common bound is preserved and the two endpoint lower-bound families exchange roles. -/
@[expose] def reverseBridgeClearance {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    {overlap : Curves.Legendre.Paths.ChamberOverlap left.chamber right.chamber}
    (clearance : Curves.Legendre.Paths.BridgeClearance left right overlap) :
    Curves.Legendre.Paths.BridgeClearance right left overlap.reverse where
  bound := clearance.bound
  positive := clearance.positive
  leftLower := by
    intro index
    change clearance.bound <=
      (overlap.bridge (overlap.matching.backward index)).rightClearance.bound
    exact clearance.rightLower (overlap.matching.backward index)
  rightLower := by
    intro index
    change clearance.bound <=
      (overlap.bridge (overlap.matching.backward index)).leftClearance.bound
    exact clearance.leftLower (overlap.matching.backward index)

/-- Reverse every geometric, root, sheet, and braid certificate of a segment. -/
@[expose] def reverse {start finish : Curves.Legendre.Paths.Gaussian} {left : Curves.Legendre.Paths.Frame start}
    {right : Curves.Legendre.Paths.Frame finish} (segment : Curves.Legendre.Paths.Segment left right) :
    Curves.Legendre.Paths.Segment right left where
  geometry := segment.geometry.reverse
  safe := segment.safe.reverse
  projection := segment.projection.reverse
  sheetClearance := by
    rw [ProjectedOverlap.reverse_chamberOverlap]
    exact reverseBridgeClearance segment.sheetClearance

/-- The geometry of a reversed certified segment is the reversed original geometry. -/
@[simp] theorem reverse_geometry {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    (segment : Curves.Legendre.Paths.Segment left right) :
    segment.reverse.geometry = segment.geometry.reverse := rfl

/-- Reversing a certified segment inverts its extracted braid word. -/
@[simp] theorem reverse_crossings {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    (segment : Curves.Legendre.Paths.Segment left right) :
    segment.reverse.crossings = segment.crossings.inverse := by
  exact ProjectedOverlap.reverse_word
    segment.projection

end Segment

/-! ## Finite folds of certified segments -/

set_option genInjectivity false in
/-- A finite chain of certified parameter segments indexed by its original endpoint root frames. -/
inductive Path : {start finish : Gaussian} ->
    Frame start -> Frame finish -> Type 2
  /-- The empty certified path at one retained root frame. -/ | nil {parameter : Gaussian} (frame
    : Frame parameter) : Path frame frame
  /-- Prepend a certified segment to a path with its exact intermediate root frame. -/ | cons {start middle finish :
    Gaussian}
      {left : Frame start} {center : Frame middle} {right :
        Frame finish}
      (head : Segment left center) (remaining : Path center right) :
      Path left right

constructive_injectivity Path

namespace Path

/-- Count the finite certified segments in the path. -/
@[expose] def stepCount : {start finish : Curves.Legendre.Paths.Gaussian} ->
    {left : Curves.Legendre.Paths.Frame start} -> {right : Curves.Legendre.Paths.Frame finish} ->
    Curves.Legendre.Paths.Path left right -> Nat
  | _, _, _, _, .nil _ => 0
  | _, _, _, _, .cons _ remaining => remaining.stepCount + 1

/-- Segment words in traversal order, retained before flattening. -/
@[expose] def segmentWords : {start finish : Curves.Legendre.Paths.Gaussian} ->
    {left : Curves.Legendre.Paths.Frame start} -> {right : Curves.Legendre.Paths.Frame finish} ->
    Curves.Legendre.Paths.Path left right -> List (Braid.Word 3)
  | _, _, _, _, .nil _ => []
  | _, _, _, _, .cons head remaining =>
      head.crossings :: remaining.segmentWords

/-- Flatten the projected braid subdivisions in path order. -/
@[expose] def word : {start finish : Curves.Legendre.Paths.Gaussian} ->
    {left : Curves.Legendre.Paths.Frame start} -> {right : Curves.Legendre.Paths.Frame finish} ->
    Curves.Legendre.Paths.Path left right -> Braid.Word 3
  | _, _, _, _, .nil _ => []
  | _, _, _, _, .cons head remaining =>
      head.crossings ++ remaining.word

/-- Fold the actual chamber-owner matchings, independently of the extracted braid word. -/
@[expose] def ownerTransport : {start finish : Curves.Legendre.Paths.Gaussian} ->
    {left : Curves.Legendre.Paths.Frame start} -> {right : Curves.Legendre.Paths.Frame finish} ->
    Curves.Legendre.Paths.Path left right -> Curves.Legendre.Paths.Bijection left.chamber.degree right.chamber.degree
  | _, _, _, _, .nil frame =>
      Data.Fin.Bijection.identity frame.chamber.degree
  | _, _, _, _, .cons head remaining =>
      Data.Fin.Bijection.comp remaining.ownerTransport
        head.projection.chamberOverlap.matching

/-- Every segment's exact bridge box followed by the boxes visited by the remaining logical branch label. -/
@[expose] def bridgeBoxes : {start finish : Curves.Legendre.Paths.Gaussian} ->
    {left : Curves.Legendre.Paths.Frame start} -> {right : Curves.Legendre.Paths.Frame finish} ->
    (path : Curves.Legendre.Paths.Path left right) -> Fin 3 -> List Rational.Box
  | _, _, _, _, .nil _, _ => []
  | _, _, _, _, .cons head remaining, position =>
      (head.projection.chamberOverlap.bridge
        (head.startOwnerIndex position)).box ::
        remaining.bridgeBoxes
          (head.projection.event.permutation.forward position)

/-- A branch-label route retains one bridge box for each segment in the certified path. -/
@[simp] theorem bridgeBoxes_length {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    (path : Curves.Legendre.Paths.Path left right) (label : Fin 3) :
    (path.bridgeBoxes label).length = path.stepCount := by
  induction path generalizing label with
  | nil frame => rfl
  | cons head remaining inductionHypothesis =>
      exact congrArg Nat.succ (inductionHypothesis
        ((ProjectedOverlap.event head.projection).permutation.forward label))

/-- The independently folded owner matching agrees pointwise with the word extracted from the atomic projection charts,
in the certified endpoint projection orders. -/
theorem ownerTransport_agrees {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    (path : Curves.Legendre.Paths.Path left right) (position : Fin 3) :
    path.ownerTransport.forward (left.projected.ownerIndex position) =
      right.projected.ownerIndex (path.word.permutation.forward position) := by
  induction path generalizing position with
  | nil frame =>
      change frame.projected.ownerIndex position =
        frame.projected.ownerIndex position
      rfl
  | @cons pathStart pathMiddle pathFinish pathLeft pathCenter pathRight
      head remaining inductionHypothesis =>
      change remaining.ownerTransport.forward
          (head.projection.chamberOverlap.matching.forward
            (pathLeft.projected.ownerIndex position)) = _
      rw [head.projection.matching_order position]
      calc
        remaining.ownerTransport.forward
            (pathCenter.projected.ownerIndex
              (head.projection.event.permutation.forward position)) =
            pathRight.projected.ownerIndex
              (remaining.word.permutation.forward
                (head.projection.event.permutation.forward position)) :=
          inductionHypothesis
            (head.projection.event.permutation.forward position)
        _ = pathRight.projected.ownerIndex
              ((head.crossings ++ remaining.word).permutation.forward
                position) :=
          congrArg pathRight.projected.ownerIndex
            (Word.permutation_append
              head.crossings remaining.word position).symm

/-- Concatenate certified paths while retaining their exact common intermediate frame. -/
@[expose] def append {first middle last : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame first} {center : Curves.Legendre.Paths.Frame middle} {right :
      Curves.Legendre.Paths.Frame last}
    (initial : Curves.Legendre.Paths.Path left center) (remaining : Curves.Legendre.Paths.Path center right) :
    Curves.Legendre.Paths.Path left right :=
  match initial with
  | .nil _ => remaining
  | .cons head tail => .cons head (tail.append remaining)

open Purelib.Curves.Legendre.Paths.Path in
/-- Concatenating certified paths concatenates their extracted braid words in traversal order. -/
@[simp] theorem word_append {first middle last : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame first} {center : Curves.Legendre.Paths.Frame middle} {right :
      Curves.Legendre.Paths.Frame last}
    (initial : Curves.Legendre.Paths.Path left center) (remaining : Curves.Legendre.Paths.Path center right) :
    (initial.append remaining).word = initial.word ++ remaining.word := by
  induction initial with
  | nil frame => rfl
  | cons head tail inductionHypothesis =>
      change head.crossings ++ (tail.append remaining).word =
        (head.crossings ++ tail.word) ++ remaining.word
      rewrite [inductionHypothesis, Data.List.Append.append_assoc]
      exact Eq.refl _

/-- Owner transport along concatenated paths is the composition of their retained matchings. -/
theorem ownerTransport_append {first middle last : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame first} {center : Curves.Legendre.Paths.Frame middle} {right :
      Curves.Legendre.Paths.Frame last}
    (initial : Curves.Legendre.Paths.Path left center) (remaining : Curves.Legendre.Paths.Path center right)
    (index : left.chamber.Index) :
    (initial.append remaining).ownerTransport.forward index =
      remaining.ownerTransport.forward
        (initial.ownerTransport.forward index) := by
  induction initial with
  | nil frame =>
      change remaining.ownerTransport.forward index =
        remaining.ownerTransport.forward index
      rfl
  | cons head tail inductionHypothesis =>
      exact inductionHypothesis remaining
        (head.projection.chamberOverlap.matching.forward index)

/-- Reverse every certified segment and its order, retaining the reversed root frames. -/
@[expose] def reverse : {start finish : Curves.Legendre.Paths.Gaussian} ->
    {left : Curves.Legendre.Paths.Frame start} -> {right : Curves.Legendre.Paths.Frame finish} ->
    Curves.Legendre.Paths.Path left right -> Curves.Legendre.Paths.Path right left
  | _, _, _, _, .nil frame => .nil frame
  | _, _, _, _, .cons head remaining =>
      remaining.reverse.append (.cons head.reverse (.nil _))

open Purelib.Curves.Legendre.Paths.Path in
/-- Reversing a certified path inverts its extracted braid word. -/
@[simp] theorem word_reverse {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    (path : Curves.Legendre.Paths.Path left right) : path.reverse.word = path.word.inverse := by
  induction path with
  | nil frame => rfl
  | cons head remaining inductionHypothesis =>
      rw [reverse, word_append, inductionHypothesis]
      simp only [word, head.reverse_crossings, Data.List.Append.append_nil]
      exact (Word.inverse_append
        head.crossings remaining.word).symm

/-- Reversed path transport is the backward map of the original owner bijection. -/
theorem ownerTransport_reverse {start finish : Curves.Legendre.Paths.Gaussian}
    {left : Curves.Legendre.Paths.Frame start} {right : Curves.Legendre.Paths.Frame finish}
    (path : Curves.Legendre.Paths.Path left right) (index : right.chamber.Index) :
    path.reverse.ownerTransport.forward index =
      path.ownerTransport.backward index := by
  induction path with
  | nil frame =>
      change index = index
      rfl
  | cons head remaining inductionHypothesis =>
      rw [reverse, ownerTransport_append]
      simp only [ownerTransport, Curves.Legendre.Paths.Segment.reverse]
      rw [inductionHypothesis index]
      cases head.projection <;> rfl

end Path

@[expose] public section

set_option genInjectivity false in
/-- The ramification label at infinity is kept separate from the three finite-root labels, so its fixed transport is
definitionally visible. -/
inductive RamificationLabel
  /-- One of the three finite root ramification labels. -/ | finite (label : Fin 3)
  /-- The separate ramification label at infinity. -/ | infinity
deriving DecidableEq

constructive_injectivity RamificationLabel

derive_exposed_repr RamificationLabel

end

/-- Transport finite ramification labels by the braid permutation and retain infinity unchanged. -/
@[expose] def transportRamification (word : Braid.Word 3) :
    RamificationLabel -> RamificationLabel
  | .finite label => .finite (word.permutation.forward label)
  | .infinity => .infinity

/-- Every braid word fixes the separate infinity ramification label. -/
@[simp] theorem transportRamification_infinity (word : Braid.Word 3) :
    transportRamification word .infinity = .infinity := rfl

/-- Transport by the inverse braid word undoes ramification-label transport. -/
@[simp] theorem transportRamification_inverse (word : Braid.Word 3)
    (label : RamificationLabel) :
    transportRamification word.inverse (transportRamification word label) =
      label := by
  cases label with
  | infinity => rfl
  | finite label =>
      apply congrArg Curves.Legendre.Paths.RamificationLabel.finite
      calc
        word.inverse.permutation.forward (word.permutation.forward label) =
            word.permutation.reverse.forward
              (word.permutation.forward label) :=
          Word.permutation_inverse word _
        _ = word.permutation.backward (word.permutation.forward label) := rfl
        _ = label := word.permutation.backward_forward label

end Purelib.Curves.Legendre.Paths
