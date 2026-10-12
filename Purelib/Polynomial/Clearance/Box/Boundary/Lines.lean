module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace Purelib.Polynomial.Clearance.Box.Boundary.Lines

open Purelib.Data.Rat.Fraction

/-- Restrict the boundary clearance to the left side, retaining its exact positive bound.

The original polynomial and box remain, and the exact boundary bound and positivity witness are reused for points on the
left vertical side. -/
@[expose] public def leftOfBoundary
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) :
    Clearance.Box.Line.Basic.VerticalLineClearance p box box.xLower where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro y lower upper
    apply clearance.lower
    exact ⟨⟨le_rfl, box.x_valid, lower, upper⟩, Or.inl rfl⟩

/-- Restrict the boundary clearance to the right side, retaining its exact positive bound.

The original polynomial and box remain, and the exact boundary bound and positivity witness are reused for points on the
right vertical side. -/
@[expose] public def rightOfBoundary
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) :
    Clearance.Box.Line.Basic.VerticalLineClearance p box box.xUpper where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro y lower upper
    apply clearance.lower
    exact ⟨⟨box.x_valid, le_rfl, lower, upper⟩,
      Or.inr (Or.inl rfl)⟩

/-- Restrict the boundary clearance to the bottom side, retaining its exact positive bound.

The original polynomial and box remain, and the exact boundary bound and positivity witness are reused for points on the
bottom horizontal side. -/
@[expose] public def bottomOfBoundary
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) :
    Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yLower where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro x lower upper
    apply clearance.lower
    exact ⟨⟨lower, upper, le_rfl, box.y_valid⟩,
      Or.inr (Or.inr (Or.inl rfl))⟩

/-- Restrict the boundary clearance to the top side, retaining its exact positive bound.

The original polynomial and box remain, and the exact boundary bound and positivity witness are reused for points on the
top horizontal side. -/
@[expose] public def topOfBoundary
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) :
    Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yUpper where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro x lower upper
    apply clearance.lower
    exact ⟨⟨lower, upper, box.y_valid, le_rfl⟩,
      Or.inr (Or.inr (Or.inr rfl))⟩

/-- Four side certificates combine by a finite minimum.

The retained bound is the nested minimum in left, right, bottom and top order. Each boundary point uses its side
certificate to bound the same polynomial squared norm. -/
@[expose] public def boundaryOfLines
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (left : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xLower)
    (right : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xUpper)
    (bottom : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yLower)
    (top : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yUpper) :
    Clearance.Box.Boundary.Basic.BoundaryClearance p box := by
  let bound := min left.bound (min right.bound (min bottom.bound top.bound))
  exact
    { bound := bound
      positive := Order.Basic.lt_min left.positive
        (Order.Basic.lt_min right.positive (Order.Basic.lt_min bottom.positive top.positive))
      lower := by
        intro z boundary
        rcases boundary.1 with ⟨xLower, xUpper, yLower, yUpper⟩
        rcases boundary.2 with onLeft | onRight | onBottom | onTop
        · calc
            bound ≤ left.bound := Order.Basic.min_le_left _ _
            _ ≤ Gaussian.Basic.Canonical.normSq (p.eval z) := by
              have lower := left.lower z.im yLower yUpper
              have pointEq : Gaussian.Components.Basic.point box.xLower z.im = z := by
                apply Gaussian.Basic.ext
                · exact onLeft.symm
                · rfl
              simpa only [pointEq] using lower

        · calc
            bound ≤ right.bound :=
              (Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_left _ _)
            _ ≤ Gaussian.Basic.Canonical.normSq (p.eval z) := by
              have lower := right.lower z.im yLower yUpper
              have pointEq : Gaussian.Components.Basic.point box.xUpper z.im = z := by
                apply Gaussian.Basic.ext
                · exact onRight.symm
                · rfl
              simpa only [pointEq] using lower
        · calc
            bound ≤ bottom.bound :=
              (Order.Basic.min_le_right _ _).trans
                ((Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_left _ _))
            _ ≤ Gaussian.Basic.Canonical.normSq (p.eval z) := by
              have lower := bottom.lower z.re xLower xUpper
              have pointEq : Gaussian.Components.Basic.point z.re box.yLower = z := by
                apply Gaussian.Basic.ext
                · rfl
                · exact onBottom.symm
              simpa only [pointEq] using lower
        · calc
            bound ≤ top.bound :=
              (Order.Basic.min_le_right _ _).trans
                ((Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_right _ _))
            _ ≤ Gaussian.Basic.Canonical.normSq (p.eval z) := by
              have lower := top.lower z.re xLower xUpper
              have pointEq : Gaussian.Components.Basic.point z.re box.yUpper = z := by
                apply Gaussian.Basic.ext
                · rfl
                · exact onTop.symm
              simpa only [pointEq] using lower }

/-- The combined boundary bound is exactly the nested minimum of the four retained side bounds.

The constructor stores the nested minimum in left, right, bottom and top order without changing any side bound. -/
@[simp] public theorem boundaryOfLines_bound
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (left : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xLower)
    (right : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xUpper)
    (bottom : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yLower)
    (top : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yUpper) :
    (Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top).bound =
      min left.bound (min right.bound (min bottom.bound top.bound)) := rfl

/-- The combined boundary clearance bound is no larger than the retained left-side bound.

The first minimum is at most its retained left operand, giving this scalar comparison for the constructed boundary
certificate. -/
public theorem boundaryOfLines_bound_le_left
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (left : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xLower)
    (right : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xUpper)
    (bottom : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yLower)
    (top : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yUpper) :
    (Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top).bound <= left.bound := by
  unfold Clearance.Box.Boundary.Lines.boundaryOfLines
  exact Order.Basic.min_le_left _ _

/-- The combined boundary clearance bound is no larger than the retained right-side bound.

The comparison follows through the outer minimum and the right operand of the next minimum, keeping the original four
side certificates. -/
public theorem boundaryOfLines_bound_le_right
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (left : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xLower)
    (right : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xUpper)
    (bottom : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yLower)
    (top : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yUpper) :
    (Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top).bound <= right.bound := by
  unfold Clearance.Box.Boundary.Lines.boundaryOfLines
  exact (Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_left _ _)

/-- The combined boundary clearance bound is no larger than the retained bottom-side bound.

The comparison follows through the first two right operands and the bottom operand of the innermost minimum, with all
original side bounds retained. -/
public theorem boundaryOfLines_bound_le_bottom
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (left : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xLower)
    (right : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xUpper)
    (bottom : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yLower)
    (top : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yUpper) :
    (Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top).bound <= bottom.bound := by
  unfold Clearance.Box.Boundary.Lines.boundaryOfLines
  exact (Order.Basic.min_le_right _ _).trans
    ((Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_left _ _))

/-- The combined boundary clearance bound is no larger than the retained top-side bound.

The comparison follows through all three right operands of the nested minimum, retaining the top certificate and its
original bound. -/
public theorem boundaryOfLines_bound_le_top
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (left : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xLower)
    (right : Clearance.Box.Line.Basic.VerticalLineClearance p box box.xUpper)
    (bottom : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yLower)
    (top : Clearance.Box.Line.Basic.HorizontalLineClearance p box box.yUpper) :
    (Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top).bound <= top.bound := by
  unfold Clearance.Box.Boundary.Lines.boundaryOfLines
  exact (Order.Basic.min_le_right _ _).trans
    ((Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_right _ _))

end Purelib.Polynomial.Clearance.Box.Boundary.Lines
