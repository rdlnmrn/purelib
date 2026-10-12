module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Subdivision
public import Purelib.Polynomial.Clearance.Box.Boundary.Coordinate
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Coordinate
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

@[expose] public section

/-!
# A finite coordinate reference at every nonzero value

An axis connector joins the supplied value to a symmetric square avoiding
zero. A counterclockwise square and the reversed connector give winding one.
This auxiliary construction supplies the erased parity proof for retained
root traces, including traces over a polynomial with no branch in its ambient.
-/

namespace Purelib.Riemann.RootContinuation.CoordinateRootReference

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Components.Basic (point)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate (coordinatePolynomial coordinatePolynomial_eval)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Data
/-- A positive rational radius bounding both coordinates of the base point. -/
public def radius (base : Gaussian.Basic.Canonical) : Rat.Fraction.Rational :=
  max 1 (max (max base.re (-base.re)) (max base.im (-base.im)))

/-- The coordinate-reference radius is strictly positive. -/
public theorem radius_positive (base : Gaussian.Basic.Canonical) : 0 < radius base :=
  lt_of_lt_of_le (by decide) (Rat.Fraction.Order.Basic.le_max_left _ _)

end

open Purelib.Data in
open Purelib.Geometry in
/-- The symmetric reference square containing the base point. -/
public def ambient (base : Gaussian.Basic.Canonical) : Box := Rational.Box.symmetric (radius base)
  (radius_positive base).le

section
open Purelib.Data
/-- The original base point lies in its retained symmetric reference square. -/
public theorem base_inside (base : Gaussian.Basic.Canonical) : (ambient base).Contains base := by
  have reUpper : base.re ≤ radius base :=
    (Rat.Fraction.Order.Basic.le_max_left _ _).trans ((Rat.Fraction.Order.Basic.le_max_left _ _).trans
      (Rat.Fraction.Order.Basic.le_max_right _ _))
  have reNegative : -base.re ≤ radius base :=
    (Rat.Fraction.Order.Basic.le_max_right _ _).trans ((Rat.Fraction.Order.Basic.le_max_left _ _).trans
      (Rat.Fraction.Order.Basic.le_max_right _ _))
  have imUpper : base.im ≤ radius base :=
    (Rat.Fraction.Order.Basic.le_max_left _ _).trans ((Rat.Fraction.Order.Basic.le_max_right _ _).trans
      (Rat.Fraction.Order.Basic.le_max_right _ _))
  have imNegative : -base.im ≤ radius base :=
    (Rat.Fraction.Order.Basic.le_max_right _ _).trans ((Rat.Fraction.Order.Basic.le_max_right _ _).trans
      (Rat.Fraction.Order.Basic.le_max_right _ _))
  change -radius base ≤ base.re ∧ base.re ≤ radius base ∧ -radius base ≤ base.im ∧ base.im ≤ radius base
  exact ⟨by simpa only [neg_neg] using Rat.Fraction.Order.Arithmetic.neg_le_neg_direct reNegative, reUpper,
    by simpa only [neg_neg] using Rat.Fraction.Order.Arithmetic.neg_le_neg_direct imNegative, imUpper⟩

/-- The square of a nonzero rational coordinate is strictly positive. -/
public theorem square_positive {value : Rat.Fraction.Rational} (nonzero : value ≠ 0) : 0 < value ^ 2 := by
  have nonnegative := Rat.Fraction.Order.Arithmetic.sq_nonneg_direct value
  have positive : value ^ 2 ≠ 0 := by
    rw [pow_two]
    exact Rat.Fraction.Field.mul_ne_zero_direct nonzero nonzero
  exact lt_of_le_of_ne nonnegative (Ne.symm positive)

end

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.Geometry
/-- Certify coordinate-polynomial clearance along a nonzero horizontal line.

The squared imaginary coordinate gives a uniform positive lower bound for the Gaussian squared norm. -/
public def horizontal (box : Rational.Box) (y : Rat.Fraction.Rational) (nonzero : y ≠ 0) :
    Clearance.Box.Line.Basic.HorizontalLineClearance Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial box y where
  bound := y ^ 2
  positive := square_positive nonzero
  lower := fun x _ _ => by
    rw [Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval,
      ← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact le_add_of_nonneg_left (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct x)

/-- Certify coordinate-polynomial clearance along a nonzero vertical line.

The squared real coordinate gives a uniform positive lower bound for the Gaussian squared norm. -/
public def vertical (box : Rational.Box) (x : Rat.Fraction.Rational) (nonzero : x ≠ 0) :
    Clearance.Box.Line.Basic.VerticalLineClearance Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial box x where
  bound := x ^ 2
  positive := square_positive nonzero
  lower := fun y _ _ => by
    rw [Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval,
      ← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact le_add_of_nonneg_right (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct y)

end

section
open Purelib.Data
open Purelib.Polynomial
/-- Construct an axis-aligned clear path from a nonzero point to its square anchor.

A decidable coordinate test selects two segments avoiding zero, with both retained inside the original symmetric square.
-/
public def connector (base : Gaussian.Basic.Canonical) (nonzero : base ≠ 0) :
    { path : Polynomial.Geometry.ClearPath Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial (ambient base) base
      (ambient base).anchor // path.WithinAmbient } := by
  let box := ambient base
  have inside := base_inside base
  have lowerNonzero : -(radius base) ≠ 0 := by
    intro zero
    have recovered := congrArg (fun value : Rat.Fraction.Rational => -value) zero
    rw [neg_neg, neg_zero] at recovered
    exact ne_of_gt (radius_positive base) recovered
  by_cases imaginary : base.im = 0
  · have real : base.re ≠ 0 := by
      intro zero
      exact nonzero (Gaussian.Basic.ext zero imaginary)
    let first : Geometry.ClearPath.ClearSegment Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial box base
      (Gaussian.Components.Basic.point base.re box.yLower) :=
      .vertical _ _ _ inside.2.2.1 inside.2.2.2 le_rfl box.y_valid (vertical box base.re real)
    let last : Geometry.ClearPath.ClearSegment Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial box
      (Gaussian.Components.Basic.point base.re box.yLower) box.anchor :=
      .horizontal _ _ _ inside.1 inside.2.1 le_rfl box.x_valid (horizontal box box.yLower lowerNonzero)
    exact ⟨.cons first (.cons last (.nil _)),
      .cons ⟨inside.1, inside.2.1⟩ (.cons ⟨le_rfl, box.y_valid⟩ (.nil _))⟩
  · let first : Geometry.ClearPath.ClearSegment Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial box base
      (Gaussian.Components.Basic.point box.xLower base.im) :=
      .horizontal _ _ _ inside.1 inside.2.1 le_rfl box.x_valid (horizontal box base.im imaginary)
    let last : Geometry.ClearPath.ClearSegment Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial box
      (Gaussian.Components.Basic.point box.xLower base.im) box.anchor :=
      .vertical _ _ _ inside.2.2.1 inside.2.2.2 le_rfl box.y_valid (vertical box box.xLower lowerNonzero)
    exact ⟨.cons first (.cons last (.nil _)),
      .cons ⟨inside.2.2.1, inside.2.2.2⟩ (.cons ⟨le_rfl, box.x_valid⟩ (.nil _))⟩

/-- The four oriented clear edges around the retained symmetric square.

The path starts and ends at the anchor and follows the counterclockwise boundary with coordinate-polynomial clearance.
-/
public def square (base : Gaussian.Basic.Canonical) :
    Polynomial.Geometry.ClearPath Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial (ambient base) (ambient
      base).anchor (ambient base).anchor :=
  let box := ambient base
  let clearance := Clearance.Box.Boundary.Coordinate.coordinate_symmetric_boundaryClearance (radius_positive base)
  .cons (.horizontal _ _ _ le_rfl box.x_valid box.x_valid le_rfl (Clearance.Box.Boundary.Lines.bottomOfBoundary
    clearance))
    (.cons (.vertical _ _ _ le_rfl box.y_valid box.y_valid le_rfl (Clearance.Box.Boundary.Lines.rightOfBoundary
      clearance))
      (.cons (.horizontal _ _ _ box.x_valid le_rfl le_rfl box.x_valid (Clearance.Box.Boundary.Lines.topOfBoundary
        clearance))
        (.cons (.vertical _ _ _ box.y_valid le_rfl le_rfl box.y_valid (Clearance.Box.Boundary.Lines.leftOfBoundary
          clearance)) (.nil _))))

end

open Purelib.Data in
/-- Every retained reference-square segment stays inside its ambient square. -/
public theorem square_within (base : Gaussian.Basic.Canonical) : (square base).WithinAmbient :=
  .cons ⟨le_rfl, (ambient base).y_valid⟩ (.cons ⟨(ambient base).x_valid, le_rfl⟩
    (.cons ⟨(ambient base).y_valid, le_rfl⟩ (.cons ⟨le_rfl, (ambient base).x_valid⟩ (.nil _))))

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
/-- The reference square's raw coordinate winding is exactly four. -/
public theorem square_winding (base : Gaussian.Basic.Canonical) : Paths.PreparedPathWinding.ClearPath.rawWinding
  (square base) = 4 := by
  have equal : Paths.PreparedPathWinding.ClearPath.rawWinding (square base) = Winding.Box.Basic.quadrupledBoxWinding
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial (ambient base) := by
    unfold square
    simp only [Paths.PreparedPathWinding.ClearPath.rawWinding,
      Paths.PreparedPathWinding.ClearSegment.rawWinding_eq_coordinateWinding,
      Paths.PreparedPathWinding.ClearSegment.coordinateWinding]
    rw [Winding.Box.Basic.quadrupledBoxWinding_eq]
    ring1
  exact equal.trans (Winding.Box.Coordinate.coordinate_symmetric_normalization (radius_positive base)).1

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- Construct a finite winding-one coordinate reference at any nonzero Gaussian rational.

Append the retained axis connector, counterclockwise square and reversed connector, preserving all segment clearances
and the exact winding certificate. -/
def build (base : Gaussian.Basic.Canonical) (nonzero : base ≠ 0) : WindingOneLoop
  Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial base :=
  let stem := connector base nonzero
  { ambient := ambient base
    path := (stem.val.append (square base)).append (Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse
      stem.val)
    within := (stem.property.append (square_within base)).append
      (Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse_withinAmbient stem.val stem.property)
    winding := by
      rw [Paths.PreparedPathClosure.ClearPath.rawWinding_append, Paths.PreparedPathClosure.ClearPath.rawWinding_append,
        Paths.PreparedPathClosure.ClearPath.rawWinding_reverse, square_winding]
      omega }

end Purelib.Riemann.RootContinuation.CoordinateRootReference
