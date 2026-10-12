module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Bisection
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Leaf
public import Purelib.Polynomial.Clearance.Pair.Cover.Prepare
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Clearance.Pair.Enclosure
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
Finite coordinate-clearance covers for the actual affine segment polynomial.
The cached cover supplies a root-sample norm bound of linear magnitude;
its finite unresolved cases retain the original positive segment floor.
The imports use finite Horner, interval and quadratic identities only.
-/

namespace Purelib.Riemann.Paths

open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)

namespace PreparedTraceClearance

open Purelib.Data.Rat in
/-- The exact closed rational unit interval used for the original trace parameterization. -/
def traceParameters : Data.Rat.Interval.Bounds := ⟨0, 1, by decide⟩

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Refine the original polynomial-pair clearance leaf by bounded interval bisection, retaining completed leaf
certificates.

Depth zero or a sufficiently small coordinate enclosure returns the original leaf. Otherwise both exact interval halves
are prepared recursively and combined with the retained parent's lower bounds and split cover. -/
def refineTraceClearance
    {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial}
    {source : Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial}
    {parameters : Data.Rat.Interval.Bounds}
    (leaf : Polynomial.Clearance.Pair.Cover.Leaf source parameters) :
    Nat → Clearance.Pair.Cover.Prepare.Prepared source parameters
  | 0 => .ofLeaf leaf
  | depth + 1 =>
      let upper := max
        (max (Fraction.abs leaf.enclosures.realRange.lower) (Fraction.abs leaf.enclosures.realRange.upper))
        (max (Fraction.abs leaf.enclosures.imagRange.lower) (Fraction.abs leaf.enclosures.imagRange.upper))
      if upper ≤ 2 * leaf.coordinateFloor then .ofLeaf leaf
      else
        let left := refineTraceClearance
          (Polynomial.Clearance.Pair.Cover.Leaf.prepare source
            (Interval.Bisection.leftHalf parameters)) depth
        let right := refineTraceClearance
          (Polynomial.Clearance.Pair.Cover.Leaf.prepare source
            (Interval.Bisection.rightHalf parameters)) depth
        ⟨max leaf.normFloor (min left.normFloor right.normFloor),
          max leaf.coordinateFloor (min left.coordinateFloor right.coordinateFloor),
          .split leaf left.cover right.cover⟩

end PreparedTraceClearance

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- Cached clearance data for the polynomial restricted to an original cleared segment.

Exact equations retain the composed polynomial, prepared real/imaginary source, initial unit-interval leaf and the
depth-eight refined cover; these remain the original executable constructions. -/
structure PreparedTraceClearance {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}
    {start finish : Basic.Canonical} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) where
  /-- The cached original polynomial composed with the exact retained segment parameterization. -/ composed :
    Geometry.ClearPath.GaussianPolynomial
  /-- The cache equals the original segment polynomial construction. -/ composed_eq : composed =
    ClearSheetContinuation.segmentPolynomial segment
  /-- The retained clearance source for the exact cached real and imaginary polynomials. -/ source :
    Clearance.Pair.Cover.Leaf.Source
    (Components.realPart composed) (Components.imagPart composed)
  /-- The source equals the exact original preparation of those cached component polynomials. -/ source_eq : source =
    Clearance.Pair.Cover.Leaf.Source.prepare
    (Components.realPart composed) (Components.imagPart composed)
  /-- The retained original clearance leaf on the exact unit trace interval. -/ initial :
    Polynomial.Clearance.Pair.Cover.Leaf
    source _root_.Purelib.Riemann.Paths.PreparedTraceClearance.traceParameters
  /-- The leaf equals the exact original source preparation on the retained trace interval. -/ initial_eq : initial =
    Polynomial.Clearance.Pair.Cover.Leaf.prepare source
      _root_.Purelib.Riemann.Paths.PreparedTraceClearance.traceParameters
  /-- The cached refined clearance cover for the exact original source and trace interval. -/ cover :
    Clearance.Pair.Cover.Prepare.Prepared source _root_.Purelib.Riemann.Paths.PreparedTraceClearance.traceParameters
  /-- The cover equals the original initial leaf refined through the fixed depth-eight procedure. -/ cover_eq : cover =
    _root_.Purelib.Riemann.Paths.PreparedTraceClearance.refineTraceClearance initial 8

constructive_injectivity PreparedTraceClearance

namespace PreparedTraceClearance

variable {polynomial : GaussianPolynomial} {ambient :
  Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment polynomial ambient start finish}

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- Cache the exact segment polynomial, component source, initial leaf and depth-eight refined clearance cover. -/
def build (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : PreparedTraceClearance segment
  :=
  let composed := ClearSheetContinuation.segmentPolynomial segment
  let source := Clearance.Pair.Cover.Leaf.Source.prepare
    (Components.realPart composed) (Components.imagPart composed)
  let initial := Polynomial.Clearance.Pair.Cover.Leaf.prepare source traceParameters
  { composed, composed_eq := rfl
    source, source_eq := rfl
    initial, initial_eq := rfl
    cover := refineTraceClearance initial 8
    cover_eq := rfl }

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- The retained cover's coordinate floor bounds the maximum absolute coordinate of the original polynomial along the
segment.

The exact composed-polynomial equation identifies each retained unit-interval evaluation with the original segment
point, preserving the cached cover witness. -/
theorem coordinate_le (clearance : PreparedTraceClearance segment) (parameter : Fraction.Rational)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    clearance.cover.coordinateFloor ≤
      max (Fraction.abs (polynomial.eval (segment.pointAt parameter)).re)
        (Fraction.abs (polynomial.eval (segment.pointAt parameter)).im) := by
  have bound := clearance.cover.cover.coordinate_le (parameter := parameter) inside
  have evaluated : clearance.composed.eval (Cast.Path.ofCoordinate parameter) =
      polynomial.eval (segment.pointAt parameter) :=
    (congrArg (fun p : Geometry.ClearPath.GaussianPolynomial => p.eval (Cast.Path.ofCoordinate parameter))
      clearance.composed_eq).trans
        (ClearSheetContinuation.segmentPolynomial_eval segment parameter)
  rw [Components.eval_realPart, Components.eval_imagPart, evaluated] at bound
  exact bound

end PreparedTraceClearance

end Purelib.Riemann.Paths
