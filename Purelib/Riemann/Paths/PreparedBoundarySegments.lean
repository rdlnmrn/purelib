module

import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

public section

/-!
# Boundary membership inherited by actual prepared refinements

Two endpoints on the same rectangle side put the entire affine parent on
that side. The retained root-child locations then put every actual child
start on the boundary, without individual coordinate checks or new searches.
-/

namespace Purelib.Riemann.Paths.PreparedBoundarySegments

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectParentBlock)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Geometry.Rational.Box.Boundary (OnBoxBoundary)

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The exact rational Gaussian carrier. -/
abbrev Gaussian := Basic.Canonical
/-- The original rational Gaussian box carrier. -/
abbrev Box := Purelib.Geometry.Rational.Box

/-- Both original endpoints share one selected coordinate boundary of the retained box.

This condition records a common lower or upper real or imaginary coordinate; containment is supplied separately where
required. -/
@[expose] def SameSide (box : Box) (first last : Gaussian) : Prop :=
  (first.re = box.xLower ∧ last.re = box.xLower) ∨
  (first.re = box.xUpper ∧ last.re = box.xUpper) ∨
  (first.im = box.yLower ∧ last.im = box.yLower) ∨
  (first.im = box.yUpper ∧ last.im = box.yUpper)

/-- Decide whether the original endpoints share a coordinate side of the retained rational box. -/
instance sameSideDecidable (box : Box) (first last : Gaussian) : Decidable (SameSide box first last) := by
  unfold SameSide
  infer_instance

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- An original centered parent edge whose endpoints lie in the retained box on the same side.

The two containment proofs and exact coordinate-side condition preserve the original parent geometry. -/
structure ParentOnBoundary (parent : CenteredEdge curve differential) (box : Box) where
  /-- The exact original parent start point belongs to the retained box. -/ startInside : box.Contains
    (parent.edge.point 0)
  /-- The exact original parent finish point belongs to the retained box. -/ finishInside : box.Contains
    (parent.edge.point 1)
  /-- The original parent endpoints share a retained coordinate side. -/ side : SameSide box (parent.edge.point 0)
    (parent.edge.point 1)

section
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- An original segment with equal endpoint real coordinates has that real coordinate at every parameter. -/
private theorem segment_re_eq {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start
      finish)
    {coordinate : Coordinate} (first : start.re = coordinate) (last : finish.re = coordinate) (fraction : Coordinate) :
    (segment.pointAt fraction).re = coordinate := by
  simp only [Geometry.ClearPath.ClearSegment.pointAt, Basic.add_re, Basic.sub_re, Scale.scale_re, first, last]
  ring1

/-- An original segment with equal endpoint imaginary coordinates has that imaginary coordinate at every parameter. -/
private theorem segment_im_eq {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start
      finish)
    {coordinate : Coordinate} (first : start.im = coordinate) (last : finish.im = coordinate) (fraction : Coordinate) :
    (segment.pointAt fraction).im = coordinate := by
  simp only [Geometry.ClearPath.ClearSegment.pointAt, Basic.add_im, Basic.sub_im, Scale.scale_im, first, last]
  ring1

end

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Any two parameters of the original same-side segment remain on that exact coordinate side. -/
theorem SameSide.pointAt {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient box : Box} {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start
      finish)
    (side : SameSide box start finish) (left right : Coordinate) :
    SameSide box (segment.pointAt left) (segment.pointAt right) := by
  rcases side with side | side | side | side
  · exact Or.inl ⟨segment_re_eq segment side.1 side.2 left, segment_re_eq segment side.1 side.2 right⟩
  · exact Or.inr (Or.inl ⟨segment_re_eq segment side.1 side.2 left, segment_re_eq segment side.1 side.2 right⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨segment_im_eq segment side.1 side.2 left, segment_im_eq segment side.1 side.2 right⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨segment_im_eq segment side.1 side.2 left, segment_im_eq segment side.1 side.2 right⟩))

section
open Purelib.Polynomial
/-- The original centered parent's real coordinate remains constant when its endpoint real coordinates agree. -/
private theorem point_re_eq (parent : CenteredEdge curve differential) {coordinate : Coordinate}
    (first : (parent.edge.point 0).re = coordinate) (last : (parent.edge.point 1).re = coordinate)
    (fraction : Coordinate) : (parent.edge.point fraction).re = coordinate := by
  change (parent.edge.localSegment.pointAt 0).re = coordinate at first
  change (parent.edge.localSegment.pointAt 1).re = coordinate at last
  rw [Geometry.ClearPath.ClearSegment.pointAt_zero] at first
  rw [Geometry.ClearPath.ClearSegment.pointAt_one] at last
  change (parent.edge.localSegment.pointAt fraction).re = coordinate
  exact segment_re_eq parent.edge.localSegment first last fraction

/-- The original centered parent's imaginary coordinate remains constant when its endpoint imaginary coordinates agree.
-/
private theorem point_im_eq (parent : CenteredEdge curve differential) {coordinate : Coordinate}
    (first : (parent.edge.point 0).im = coordinate) (last : (parent.edge.point 1).im = coordinate)
    (fraction : Coordinate) : (parent.edge.point fraction).im = coordinate := by
  change (parent.edge.localSegment.pointAt 0).im = coordinate at first
  change (parent.edge.localSegment.pointAt 1).im = coordinate at last
  rw [Geometry.ClearPath.ClearSegment.pointAt_zero] at first
  rw [Geometry.ClearPath.ClearSegment.pointAt_one] at last
  change (parent.edge.localSegment.pointAt fraction).im = coordinate
  exact segment_im_eq parent.edge.localSegment first last fraction

end

section
open Purelib.Geometry.Rational
/-- Every unit-interval parameter of the original retained same-side parent lies on the box boundary. -/
theorem ParentOnBoundary.point {parent : CenteredEdge curve differential} {box : Box}
    (boundary : ParentOnBoundary parent box) {fraction : Coordinate} (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    Box.Boundary.OnBoxBoundary box (parent.edge.point fraction) := by
  refine ⟨PreparedPrimitivePaths.point_inside_of_endpoints parent box boundary.startInside boundary.finishInside inside,
    ?_⟩
  rcases boundary.side with side | side | side | side
  · exact Or.inl (point_re_eq parent side.1 side.2 fraction)
  · exact Or.inr (Or.inl (point_re_eq parent side.1 side.2 fraction))
  · exact Or.inr (Or.inr (Or.inl (point_im_eq parent side.1 side.2 fraction)))
  · exact Or.inr (Or.inr (Or.inr (point_im_eq parent side.1 side.2 fraction)))

/-- Every original direct-refinement child starts on the retained parent boundary.

Each stored root-child comparison retains its parent fraction and unit-interval
bounds. The parent boundary certificate places that exact child start on the box. -/
theorem ParentOnBoundary.child_starts {parent : CenteredEdge curve differential} {box : Box}
    (boundary : ParentOnBoundary parent box) (block : DirectParentBlock parent) :
    ∀ child ∈ block.children, Box.Boundary.OnBoxBoundary box (child.edge.point 0) := by
  have roots := block.roots
  generalize block.children = children at roots ⊢
  induction roots with
  | nil => intro child member; cases member
  | cons head tail ih =>
      intro child member
      rcases Membership.mem_cons.mp member with rfl | member
      · rw [← head.point_eq]
        exact boundary.point head.inside
      · exact ih child member

end

open Purelib.Riemann.Integration in
/-- The original boundary parent's geometric movement is at most the retained box squared diameter. -/
theorem ParentOnBoundary.movement_le {parent : CenteredEdge curve differential} {box : Box}
    (boundary : ParentOnBoundary parent box) :
    PreparedDirectDyadicRefinements.geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter ≤ box.diagonalSq := by
  have bounded := box.normSq_sub_le_diagonalSq boundary.finishInside boundary.startInside
  rw [parent.edge.point_one, parent.edge.point_zero] at bounded
  exact bounded

end Purelib.Riemann.Paths.PreparedBoundarySegments
