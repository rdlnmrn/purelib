module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Clear paths inside a regular rectangle

Full-box clearance supplies every horizontal and vertical line used here.
The connector stays in that same box, including when an endpoint is on its
boundary. Its two legs copy the existing clearance bound. A stationary
query has no segments, so transporting it can reuse its original owner.
-/

namespace Purelib.Riemann.Paths.ClearBoxPaths

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {box :
  Purelib.Geometry.Rational.Box}

section
open Purelib.Data
open Purelib.Polynomial
/-- Restrict a full-box clearance to a horizontal line at a retained in-box height. -/
def horizontal (clearance : Clearance.Box.Region.RegionClearance polynomial box)
    (y : Rat.Fraction.Rational) (inside : box.yLower ≤ y ∧ y ≤ box.yUpper) :
    Clearance.Box.Line.Basic.HorizontalLineClearance polynomial box y :=
  ⟨clearance.bound, clearance.positive, fun _ lower upper =>
    by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      clearance.lower (Gaussian.Components.Basic.point _ y) ⟨lower, upper, inside.1, inside.2⟩⟩

/-- Restrict a full-box clearance to a vertical line at a retained in-box coordinate. -/
def vertical (clearance : Clearance.Box.Region.RegionClearance polynomial box)
    (x : Rat.Fraction.Rational) (inside : box.xLower ≤ x ∧ x ≤ box.xUpper) :
    Clearance.Box.Line.Basic.VerticalLineClearance polynomial box x :=
  ⟨clearance.bound, clearance.positive, fun _ lower upper =>
    by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      clearance.lower (Gaussian.Components.Basic.point x _) ⟨inside.1, inside.2, lower, upper⟩⟩

end

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
set_option genInjectivity false in
/-- A clear axis-aligned connector within the retained rectangle using at most two segments. -/
structure Route (polynomial : Geometry.ClearPath.GaussianPolynomial) (box : Rational.Box) (start finish
  : Gaussian.Basic.Canonical) where
  /-- The retained clear path joining the displayed endpoints. -/ path : Polynomial.Geometry.ClearPath polynomial box
    start finish
  /-- Every segment of the path remains in the same cleared ambient box. -/ within : path.WithinAmbient
  /-- The retained connector has at most two segments. -/ short : path.segmentCount ≤ 2

constructive_injectivity Route

namespace Route

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
/-- Construct an in-box clear connector with no redundant stationary legs.

Coincident endpoints give the empty path; equal coordinates give one segment; otherwise a horizontal leg followed by a
vertical leg uses the original box clearance. -/
def build (clearance : Clearance.Box.Region.RegionClearance polynomial box)
    (start finish : Gaussian.Basic.Canonical) (first : box.Contains start) (last : box.Contains finish) :
    Route polynomial box start finish :=
  if equal : start = finish then
    equal ▸ ⟨.nil start, .nil start, by change 0 ≤ 2; decide⟩
  else
    let left : Geometry.ClearPath.ClearSegment polynomial box start (Gaussian.Components.Basic.point finish.re start.im)
      :=
      .horizontal start.re finish.re start.im first.1 first.2.1 last.1 last.2.1
        (Paths.ClearBoxPaths.horizontal clearance start.im first.2.2)
    let right : Geometry.ClearPath.ClearSegment polynomial box (Gaussian.Components.Basic.point finish.re start.im)
      finish :=
      .vertical finish.re start.im finish.im first.2.2.1 first.2.2.2 last.2.2.1 last.2.2.2
        (Paths.ClearBoxPaths.vertical clearance finish.re ⟨last.1, last.2.1⟩)
    if sameHeight : start.im = finish.im then
      let equal : Gaussian.Components.Basic.point finish.re start.im = finish := Gaussian.Basic.ext rfl sameHeight
      ⟨.cons (left.castFinish equal) (.nil finish),
        .cons (left.castFinish_withinAmbient first.2.2 equal) (.nil finish), by change 1 ≤ 2; decide⟩
    else if sameWidth : start.re = finish.re then
      let equal : Gaussian.Components.Basic.point finish.re start.im = start := Gaussian.Basic.ext sameWidth.symm rfl
      ⟨.cons (right.castStart equal) (.nil finish),
        .cons (right.castStart_withinAmbient ⟨last.1, last.2.1⟩ equal) (.nil finish), by change 1 ≤ 2; decide⟩
    else
      ⟨.cons left (.cons right (.nil finish)),
        .cons first.2.2 (.cons ⟨last.1, last.2.1⟩ (.nil finish)), by change 2 ≤ 2; exact le_rfl⟩

open Purelib.Data in
open Purelib.Polynomial in
/-- Connecting a point to itself constructs the empty clear path. -/
theorem build_self (clearance : Clearance.Box.Region.RegionClearance polynomial box)
    (point : Gaussian.Basic.Canonical) (inside : box.Contains point) :
    (build clearance point point inside inside).path = .nil point := by
  unfold build
  rw [dif_pos rfl]

end Route

end Purelib.Riemann.Paths.ClearBoxPaths
