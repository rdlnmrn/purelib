module
public import Purelib.Geometry.Rational.Box.Sample
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Boundary

import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

section
@[expose] public section

/-!
# Choice-free degree-sharp maximality

The finite exact-isolation partition assigns every sufficiently refined
winding-one track to one displayed output cell.  Zero-winding remainder cells
cannot own such a track, and a raw-winding-four output cell cannot own two
separated tracks.  All searches below scan finite lists directly.
-/

namespace Purelib.Geometry.Rational.Box.Boundary.Interior

/-- Construct a point of the inner box on the outer boundary when the inner anchor lies inside but strict containment
fails.

Coordinate comparisons select the failing side and retain membership in both boxes; no point-selection principle is
needed. -/
theorem exists_boundary_point_of_anchor_mem_of_not_strictInterior
    {inner outer : Rational.Box} (anchorInside : outer.Contains inner.anchor)
    (notStrict : ¬inner.StrictInterior outer) :
    ∃ point : Data.Gaussian.Basic.Canonical,
      Boundary.OnBoxBoundary outer point ∧ inner.Contains point := by
  by_cases left : outer.xLower < inner.xLower
  · by_cases right : inner.xUpper < outer.xUpper
    · by_cases bottom : outer.yLower < inner.yLower
      · by_cases top : inner.yUpper < outer.yUpper
        · exact (notStrict ⟨left, right, bottom, top⟩).elim
        · let point : Data.Gaussian.Basic.Canonical := ⟨inner.xLower, outer.yUpper⟩
          refine ⟨point, ?_, ?_⟩
          · change Boundary.OnBoxBoundary outer
              ⟨inner.xLower, outer.yUpper⟩
            exact ⟨⟨anchorInside.1, anchorInside.2.1,
                outer.y_valid, le_rfl⟩,
              Or.inr (Or.inr (Or.inr rfl))⟩
          · change inner.Contains ⟨inner.xLower, outer.yUpper⟩
            exact ⟨le_rfl, inner.x_valid,
              anchorInside.2.2.2,
              le_of_not_gt top⟩
      · refine ⟨inner.anchor, ?_, inner.contains_anchor⟩
        have bottomEqual : inner.yLower = outer.yLower :=
          le_antisymm (le_of_not_gt bottom) anchorInside.2.2.1
        exact ⟨anchorInside,
          Or.inr (Or.inr (Or.inl bottomEqual))⟩
    · let point : Data.Gaussian.Basic.Canonical := ⟨outer.xUpper, inner.yLower⟩
      refine ⟨point, ?_, ?_⟩
      · change Boundary.OnBoxBoundary outer ⟨outer.xUpper, inner.yLower⟩
        exact ⟨⟨outer.x_valid, le_rfl,
            anchorInside.2.2.1, anchorInside.2.2.2⟩,
          Or.inr (Or.inl rfl)⟩
      · change inner.Contains ⟨outer.xUpper, inner.yLower⟩
        exact ⟨anchorInside.2.1,
          le_of_not_gt right, le_rfl, inner.y_valid⟩
  · refine ⟨inner.anchor, ?_, inner.contains_anchor⟩
    have leftEqual : inner.xLower = outer.xLower :=
      le_antisymm (le_of_not_gt left) anchorInside.1
    exact ⟨anchorInside, Or.inl leftEqual⟩
end Purelib.Geometry.Rational.Box.Boundary.Interior

end
