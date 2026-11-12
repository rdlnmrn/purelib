module

import Purelib.Geometry.Rational.Box.Separation.Family

/-!
# Retained quantitative box-family separation

The original first positive coordinate gap is stored once. Its squared
minimum controls every pair of points retained in the original two boxes,
while an empty original family retains the initial bound one.
-/

namespace TestPurelib.Geometry.Rational.Box.Separation

open Purelib
open Geometry.Rational
open Data.Gaussian.Basic (Canonical)

/-- The first original unit-width box. -/
private def left : Box := ⟨-1, 0, 0, 1, by decide, by decide⟩

/-- The second original box has a positive real-coordinate gap of one half. -/
private def right : Box := ⟨1 / 2, 1, 0, 1, by decide, by decide⟩

/-- The original two displayed boxes are separated in their actual order. -/
private theorem pairwise : [left, right].Pairwise Box.Separated := by
  apply List.Pairwise.cons
  · intro box member
    cases member with
    | head => exact Or.inl (by decide +kernel)
    | tail _ impossible => nomatch impossible
  · exact List.Pairwise.cons (fun _ impossible => nomatch impossible) List.Pairwise.nil

/-- The common floor is the square of the retained half-unit original gap. -/
private theorem original_floor : (Box.Separation.Family.prepare [left, right] pairwise).bound = 1 / 4 := by
  decide +kernel

/-- The original family gap controls every displayed point pair in its same two boxes. -/
private theorem all_contained_points (points : Fin [left, right].length → Canonical)
    (inside : ∀ index, ([left, right].get index).Contains (points index)) :
    (List.ofFn points).Pairwise (fun first second =>
      (Box.Separation.Family.prepare [left, right] pairwise).bound ≤
        Data.Gaussian.Norm.Basic.normSq (first - second)) :=
  (Box.Separation.Family.prepare [left, right] pairwise).points_separated points inside

/-- The empty original family needs no artificial separation witness or gap search. -/
private theorem empty_floor : (Box.Separation.Family.prepare [] List.Pairwise.nil).bound = 1 := by decide +kernel

end TestPurelib.Geometry.Rational.Box.Separation
