module

public import Purelib.Polynomial.Clearance.Box.Region.Basic
public import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Exact.Extraction
import Purelib.RootIsolation.State.WindingOne.Count
import Purelib.Data.Int.Order

/-! # Finite winding counts for positive clear regions -/

public section

namespace Purelib.Polynomial.Winding.Box.Region

open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Box.Region (ClearRegion)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

/-- A clear region containing a positive-winding clear subregion has winding at least one.

Finite extraction supplies a winding-one state strictly inside the original
subregion. The existing eliminant-safe counting theorem compares that actual
extracted state with the surrounding original clear region.
-/
theorem winding_ge_four_of_positive_region {p : CoefficientPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input p) (outer inner : ClearRegion p ambient)
    (positive : 0 < Winding.Box.Basic.quadrupledBoxWinding p inner.box)
    (nested : inner.box.Refines outer.box) :
    4 ≤ Winding.Box.Basic.quadrupledBoxWinding p outer.box := by
  let extracted := Exact.Extraction.extractRegion input.degreeAtLeastTwo input.squarefree
    input.elimination inner positive
  exact State.WindingOne.Count.region_rawWinding_ge_four_of_strictInterior
    input.degreeAtLeastTwo input.squarefree input.elimination extracted.track.initial outer
    (Box.Refinement.StrictInterior.Boxes.trans_refines extracted.centerStrict nested)

/-- Two separated positive-winding clear subregions contribute winding at least two to their surrounding clear region.

Each original subregion supplies its own finite extracted winding-one state.
Strict extraction preserves their separation and gives the actual states used
by the existing finite two-state count; no full ambient-line certificates are
assumed for the original subregions.
-/
theorem winding_ge_eight_of_separated_positive_regions {p : CoefficientPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input p) (outer left right : ClearRegion p ambient)
    (leftPositive : 0 < Winding.Box.Basic.quadrupledBoxWinding p left.box)
    (rightPositive : 0 < Winding.Box.Basic.quadrupledBoxWinding p right.box)
    (leftNested : left.box.Refines outer.box) (rightNested : right.box.Refines outer.box)
    (separated : left.box.Separated right.box) :
    8 ≤ Winding.Box.Basic.quadrupledBoxWinding p outer.box := by
  let first := Exact.Extraction.extractRegion input.degreeAtLeastTwo input.squarefree
    input.elimination left leftPositive
  let second := Exact.Extraction.extractRegion input.degreeAtLeastTwo input.squarefree
    input.elimination right rightPositive
  have firstStrict := Box.Refinement.StrictInterior.Boxes.trans_refines first.centerStrict leftNested
  have secondStrict := Box.Refinement.StrictInterior.Boxes.trans_refines second.centerStrict rightNested
  have smallerSeparated := separated.of_refines (Box.Refinement.StrictInterior.refines first.centerStrict)
    (Box.Refinement.StrictInterior.refines second.centerStrict)
  exact State.WindingOne.Count.region_rawWinding_ge_eight_of_separated input.degreeAtLeastTwo
    input.squarefree input.elimination outer first.track.initial second.track.initial
    firstStrict secondStrict smallerSeparated

/-- Positive-winding clear subregions of a winding-one clear region cannot be separated.

The original containing region has winding exactly one. Finite extraction and
counting would make two separated positive subregions contribute winding at
least two, contradicting that same region's original winding certificate.
-/
theorem not_separated_in_winding_one_region {p : CoefficientPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input p) (outer left right : ClearRegion p ambient)
    (one : Winding.Box.Basic.quadrupledBoxWinding p outer.box = 4)
    (leftPositive : 0 < Winding.Box.Basic.quadrupledBoxWinding p left.box)
    (rightPositive : 0 < Winding.Box.Basic.quadrupledBoxWinding p right.box)
    (leftNested : left.box.Refines outer.box) (rightNested : right.box.Refines outer.box) :
    ¬ left.box.Separated right.box := by
  intro separated
  have count := winding_ge_eight_of_separated_positive_regions input outer left right
    leftPositive rightPositive leftNested rightNested separated
  rewrite [one] at count
  exact (by decide : ¬ (8 : Int) ≤ 4) count

end Purelib.Polynomial.Winding.Box.Region

end
