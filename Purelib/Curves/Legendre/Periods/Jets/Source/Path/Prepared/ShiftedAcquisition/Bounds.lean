module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Queries
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Bounds
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Fixed physical-box bounds for the actual shifted acquisition

The same materialized Parents and its original covering-patch entries
supply every child. Actual affine parameter incidence puts each center in
the original physical box. Its retained shifted clearance then bounds the
actual seed-derived rootLower before fine requests or observation stages.
Every actual neighborhood refines the single original-box-plus-one envelope.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)

/-- Every actual located child fraction remains in the original fixed physical box.

The original request's parameterAt lies in the unit interval. The retained
segment's all-point ambient containment and exact point_eq identify this
same child point, without a second subdivision, query or acquisition.
-/
theorem childPoint_inside (index : Fin retained.parents.covered.parents.length)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) :
    (patch.neighborhood count).box.Contains (child.edge.point input) := by
  have fractionInside := PreparedSheetContinuation.parameterAt_inside child.edge.left child.edge.request
    child.edge.ordered input inside
  have originalInside := retained.segment.pointAt_contains retained.within
    (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input) fractionInside
  have pointEq := (retained.originalPoint_eq index child_eq input).trans (retained.point_eq _).symm
  exact Eq.mp (congrArg (fun point => (patch.neighborhood count).box.Contains point) pointEq.symm) originalInside

/-- The actual covering-patch center at every child occurrence lies in the same original physical box.

The existing CoveredParents.entry reads the retained patch at that exact
ordered occurrence. Its original center_eq identifies the actual child
start at every coefficient count, independently of fine query stages.
-/
theorem childCenter_inside (index : Fin retained.parents.covered.parents.length) (modelCount : Nat) :
    (patch.neighborhood count).box.Contains
      ((retained.parents.coveredParents.entry index).val.neighborhood modelCount).base.site.center := by
  have childInside := retained.childPoint_inside index rfl 0
    ⟨Order.Basic.le_refl _, by decide +kernel⟩
  have centerEq := (retained.parents.coveredParents.entry index).val.center_eq modelCount
  exact Eq.mp (congrArg (fun point => (patch.neighborhood count).box.Contains point) centerEq.symm) childInside

/-- The same original shifted-clearance floor bounds each actual retained child's seed-derived rootLower.

The fixed positive floor comes from the original Range and physical box.
The actual child's own Seed.residual_small pays the seed norm. Neither a
mesh-dependent minimum nor a signed comparison between independent owners
is used to derive this quantitative bound.
-/
theorem child_rootLower_ge (index : Fin retained.parents.covered.parents.length) (modelCount : Nat) :
    (1 / 4 : Rational) /
        (2 + 3 / (((patch.neighborhood count).base.site.denominatorValue / 4) / 4)) ≤
      ((retained.parents.coveredParents.entry index).val.neighborhood modelCount).rootLower := by
  let actual := (retained.parents.coveredParents.entry index).val.neighborhood modelCount
  have floorPositive : 0 < ((patch.neighborhood count).base.site.denominatorValue / 4) / 4 :=
    Order.Field.div_pos_direct
      (Order.Field.div_pos_direct (patch.neighborhood count).base.site.denominatorValue_positive
        (by decide +kernel : (0 : Rational) < 4))
      (by decide +kernel : (0 : Rational) < 4)
  have lower := range.shifted_lower (retained.childCenter_inside index modelCount) increment admitted
  rewrite [Norm.Basic.normSq_eq_canonical] at lower
  exact actual.rootLower_ge floorPositive lower

/-- Every actual child neighborhood refines the single original physical box enlarged by one coordinate unit.

The exact retained patch center is in the original physical box. The
original neighborhood constructor's radius is at most one, including its
accepted or rejected grow branch. No successive box enlargement or
refinement to the original seed-owner box is assumed.
-/
theorem child_box_refines_enlarge (index : Fin retained.parents.covered.parents.length) (modelCount : Nat) :
    ((retained.parents.coveredParents.entry index).val.neighborhood modelCount).box.Refines
      ((patch.neighborhood count).box.enlarge 1 (by decide +kernel)) :=
  ((retained.parents.coveredParents.entry index).val.neighborhood modelCount).box_refines_enlarge
    (retained.childCenter_inside index modelCount)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
