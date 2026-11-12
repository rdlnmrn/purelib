module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Queries
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Envelope
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Affine lineage of the same actual shifted acquisition

A fixed box containing the original parent endpoints contains all actual
acquired children. Their endpoints and retained covering-patch centers
therefore stay in that same box when those actual children become later
parents; the neighborhood enlargement is not iterated.
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
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)

/-- Every actual child fraction remains in any original fixed box containing the same physical parent endpoints. -/
theorem childPoint_inside_of_endpoints {box : Box}
    (startInside : box.Contains (startPoint parent).coordinate)
    (finishInside : box.Contains (finishPoint parent).coordinate)
    (index : Fin retained.parents.covered.parents.length)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) : box.Contains (child.edge.point input) := by
  have fractionInside := PreparedSheetContinuation.parameterAt_inside child.edge.left child.edge.request
    child.edge.ordered input inside
  have originalInside := retained.segment.pointAt_contains_of_endpoints startInside finishInside
    (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input) fractionInside
  have same := (retained.originalPoint_eq index child_eq input).trans (retained.point_eq _).symm
  exact Eq.mp (congrArg (fun point => box.Contains point) same.symm) originalInside

/-- Both actual acquired child endpoints remain in the same fixed original box, with their original order preserved.

These are the literal endpoints used by the next retained acquisition if
this actual child becomes its parent. No polynomial ambient, covering patch,
source owner, signed sheet or subdivision is rebuilt by the comparison.
-/
theorem childEndpoints_inside {box : Box}
    (startInside : box.Contains (startPoint parent).coordinate)
    (finishInside : box.Contains (finishPoint parent).coordinate)
    (index : Fin retained.parents.covered.parents.length)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt) :
    box.Contains (startPoint child).coordinate ∧ box.Contains (finishPoint child).coordinate := by
  have first := retained.childPoint_inside_of_endpoints startInside finishInside index child_eq 0
    ⟨Order.Basic.le_refl _, by decide +kernel⟩
  have last := retained.childPoint_inside_of_endpoints startInside finishInside index child_eq 1
    ⟨by decide +kernel, Order.Basic.le_refl _⟩
  exact ⟨Eq.mp (congrArg (fun point => box.Contains point) child.edge.point_zero) first,
    Eq.mp (congrArg (fun point => box.Contains point) child.edge.point_one) last⟩

/-- The same actual covering entry's center remains in the original fixed box at every model count. -/
theorem childCenter_inside_of_endpoints {box : Box}
    (startInside : box.Contains (startPoint parent).coordinate)
    (finishInside : box.Contains (finishPoint parent).coordinate)
    (index : Fin retained.parents.covered.parents.length) (modelCount : Nat) :
    box.Contains ((retained.parents.coveredParents.entry index).val.neighborhood modelCount).base.site.center := by
  have first := retained.childPoint_inside_of_endpoints startInside finishInside index rfl 0
    ⟨Order.Basic.le_refl _, by decide +kernel⟩
  exact Eq.mp (congrArg (fun point => box.Contains point)
    ((retained.parents.coveredParents.entry index).val.center_eq modelCount).symm) first

/-- An actual later acquired child has the ONE original-strip ceiling from its ancestral endpoint and parameter lineage.

The two endpoint memberships concern the original physical box, and the
parameter identity is the original affine-window index of this actual
acquisition. Its center is derived internally from the same retained child;
no enlarged box, new seed, H, query or signed relation is supplied.
-/
theorem child_rowCeiling_le_in_originalStrip
    {originalParameter direction : Canonical} {originalCount : Nat}
    (original : ContinuedNeighborhood (Paths.polynomial originalParameter) originalCount)
    (originalRange : Variation.Point.Range original)
    (originalAdmitted : Norm.Basic.normSq direction ≤ originalRange.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (parameterEq : parameter + increment = originalParameter + Scale.scale time direction)
    (firstInside : original.box.Contains (startPoint parent).coordinate)
    (lastInside : original.box.Contains (finishPoint parent).coordinate)
    (index : Fin retained.parents.covered.parents.length) (modelCount : Nat)
    (laterIncrement : Canonical) (order coordinate : Fin 2) :
    Variation.Point.Step.Joint.rowCeiling
        ((retained.parents.coveredParents.entry index).val.neighborhood modelCount)
        laterIncrement order coordinate ≤ Variation.Point.Step.Joint.shiftedEnvelopeCeiling original :=
  originalRange.rowCeiling_le_at_parameter originalAdmitted time timeInside
    ((retained.parents.coveredParents.entry index).val.neighborhood modelCount) parameterEq
    (retained.childCenter_inside_of_endpoints firstInside lastInside index modelCount)
    laterIncrement order coordinate

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
