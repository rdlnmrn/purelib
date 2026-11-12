module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Envelope
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Envelope
import Purelib.Data.List.DependentProduct

/-! # A fixed original-strip ceiling on actual ancestral source families

The original range allocation and retained source caches compute the scale.
A stored ancestral endpoint product, constructed by the original identity
and occurrence-map operations, locates every actual later covering patch in
its SAME original physical box. The actual affine parameter index pays its
original all-point polynomial floor at every stage before the fine mesh.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step (Joint)

/-- Every actual descendant source patch has the same original-family ceiling throughout one paid affine strip.

The original source product remains the numerical owner of the computed
maximum. The later cover remains the owner of each actual seed/rootLower.
Only stored ancestor indices, endpoint memberships and the actual affine
parameter identity link them; no H, sample error, root equivalence, period
equality or geometric Completion is assumed or inferred.
-/
theorem rowCeiling_le_in_originalStrip
    {originalParameter actualParameter direction : Canonical}
    {originalFrame : Paths.Frame originalParameter} {frame : Paths.Frame actualParameter}
    {basis : Differential 1} {originalCount count : Nat}
    {originalParents : List (CenteredEdge (Fibre.frameCurve originalFrame) basis)}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {originalCovered : CoveredParents originalCount originalParents} {covered : CoveredParents count parents}
    {originalStart originalFinish : LiftedPoint 2}
    {originalPath : LiftedPath 2 originalStart originalFinish} {originalStage originalFloor : Nat}
    {originalTargets : CellEndpoints.Targets originalPath originalStage}
    (original : PreparedParents originalCovered originalFloor originalTargets)
    (ranges : ParameterRange originalCovered) (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (parameterEq : actualParameter = originalParameter + Scale.scale time direction)
    (lineage : DependentProduct parents (fun index =>
      { ancestor : Fin originalParents.length //
        ((originalCovered.entry ancestor).val.neighborhood originalCount).box.Contains
            (PreparedParent.startPoint (parents[index.val]'index.isLt)).coordinate ∧
          ((originalCovered.entry ancestor).val.neighborhood originalCount).box.Contains
            (PreparedParent.finishPoint (parents[index.val]'index.isLt)).coordinate }))
    (index : Fin parents.length) (laterIncrement : Canonical) (order coordinate : Fin 2) :
    Joint.rowCeiling (parameter := actualParameter) ((covered.entry index).val.neighborhood count)
        laterIncrement order coordinate ≤ original.envelopeCeiling := by
  let ancestor := DependentProduct.get parents lineage index
  let originalPatch := (originalCovered.entry ancestor.val).val.neighborhood originalCount
  let actual := (covered.entry index).val.neighborhood count
  have centerEq : actual.base.site.center =
      (PreparedParent.startPoint (parents[index.val]'index.isLt)).coordinate :=
    ((covered.entry index).val.center_eq count).trans (parents[index.val]'index.isLt).edge.point_zero
  have inside : originalPatch.box.Contains actual.base.site.center :=
    Eq.mp (congrArg (fun point => originalPatch.box.Contains point) centerEq.symm) ancestor.property.1
  have paid := admitted.trans (allocation.bound_le_entry ancestor.val)
  have bounded := (ranges.entry ancestor.val).rowCeiling_le_at_parameter
    paid time timeInside actual parameterEq inside laterIncrement order coordinate
  exact bounded.trans (original.entry_envelopeCeiling_le ancestor.val)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
