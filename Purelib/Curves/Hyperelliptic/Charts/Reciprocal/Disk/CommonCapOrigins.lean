module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Tactic.Ring
import Purelib.Data.List.Map
open Purelib.Data.List

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins.ReciprocalDiskArcOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.PairedIncrementArea

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Cap-origin accounting uses the common sheet bit of the two actual
recast-root alignments. Bilinear area is invariant under their joint sign. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover CommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest (Entry Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation (SourcePath)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment (RegularAlignment)
open Purelib.Integration.Path.PairedIncrementArea (Summary)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon (dyadicArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins.Bilinear (dyadicArea_sub_origin
  dyadicEdges_sum_area)
variable {genus count otherCount : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : Cover data} {secondCover :
    Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    CommonCover firstCover secondCover}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum stage depth : Nat} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {source : SourcePrimitive data stage}
    {otherSource : SourcePrimitive otherData
    stage}
  {request : CommonRibbonRequest regular common
    target minimum}

/-- The two retained differential-recast alignments select the same actual cap sheet sign after stage two. -/
theorem Entry.same_sign (entry : CommonRibbonRequest.Entry request sample otherSample source otherSource depth) (later :
  2 ≤ stage) :
    entry.left.first.flip = entry.right.first.flip := by
  let first := ArcOwners.Point.build cap (RootModel.build entry.plan.interval.first.cell)
    entry.plan.interval.edge.left.parameter
    ⟨entry.plan.interval.first.lower, entry.plan.interval.ordered.trans entry.plan.interval.first.upper⟩
  let second := ArcOwners.Point.build cap (RootModel.build entry.plan.interval.second.cell)
    entry.plan.interval.edge.left.parameter
    ⟨entry.plan.interval.second.lower, entry.plan.interval.ordered.trans entry.plan.interval.second.upper⟩
  exact Join.paired_same_sign
    (Join.ofRecast first second)
    entry.left entry.right later

/-- Read both retained cap primitive samples at the inverse of the original source point. -/
def capValues (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox) (parameter : InverseRootPolynomial.Coordinate) :
      PrimitivePoint :=
  ⟨sample.primitive.value.eval (parent.edge.point parameter)⁻¹,
    otherSample.primitive.value.eval (parent.edge.point parameter)⁻¹⟩

/-- The two exact retained cap primitive values at their respective original parent origins. -/
def Entry.capOrigin (entry : CommonRibbonRequest.Entry request sample otherSample source otherSource depth) :
  PrimitivePoint :=
  ⟨sample.primitive.value.eval (parent.edge.point entry.plan.interval.first.owner.left.parameter)⁻¹,
    otherSample.primitive.value.eval (parent.edge.point entry.plan.interval.second.owner.left.parameter)⁻¹⟩

/-- The exact bilinear origin correction for the actual common-cover interval. -/
def Entry.capOriginTerm (entry : CommonRibbonRequest.Entry request sample otherSample source otherSource depth) :
  Data.Gaussian.Basic.Canonical :=
  Stokes.edgeArea entry.capOrigin
    ((capValues (parent := parent)
    sample otherSample entry.plan.interval.edge.right.parameter).sub
    (capValues (parent := parent)
      sample otherSample entry.plan.interval.edge.left.parameter))

/-- Negating both primitive coordinates preserves their complete finite dyadic bilinear area. -/
theorem dyadicArea_joint_neg (values : InverseRootPolynomial.Coordinate → Stokes.PrimitivePoint) (depth : Nat) (first
  last : InverseRootPolynomial.Coordinate) :
    DyadicBilinearBoundaryRibbon.dyadicArea (fun parameter => ⟨-(values parameter).left, -(values parameter).right⟩)
      depth first last =
      DyadicBilinearBoundaryRibbon.dyadicArea values depth first last := by
  induction depth generalizing first last with
  | zero =>
    rw [DyadicBilinearBoundaryRibbon.dyadicArea_zero, DyadicBilinearBoundaryRibbon.dyadicArea_zero];
    unfold Stokes.edgeArea; ring1
  | succ depth ih =>
    rw [DyadicBilinearBoundaryRibbon.dyadicArea_succ, DyadicBilinearBoundaryRibbon.dyadicArea_succ, ih, ih]

/-- The retained cap area equals the unsigned paired cap area after subtracting the exact retained origin. -/
theorem Entry.cap_area_unsigned (entry : CommonRibbonRequest.Entry request sample otherSample source otherSource depth)
  (later : 2 ≤ stage) :
    entry.evaluated.capArea = DyadicBilinearBoundaryRibbon.dyadicArea
      (fun parameter => (capValues
        (parent := parent) sample otherSample parameter).sub entry.capOrigin) depth
      entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter := by
  rw [entry.evaluated.capArea_eq]
  have same := entry.same_sign later
  have point (parameter : InverseRootPolynomial.Coordinate) : (PreparedEdgeRecasting.recastCenteredEdge other
    parent).edge.point parameter = parent.edge.point parameter := rfl
  cases bit : entry.left.first.flip with
  | false =>
      apply DyadicBilinearBoundaryRibbon.dyadicArea_congr
      intro parameter
      change (⟨_, _⟩ : Stokes.PrimitivePoint) = ⟨_, _⟩
      apply congrArg₂ PrimitivePoint.mk <;>
        dsimp only [RegularAlignment.pairedCapValues, RegularAlignment.capValue,
          capValues,
          Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.capOrigin,
          PrimitivePoint.sub] <;>
        simp only [entry.left.primitive_eq, entry.right.primitive_eq, ← same, bit, if_neg (show (false : Bool) ≠ true
          from fun h => Bool.noConfusion h), point, -eq_self, -iff_self]
      all_goals rfl
  | true =>
      rw [← dyadicArea_joint_neg (fun
        parameter => (capValues
        (parent := parent) sample otherSample parameter).sub entry.capOrigin)]
      apply DyadicBilinearBoundaryRibbon.dyadicArea_congr
      intro parameter
      change (⟨_, _⟩ : Stokes.PrimitivePoint) = ⟨_, _⟩
      apply congrArg₂ PrimitivePoint.mk <;>
        dsimp only [RegularAlignment.pairedCapValues, RegularAlignment.capValue,
          capValues,
          Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.capOrigin,
          PrimitivePoint.sub] <;>
        simp only [entry.left.primitive_eq, entry.right.primitive_eq, ← same, bit, if_pos (rfl : true = true),
          DensePolynomial.eval_neg, point, -eq_self, -iff_self] <;> ring1

/-- Adding the actual retained cap-origin correction recovers the unanchored paired dyadic area. -/
theorem Entry.cap_area_unanchored (entry : CommonRibbonRequest.Entry request sample otherSample source otherSource
  depth) (later : 2 ≤ stage) :
    entry.evaluated.capArea + entry.capOriginTerm = DyadicBilinearBoundaryRibbon.dyadicArea
      (capValues (parent := parent)
      sample otherSample) depth
      entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter := by
  rw [entry.cap_area_unsigned later, Bilinear.dyadicArea_sub_origin]
  change (_ - entry.capOriginTerm) + entry.capOriginTerm = _
  ring1

/-- Summing all original retained interval areas and their origin corrections recovers the complete unanchored paired
cap area at the combined depth. -/
theorem Evaluation.cap_area_unanchored (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source
  otherSource depth)
    (later : 2 ≤ stage) :
    evaluated.capArea + Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.entries.map
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.capOriginTerm) =
      DyadicBilinearBoundaryRibbon.dyadicArea
        (capValues (parent := parent)
        sample otherSample) (common.depth + depth) 0 1 := by
  have aggregate (entries : List (CommonRibbonRequest.Entry request sample otherSample source otherSource depth)) :
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.capArea)) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.capOriginTerm) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => DyadicBilinearBoundaryRibbon.dyadicArea
        (capValues (parent := parent)
        sample otherSample) depth
        entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter)) := by
    induction entries with
    | nil => change (0 : Data.Gaussian.Basic.Canonical) + 0 = 0; ring1
    | cons head tail ih =>
        change (_ + _) + (_ + _) = _ + _
        have rearrange (a b c d : Data.Gaussian.Basic.Canonical) : (a + b) + (c + d) = (a + c) + (b + d) := by ring1
        rw [rearrange, head.cap_area_unanchored later, ih]
  have plans := congrArg (List.map (fun plan => plan.interval.edge)) evaluated.plans_eq
  have intervals := congrArg (List.map CommonInterval.edge) request.intervals_eq
  rw [Map.map_map] at plans intervals
  have edges := (plans.trans intervals).trans common.edges_eq
  rw [evaluated.capArea_eq, aggregate]
  have mapped := congrArg (fun edges => Data.Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge =>
    DyadicBilinearBoundaryRibbon.dyadicArea
      (capValues (parent := parent)
      sample otherSample) depth edge.left.parameter edge.right.parameter))) edges
  rw [Map.map_map] at mapped
  exact mapped.trans (Bilinear.dyadicEdges_sum_area _ common.depth depth _ _)

namespace Evaluation

set_option genInjectivity false in
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation in
/-- Both complete increment paths, with shared-sign cap readback and the remaining exact correction. No endpoint
discrepancy is silently discarded. -/
structure PairedPaths (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source otherSource depth)
  where
  /-- The retained complete original source increment path and its exact correction. -/ sourcePath :
    Evaluation.SourcePath evaluated
  /-- The cached complete paired cap increment path on the original common cover. -/ capPath : List
    Stokes.PrimitivePoint
  /-- The cap path is the exact dyadic increment list at the combined retained depth. -/ capPath_eq : capPath =
    DyadicPairedPrimitivePaths.increments
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent)
    sample otherSample)
    (common.depth + depth) 0 1
  /-- The cached summary of this exact paired cap path. -/ capSummary : PairedIncrementArea.Summary capPath
  /-- The cached sum of every actual retained cap-origin correction. -/ origins : Data.Gaussian.Basic.Canonical
  /-- The origin cache is the exact finite sum over the original ordered evaluated entries. -/ origins_eq : origins =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.entries.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.capOriginTerm)
  /-- The cached bilinear chord joining the actual first and last cap readings. -/ chord : Data.Gaussian.Basic.Canonical
  /-- The chord is exactly the edge area of the retained cap endpoints. -/ chord_eq : chord = Stokes.edgeArea
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent)
    sample otherSample 0) (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues
    (parent := parent) sample otherSample 1)
  /-- The retained cap summary area equals the evaluated cap area plus all origins minus its actual endpoint chord. -/
    capArea_eq : capSummary.areaValue = evaluated.capArea + origins - chord
  /-- The cached complete source-to-cap area correction. -/ correction : Data.Gaussian.Basic.Canonical
  /-- The correction combines the retained source correction with exact origin and chord terms. -/ correction_eq :
    correction = sourcePath.correction - origins + chord
  /-- The actual complete source and cap areas, after the retained correction, satisfy the original target. -/ accurate
    : Data.Gaussian.Norm.Basic.normSq
    (sourcePath.summary.areaValue - capSummary.areaValue - correction) < target

constructive_injectivity PairedPaths

/-- Cache both complete increment paths and every actual origin and endpoint correction, preserving the original paired
area payment. -/
def pairedPaths (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source otherSource depth) (later
  : 2 ≤ stage) :
  PairedPaths evaluated :=
  by
  let sourcePath := evaluated.sourcePath
  let values := Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent :=
    parent) sample otherSample
  let path := DyadicPairedPrimitivePaths.increments values (common.depth + depth) 0 1
  let summary := Summary.build path
  let origins := Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.entries.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.capOriginTerm)
  let chord := Stokes.edgeArea (values 0) (values 1)
  have area : summary.areaValue = evaluated.capArea + origins - chord := by
    rw [summary.area_eq, DyadicPairedPrimitivePaths.increments_area, ← evaluated.cap_area_unanchored later]
  have equal : sourcePath.summary.areaValue - summary.areaValue - (sourcePath.correction - origins + chord) =
      sourcePath.summary.areaValue - evaluated.capArea - sourcePath.correction := by rw [area]; ring1
  exact ⟨sourcePath, path, rfl, summary, origins, rfl, chord, rfl, area, sourcePath.correction - origins + chord, rfl,
    (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_lt sourcePath.accurate⟩

end Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
