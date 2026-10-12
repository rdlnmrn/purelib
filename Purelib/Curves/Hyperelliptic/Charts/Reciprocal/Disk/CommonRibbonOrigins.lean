module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
public import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.PairedIncrementArea

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

public section

/-! Exact source-origin accounting for the complete paired ribbon family.
Different cell anchors contribute explicit finite boundary terms. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins.Bilinear
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon (dyadicArea dyadicArea_zero dyadicArea_succ)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint dyadicEdges)

/-- Changing the original paired primitive origin subtracts its explicit endpoint wedge from finite dyadic area. -/
theorem dyadicArea_sub_origin (values : InverseRootPolynomial.Coordinate → Stokes.PrimitivePoint) (origin :
  Stokes.PrimitivePoint)
    (depth : Nat) (first last : InverseRootPolynomial.Coordinate) :
    DyadicBilinearBoundaryRibbon.dyadicArea (fun parameter => (values parameter).sub origin) depth first last =
      DyadicBilinearBoundaryRibbon.dyadicArea values depth first last - Stokes.edgeArea origin ((values last).sub
        (values first)) := by
  induction depth generalizing first last with
  | zero =>
    rw [DyadicBilinearBoundaryRibbon.dyadicArea_zero, DyadicBilinearBoundaryRibbon.dyadicArea_zero]; simp only
      [-eq_self, -iff_self, Stokes.edgeArea, PrimitivePoint.sub]; ring1
  | succ depth ih =>
      rw [DyadicBilinearBoundaryRibbon.dyadicArea_succ, DyadicBilinearBoundaryRibbon.dyadicArea_succ, ih, ih]
      simp only [-eq_self, -iff_self, Stokes.edgeArea, PrimitivePoint.sub]
      ring1

/-- Summing original fine areas over a complete coarse dyadic edge list gives the combined-depth area. -/
theorem dyadicEdges_sum_area (values : InverseRootPolynomial.Coordinate → Stokes.PrimitivePoint) (coarse fine : Nat)
  (first last : ClearSheetContinuation.Subdivision.Endpoint) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((ClearSheetContinuation.Subdivision.dyadicEdges coarse first
      last).map (fun edge => DyadicBilinearBoundaryRibbon.dyadicArea values fine edge.left.parameter
      edge.right.parameter)) =
      DyadicBilinearBoundaryRibbon.dyadicArea values (coarse + fine) first.parameter last.parameter := by
  induction coarse generalizing first last with
  | zero =>
      change DyadicBilinearBoundaryRibbon.dyadicArea values fine first.parameter last.parameter + 0 =
        DyadicBilinearBoundaryRibbon.dyadicArea values (0 + fine) first.parameter last.parameter
      rw [Nat.zero_add, add_zero]
  | succ coarse ih =>
      rw [ClearSheetContinuation.Subdivision.dyadicEdges, Purelib.Data.List.Map.map_append, IncrementArea.sum_append,
        ih, ih, Nat.succ_add, DyadicBilinearBoundaryRibbon.dyadicArea_succ]
      have middle : ClearSheetContinuation.midpoint first.parameter last.parameter =
          PreparedBoxPartitions.midpoint first.parameter last.parameter := by
        unfold ClearSheetContinuation.midpoint PreparedBoxPartitions.midpoint
        apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
        calc
          _ = first.parameter + last.parameter := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
          _ = first.parameter * 2 + ((last.parameter - first.parameter) / 2) * 2 := by
            rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]; ring1
          _ = _ := by ring1
      change DyadicBilinearBoundaryRibbon.dyadicArea values (coarse + fine) first.parameter
        (ClearSheetContinuation.midpoint _ _) +
        DyadicBilinearBoundaryRibbon.dyadicArea values (coarse + fine) (ClearSheetContinuation.midpoint _ _)
          last.parameter = _
      rw [middle]

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins.Bilinear

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover CommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest (Entry Evaluation)
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

/-- Pair the two original source primitive values before subtracting their separate cell origins. -/
@[expose] def sourceValues (source : UniformReciprocalPrimitives.SourcePrimitive data stage) (otherSource :
  UniformReciprocalPrimitives.SourcePrimitive otherData stage)
    (parameter : InverseRootPolynomial.Coordinate) : PrimitivePoint :=
  ⟨source.primitive.value.eval (parent.edge.point parameter), otherSource.primitive.value.eval (parent.edge.point
    parameter)⟩

/-- Read both original source primitive origins from this exact retained interval's cell owners. -/
@[expose] def Entry.sourceOrigin (entry : CommonRibbonRequest.Entry request sample otherSample source otherSource depth)
  : PrimitivePoint :=
  ⟨source.primitive.value.eval (parent.edge.point entry.plan.interval.first.owner.left.parameter),
    otherSource.primitive.value.eval (parent.edge.point entry.plan.interval.second.owner.left.parameter)⟩

/-- The explicit wedge of the retained original source origin with the interval's actual paired increment. -/
@[expose] def Entry.sourceOriginTerm (entry : CommonRibbonRequest.Entry request sample otherSample source otherSource
  depth) : Data.Gaussian.Basic.Canonical :=
  Stokes.edgeArea entry.sourceOrigin
    ((sourceValues source otherSource
    entry.plan.interval.edge.right.parameter).sub
    (sourceValues source otherSource
      entry.plan.interval.edge.left.parameter))

/-- Adding the actual retained source-origin correction recovers the original unanchored finite dyadic source area. -/
theorem Entry.source_area_unanchored (entry : CommonRibbonRequest.Entry request sample otherSample source otherSource
  depth) :
    entry.evaluated.sourceArea + entry.sourceOriginTerm = DyadicBilinearBoundaryRibbon.dyadicArea
      (sourceValues source
      otherSource) depth
      entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter := by
  rw [entry.evaluated.sourceArea_eq]
  change DyadicBilinearBoundaryRibbon.dyadicArea (fun parameter =>
    (sourceValues source otherSource
    parameter).sub entry.sourceOrigin) depth _ _ + _ = _
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins.Bilinear.dyadicArea_sub_origin]
  change (_ - entry.sourceOriginTerm) + entry.sourceOriginTerm = _
  ring1

/-- Adding the actual retained source-origin correction recovers the original unanchored finite dyadic source area. -/
theorem Evaluation.source_area_unanchored (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source
  otherSource depth) :
    evaluated.sourceArea + Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.entries.map
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.sourceOriginTerm) =
      DyadicBilinearBoundaryRibbon.dyadicArea
        (sourceValues source
        otherSource) (common.depth + depth) 0 1 := by
  have aggregate (entries : List (CommonRibbonRequest.Entry request sample otherSample source otherSource depth)) :
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.sourceArea)) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.sourceOriginTerm) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => DyadicBilinearBoundaryRibbon.dyadicArea
        (sourceValues source
        otherSource) depth
        entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter)) := by
    induction entries with
    | nil => change (0 : Data.Gaussian.Basic.Canonical) + 0 = 0; ring1
    | cons head tail ih =>
        change (_ + _) + (_ + _) = _ + _
        have rearrange (a b c d : Data.Gaussian.Basic.Canonical) : (a + b) + (c + d) = (a + c) + (b + d) := by ring1
        rw [rearrange, head.source_area_unanchored, ih]
  have plans := congrArg (List.map (fun plan => plan.interval.edge)) evaluated.plans_eq
  have intervals := congrArg (List.map CommonInterval.edge) request.intervals_eq
  rw [Purelib.Data.List.Map.map_map] at plans intervals
  have edges := (plans.trans intervals).trans common.edges_eq
  rw [evaluated.sourceArea_eq, aggregate]
  have mapped := congrArg (fun edges => Data.Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge =>
    DyadicBilinearBoundaryRibbon.dyadicArea
      (sourceValues source
      otherSource) depth edge.left.parameter edge.right.parameter))) edges
  rw [Purelib.Data.List.Map.map_map] at mapped
  exact mapped.trans (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins.Bilinear.dyadicEdges_sum_area _
    common.depth depth _ _)

namespace Evaluation

set_option genInjectivity false in
/-- The actual source path and its one-pass summary, with every change of origin and the open-path endpoint chord
retained in the correction. -/
structure SourcePath (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source otherSource depth)
  where
  /-- The cached original complete paired source increment path. -/ path : List Stokes.PrimitivePoint
  /-- The retained source path uses the original paired values at the exact combined common-cover depth. -/ path_eq :
    path = DyadicPairedPrimitivePaths.increments
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource)
    (common.depth + depth) 0 1
  /-- The cached original paired source path's total and area certificate. -/ summary : PairedIncrementArea.Summary path
  /-- The cached sum of actual original source-origin correction wedges. -/ origins : Data.Gaussian.Basic.Canonical
  /-- The origin correction is exactly the sum over the retained original interval entries. -/ origins_eq : origins =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.entries.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.sourceOriginTerm)
  /-- The cached original open source endpoint chord area. -/ chord : Data.Gaussian.Basic.Canonical
  /-- The chord is exactly the wedge of the original source values at parameters zero and one. -/ chord_eq : chord =
    Stokes.edgeArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues
    source otherSource 0)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource
    1)
  /-- The original source path area equals the retained interval area plus origins minus the explicit endpoint chord. -/
    area_eq : summary.areaValue = evaluated.sourceArea + origins - chord
  /-- The cached full correction combining original ribbon endpoints, cell origins and the open chord. -/ correction :
    Data.Gaussian.Basic.Canonical
  /-- The retained full correction is exactly endpoint correction plus source origins minus chord. -/ correction_eq :
    correction = evaluated.endpoint + origins - chord
  /-- The actual original source path and retained cap areas satisfy the paid target after the full explicit correction.
  -/
  accurate : Data.Gaussian.Norm.Basic.normSq (summary.areaValue - evaluated.capArea - correction) < target

constructive_injectivity SourcePath

/-- Cache the original full paired source path and summary, retaining all cell-origin and open endpoint chord
corrections. -/
@[expose] def sourcePath (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source otherSource
  depth) : SourcePath
  evaluated := by
  let values := Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source
    otherSource
  let path := DyadicPairedPrimitivePaths.increments values (common.depth + depth) 0 1
  let summary := Summary.build path
  let origins := Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.entries.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.sourceOriginTerm)
  let chord := Stokes.edgeArea (values 0) (values 1)
  have area : summary.areaValue = evaluated.sourceArea + origins - chord := by
    rw [summary.area_eq, DyadicPairedPrimitivePaths.increments_area, ← evaluated.source_area_unanchored]
  have equal : summary.areaValue - evaluated.capArea - (evaluated.endpoint + origins - chord) = evaluated.remainder :=
    by
    rw [area, evaluated.remainder_eq]
    ring1
  exact ⟨path, rfl, summary, origins, rfl, chord, rfl, area, evaluated.endpoint + origins - chord, rfl,
    (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_lt evaluated.accurate⟩

end Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
