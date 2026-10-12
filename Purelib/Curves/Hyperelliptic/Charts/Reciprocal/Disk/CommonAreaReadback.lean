module
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonCapOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonSignChain
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonBlockArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonIncrementArea
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

public section

/-! The requested block comparison reads back to the literal parent dyadic
paths. Shared sheet signs disappear from the full bilinear cap area. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback.Bilinear

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib

/-- Flattened fine increments equal the exact combined-depth parent increments.

The original coarse edge order and both endpoint parameters are retained.
The successor calculation concatenates the same two midpoint subdivisions. -/
theorem dyadicEdges_flatten_increments (values : Normalization.InverseRootPolynomial.Coordinate →
  Topology.Polygon.Stokes.PrimitivePoint) (coarse fine : Nat) (first last :
  Branches.ClearSheetContinuation.Subdivision.Endpoint) :
    ((Branches.ClearSheetContinuation.Subdivision.dyadicEdges coarse first last).map (fun edge =>
      Path.Dyadic.DyadicPairedPrimitivePaths.increments values fine edge.left.parameter edge.right.parameter)).flatten =
      Path.Dyadic.DyadicPairedPrimitivePaths.increments values (coarse + fine) first.parameter last.parameter := open
        Purelib.Data.Rat in by
  induction coarse generalizing first last with
  | zero =>
      dsimp only [Branches.ClearSheetContinuation.Subdivision.dyadicEdges,
        List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
      rw [Data.List.Append.append_nil, Nat.zero_add]
  | succ coarse ih =>
      rw [Branches.ClearSheetContinuation.Subdivision.dyadicEdges, Data.List.Map.map_append,
        Data.List.Flatten.flatten_append, ih, ih, Nat.succ_add, Path.Dyadic.DyadicPairedPrimitivePaths.increments]
      have middle : Branches.ClearSheetContinuation.midpoint first.parameter last.parameter =
          Rectangle.Partition.PreparedBoxPartitions.midpoint first.parameter last.parameter := by
        unfold Branches.ClearSheetContinuation.midpoint Rectangle.Partition.PreparedBoxPartitions.midpoint
        apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
        calc
          _ = first.parameter + last.parameter := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
          _ = first.parameter * 2 + ((last.parameter - first.parameter) / 2) * 2 := by
            rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]; ring1
          _ = _ := by ring1
      change Path.Dyadic.DyadicPairedPrimitivePaths.increments values (coarse + fine) first.parameter
        (Branches.ClearSheetContinuation.midpoint _ _) ++
        Path.Dyadic.DyadicPairedPrimitivePaths.increments values (coarse + fine)
          (Branches.ClearSheetContinuation.midpoint _ _) last.parameter = _
      rw [middle]

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback.Bilinear

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib

variable {genus count otherCount : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential other :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {secondCover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonCover firstCover secondCover}
  {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage depth : Nat} {box otherBox :
    Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {source : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data stage} {otherSource :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive otherData stage}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular common target minimum}
  {evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation request sample
    otherSample source otherSource depth}

/-- Flattening interval paths gives the complete original parent increment path.

The retained plan and interval equalities identify their original edge list.
Mapping and flattening preserve its order at the combined dyadic depth. -/
theorem Evaluation.flatten_paths (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation request sample otherSample
  source otherSource depth)
    (values : Normalization.InverseRootPolynomial.Coordinate → Topology.Polygon.Stokes.PrimitivePoint) (fine : Nat) :
    (evaluated.entries.map (fun entry => Path.Dyadic.DyadicPairedPrimitivePaths.increments values fine
      entry.plan.interval.edge.left.parameter
      entry.plan.interval.edge.right.parameter)).flatten = Path.Dyadic.DyadicPairedPrimitivePaths.increments values
        (common.depth + fine) 0 1 := by
  have plans := congrArg (List.map (fun plan => plan.interval.edge)) evaluated.plans_eq
  have intervals := congrArg (List.map Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonInterval.edge)
    request.intervals_eq
  rw [Data.List.Map.map_map] at plans intervals
  have edges := (plans.trans intervals).trans common.edges_eq
  have paths := congrArg (fun edges => (edges.map (fun edge => Path.Dyadic.DyadicPairedPrimitivePaths.increments values
    fine edge.left.parameter edge.right.parameter)).flatten) edges
  rw [Data.List.Map.map_map] at paths
  exact paths.trans (Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback.Bilinear.dyadicEdges_flatten_increments
    values common.depth fine _ _)

/-- A common sign on both cap readings preserves their full bilinear area.

The two literal Boolean branches retain the original polynomial readings.
Simultaneous negation preserves both the dyadic area and endpoint correction. -/
theorem Evaluation.SharedPair.area_unsigned (shared :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.SharedPair evaluated) (fine :
  Nat) :
    Path.PairedIncrementArea.area (Path.Dyadic.DyadicPairedPrimitivePaths.increments shared.values fine 0 1) =
      Path.PairedIncrementArea.area (Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
      otherSample) fine 0 1) := open Purelib.Polynomial in by
  rw [Path.Dyadic.DyadicPairedPrimitivePaths.increments_area, Path.Dyadic.DyadicPairedPrimitivePaths.increments_area]
  cases bit : shared.flip with
  | false =>
      have points (parameter : Normalization.InverseRootPolynomial.Coordinate) : shared.values parameter =
        Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
        otherSample parameter := by
        apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk
        · rw [shared.first_eq, bit, if_neg (by intro impossible; cases impossible)]
        · rw [shared.second_eq, bit, if_neg (by intro impossible; cases impossible)]
      rw [Periods.DyadicBilinearBoundaryRibbon.dyadicArea_congr points, points 0, points 1]
  | true =>
      have points (parameter : Normalization.InverseRootPolynomial.Coordinate) : shared.values parameter =
          ⟨-(Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent)
            sample otherSample parameter).left,
            -(Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent)
              sample otherSample parameter).right⟩ := by
        apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk
        · rw [shared.first_eq, bit, if_pos rfl]
          exact Dense.Basic.DensePolynomial.eval_neg _ _
        · rw [shared.second_eq, bit, if_pos rfl]
          exact Dense.Basic.DensePolynomial.eval_neg _ _
      rw [Periods.DyadicBilinearBoundaryRibbon.dyadicArea_congr points,
        Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.dyadicArea_joint_neg, points 0,
        points 1]
      simp only [Topology.Polygon.Stokes.edgeArea]
      ring1

namespace AreaRequest.Certified
variable {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest request} {fine : Nat}

/-- The source path is the complete original source-value increment path.

Its retained pair and ribbon equations identify the same ordered increments
at the combined depth, without replacing either original source owner. -/
theorem source_path (certified : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest.Certified prepared
  sample otherSample fine) :
    certified.compared.firstPath = Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues certified.source
      certified.otherSource) (common.depth + fine) 0 1 := by
  rw [certified.compared.firstPath_eq, certified.compared.pairs_eq, Data.List.Map.map_map]
  exact certified.ribbons.flatten_paths _ fine

/-- The cap path is the complete shared cap-value increment path.

The retained pair equations and ribbon paths read the original shared values
on the same ordered combined-depth parent subdivision. -/
theorem cap_path (certified : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest.Certified prepared
  sample otherSample fine) :
    certified.compared.secondPath = Path.Dyadic.DyadicPairedPrimitivePaths.increments certified.shared.values
      (common.depth + fine) 0 1 := by
  rw [certified.compared.secondPath_eq, certified.compared.pairs_eq, Data.List.Map.map_map]
  exact certified.ribbons.flatten_paths _ fine

/-- The retained cap area equals the unsigned full cap-polynomial path area. -/
theorem cap_area (certified : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest.Certified prepared
  sample otherSample fine) :
    certified.compared.secondSummary.areaValue = Path.PairedIncrementArea.area
      (Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
      otherSample) (common.depth + fine) 0 1) := by
  rw [certified.compared.secondSummary.area_eq,
    Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest.Certified.cap_path
    certified, certified.shared.area_unsigned]

/-- The complete original source area and unsigned cap area differ by less than the retained target. -/
@[expose] def UnsignedAreaError (certified :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest.Certified prepared sample otherSample fine) : Prop
  :=
  Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (Path.Dyadic.DyadicPairedPrimitivePaths.increments
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues certified.source
    certified.otherSource) (common.depth + fine) 0 1) -
    Path.PairedIncrementArea.area (Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
      otherSample) (common.depth + fine) 0 1)) < target

/-- Actual whole-parent paths, unsigned cap polynomial, strict requested
error, and no residual correction or endpoint-chord substitution. -/
theorem unsigned_area_error (certified : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest.Certified
  prepared sample otherSample fine) :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest.Certified.UnsignedAreaError
  certified := by
  have bound := certified.accurate
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest.Certified.cap_area
    certified, certified.compared.firstSummary.area_eq,
    Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest.Certified.source_path
    certified] at bound
  exact bound

end AreaRequest.Certified
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
