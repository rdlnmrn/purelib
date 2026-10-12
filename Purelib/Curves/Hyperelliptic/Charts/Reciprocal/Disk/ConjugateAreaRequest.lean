module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
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
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
import Purelib.Integration.Path.PairedBlockComparison
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateIncrementArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonIncrementArea
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path.DyadicConjugateIncrementComparison
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes

/-! Requested whole-parent conjugate area comparison on the existing source
models and the shared signed reciprocal polynomial pair. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateAreaRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover CommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest (Evaluation sourceValues
  capValues dyadicArea_joint_neg)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest (AreaRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths (increments increments_area)
open Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon (dyadicArea_congr)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback.Bilinear (dyadicEdges_flatten_increments)
open Purelib.Integration.Path.PairedIncrementArea (area)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
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
  {target : Coordinate} {minimum stage depth : Nat} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {source : SourcePrimitive data stage}
    {otherSource : SourcePrimitive otherData
    stage}
  {request : CommonRibbonRequest regular common
    target minimum}
  {evaluated : Evaluation
    request sample otherSample source otherSource depth}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst conjugateFirst_bounded conjugateFirst_error)
open Purelib.Integration.Path.DyadicConjugateIncrementComparison.PairedIncrementArea (total_conjugate)
open Purelib.Integration.Path.DyadicConjugateIncrementComparison.Bilinear (increments_conjugate)

/-- The same computed model stage pays complete conjugate parent paths, including the polygon of interval totals. -/
theorem AreaRequest.conjugate_area_accurate (prepared : CommonAreaRequest.AreaRequest request)
    (shared : Evaluation.SharedPair evaluated) (later : prepared.index ≤ stage) (fine : Nat) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments (fun
      parameter => ConjugateIncrementComparison.conjugateFirst (CommonRibbonRequest.sourceValues source otherSource
      parameter))
        (common.depth + fine) 0 1) -
      PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments (fun parameter =>
        ConjugateIncrementComparison.conjugateFirst (shared.values parameter))
        (common.depth + fine) 0 1)) < target := by
  let pairs := evaluated.entries.map (fun entry =>
    (DyadicPairedPrimitivePaths.increments (fun parameter => ConjugateIncrementComparison.conjugateFirst
      (CommonRibbonRequest.sourceValues source otherSource parameter)) fine
      entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter,
     DyadicPairedPrimitivePaths.increments (fun parameter => ConjugateIncrementComparison.conjugateFirst (shared.values
       parameter)) fine
      entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter))
  have bound := PairedBlockComparison.blocks_area_difference_bound pairs
    (Geometric.Basic.quarterRadius_nonneg prepared.regularScale_nonnegative stage) prepared.density_nonnegative
    (areaError := 16 * Geometric.Basic.quarterRadius prepared.regularScale stage * prepared.density)
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Map.mem_map.mp member
      dsimp only [Prod.fst, Prod.snd]
      rw [← Bilinear.increments_conjugate, ← Bilinear.increments_conjugate]
      exact (shared.conjugate_interval_area_bound entry retained fine).trans
        (prepared.entry_allowances entry retained).1)
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Map.mem_map.mp member
      dsimp only [Prod.fst, Prod.snd]
      rw [← Bilinear.increments_conjugate, ← Bilinear.increments_conjugate, PairedIncrementArea.total_conjugate,
        PairedIncrementArea.total_conjugate]
      have original := (shared.block_totals entry retained fine).1
      have transformed := ConjugateIncrementComparison.conjugateFirst_error original
      have larger := (prepared.entry_allowances entry retained).2.1
      exact ⟨transformed.1.trans larger, transformed.2.trans larger⟩)
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Map.mem_map.mp member
      dsimp only [Prod.fst, Prod.snd]
      rw [← Bilinear.increments_conjugate, PairedIncrementArea.total_conjugate]
      have original := (shared.block_totals entry retained fine).2.1
      have transformed := ConjugateIncrementComparison.conjugateFirst_bounded original
      have larger := (prepared.entry_allowances entry retained).2.2
      exact ⟨transformed.1.trans larger, transformed.2.trans larger⟩)
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Map.mem_map.mp member
      dsimp only [Prod.fst, Prod.snd]
      rw [← Bilinear.increments_conjugate, PairedIncrementArea.total_conjugate]
      have original := (shared.block_totals entry retained fine).2.2
      have transformed := ConjugateIncrementComparison.conjugateFirst_bounded original
      have larger := (prepared.entry_allowances entry retained).2.2
      exact ⟨transformed.1.trans larger, transformed.2.trans larger⟩)
  have count : evaluated.entries.length = prepared.count := by
    have length := congrArg List.length evaluated.plans_eq
    rw [Data.List.Map.length_map] at length
    exact length.trans prepared.count_eq.symm
  dsimp only [pairs] at bound
  simp only [Data.List.Map.map_map, Data.List.Map.length_map, count, -eq_self, -iff_self] at bound
  dsimp only [Function.comp_def] at bound
  rw [evaluated.flatten_paths, evaluated.flatten_paths] at bound
  have scale : 2 * ((prepared.count : InverseRootPolynomial.Coordinate)^2 *
      (16 * Geometric.Basic.quarterRadius prepared.regularScale stage * prepared.density) +
      16 * (prepared.count : InverseRootPolynomial.Coordinate)^4 * Geometric.Basic.quarterRadius prepared.regularScale
        stage * prepared.density) =
      Geometric.Basic.quarterRadius prepared.scale stage := by
    rw [prepared.scale_eq, Geometric.Basic.quarterRadius_eq_mul_pow,
      Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  exact bound.trans_lt (scale.trans_lt
    ((quarterRadius_antitone prepared.scale_nonnegative later).trans_lt
      (prepared.error_eq ▸ prepared.accurate)))

/-- The retained common sheet bit cancels from conjugate/value area too. This uses the same signed polynomial pair, not
independent sign choices. -/
theorem Evaluation.SharedPair.conjugate_area_unsigned (shared : Evaluation.SharedPair evaluated) (fine : Nat) :
    PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments (fun parameter =>
      ConjugateIncrementComparison.conjugateFirst (shared.values parameter)) fine 0 1) =
      PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments (fun parameter =>
        ConjugateIncrementComparison.conjugateFirst (CommonRibbonRequest.capValues (parent := parent) sample otherSample
        parameter)) fine 0 1) := by
  rw [DyadicPairedPrimitivePaths.increments_area, DyadicPairedPrimitivePaths.increments_area]
  cases bit : shared.flip with
  | false =>
      have original (parameter : InverseRootPolynomial.Coordinate) : shared.values parameter =
        CommonRibbonRequest.capValues (parent := parent) sample otherSample parameter := by
        apply congrArg₂ PrimitivePoint.mk <;>
          simp only [shared.first_eq, shared.second_eq, bit, if_neg (show ¬ (false = true) from by decide), -eq_self,
            -iff_self] <;> rfl
      have points (parameter : InverseRootPolynomial.Coordinate) := congrArg ConjugateIncrementComparison.conjugateFirst
        (original parameter)
      rw [DyadicBilinearBoundaryRibbon.dyadicArea_congr points, points 0, points 1]
  | true =>
      have original (parameter : InverseRootPolynomial.Coordinate) : shared.values parameter =
          ⟨-(CommonRibbonRequest.capValues (parent := parent) sample otherSample parameter).left,
            -(CommonRibbonRequest.capValues (parent := parent) sample otherSample parameter).right⟩ := by
        apply congrArg₂ PrimitivePoint.mk <;>
          simp only [CommonRibbonRequest.capValues, shared.first_eq, shared.second_eq, bit, if_pos (Eq.refl true),
            DensePolynomial.eval_neg, -eq_self, -iff_self] <;> rfl
      have points (parameter : InverseRootPolynomial.Coordinate) : ConjugateIncrementComparison.conjugateFirst
        (shared.values parameter) =
          ⟨-(ConjugateIncrementComparison.conjugateFirst (CommonRibbonRequest.capValues (parent := parent) sample
            otherSample parameter)).left,
            -(ConjugateIncrementComparison.conjugateFirst (CommonRibbonRequest.capValues (parent := parent) sample
              otherSample parameter)).right⟩ :=
        congrArg ConjugateIncrementComparison.conjugateFirst (original parameter)
      rw [DyadicBilinearBoundaryRibbon.dyadicArea_congr points, CommonRibbonRequest.dyadicArea_joint_neg, points 0,
        points 1]
      simp only [Stokes.edgeArea, -eq_self, -iff_self]
      ring1

/-- A strict bound on the actual whole-parent paths and unsigned cap polynomials, ready for their inverse-arc and
endpoint-chord readbacks. -/
theorem AreaRequest.Certified.conjugate_unsigned_area_error
    {prepared : CommonAreaRequest.AreaRequest request} {fine : Nat}
    (certified : AreaRequest.Certified prepared sample otherSample fine) (later : prepared.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments (fun
      parameter => ConjugateIncrementComparison.conjugateFirst
        (CommonRibbonRequest.sourceValues certified.source certified.otherSource parameter)) (common.depth + fine) 0 1)
          -
      PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments (fun parameter =>
        ConjugateIncrementComparison.conjugateFirst
        (CommonRibbonRequest.capValues (parent := parent) sample otherSample parameter)) (common.depth + fine) 0 1)) <
          target := by
  have bound := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateAreaRequest.AreaRequest.conjugate_area_accurate
    prepared certified.shared later fine
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateAreaRequest.Evaluation.SharedPair.conjugate_area_unsigned
    certified.shared] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateAreaRequest
