module
import Purelib.Data.List.Append
import Purelib.Data.List.Reverse
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.Resampling.OrientedBounds
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunOrder
import Purelib.Integration.Path.Dyadic.SourceDyadicResampling
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring

public section

/-! Compare retained physical runs with the same closed bank's source paths.
Reversal uses the retained increment lists, never a new primitive sampling. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
open
  ExteriorProgram.SurfacePreparation
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path.Resampling
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison (sourceReferencePaths)
open Purelib.Integration.Path.Resampling.OrientedBounds (orientParameter)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns (StoredSourceChord SourceChordRun
  SourceChordGrouping sourceParentIncrement)
open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.PairedIncrementArea (area)

/-- The total of a singleton primitive increment is the original increment. -/
private theorem singleton_total (value : Stokes.PrimitivePoint) : PairedIncrementArea.total [value] = value := by
  apply congrArg₂ PrimitivePoint.mk <;> exact add_zero _

/-- Negating both primitive coordinates twice recovers the original primitive point. -/
private theorem negate_twice (value : Stokes.PrimitivePoint) :
    PrimitivePoint.zero.sub (PrimitivePoint.zero.sub value) = value := by
  apply congrArg₂ PrimitivePoint.mk <;> dsimp only [PrimitivePoint.sub, PrimitivePoint.zero, -eq_self, -iff_self] <;>
    ring1

/-- Negating each retained primitive increment negates the total displacement. -/
private theorem negate_total (values : List Stokes.PrimitivePoint) :
    PairedIncrementArea.total (values.map (PrimitivePoint.zero.sub)) = PrimitivePoint.zero.sub
      (PairedIncrementArea.total values) := by
  induction values with
  | nil => apply congrArg₂ PrimitivePoint.mk <;> exact (sub_self _).symm
  | cons first rest ih =>
    change (PrimitivePoint.zero.sub first).add (PairedIncrementArea.total (rest.map (PrimitivePoint.zero.sub))) =
      PrimitivePoint.zero.sub (first.add (PairedIncrementArea.total rest))
    rw [ih]
    apply congrArg₂ PrimitivePoint.mk <;> dsimp only [PrimitivePoint.sub, PrimitivePoint.add, PrimitivePoint.zero,
      -eq_self, -iff_self] <;> ring1

/-- Reversing the retained increment list preserves its total displacement. -/
private theorem reverse_total (values : List Stokes.PrimitivePoint) : PairedIncrementArea.total values.reverse =
  PairedIncrementArea.total values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    rw [Data.List.Reverse.reverse_cons, PairedAreaBlocks.total_append,
      singleton_total,
      ih]
    apply congrArg₂ PrimitivePoint.mk <;> exact add_comm _ _

/-- Keep the original increments in forward traversal or reverse and negate them for backward traversal. -/
@[expose] def orientIncrements (forward : Bool) (values : List Stokes.PrimitivePoint) : List PrimitivePoint :=
  if forward then values else values.reverse.map (PrimitivePoint.zero.sub)

/-- Orienting the original increment list preserves or negates its total displacement according to the retained
direction. -/
private theorem orient_total (forward : Bool) (values : List Stokes.PrimitivePoint) :
    PairedIncrementArea.total
      (orientIncrements
      forward values) = if forward then PairedIncrementArea.total values else PrimitivePoint.zero.sub
      (PairedIncrementArea.total values) := by
  cases forward with
  | true => rfl
  | false => exact
    (negate_total
    values.reverse).trans (congrArg (PrimitivePoint.zero.sub)
    (reverse_total
    values))

/-- Negating every paired primitive increment preserves the original polygon area. -/
private theorem negate_area (values : List Stokes.PrimitivePoint) :
    PairedIncrementArea.area (values.map (PrimitivePoint.zero.sub)) = PairedIncrementArea.area values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    rw [List.map_cons, PairedAreaBlocks.area_cons,
      negate_total,
      ih]
    change Stokes.edgeArea (PrimitivePoint.zero.sub first) (PrimitivePoint.zero.sub (PairedIncrementArea.total rest)) +
      PairedIncrementArea.area rest =
      Stokes.edgeArea first (PairedIncrementArea.total rest) + PairedIncrementArea.area rest
    simp only [Stokes.edgeArea, PrimitivePoint.sub, PrimitivePoint.zero, -eq_self, -iff_self]
    ring1

/-- Reversing the original increment order negates its polygon area. -/
private theorem reverse_area (values : List Stokes.PrimitivePoint) : PairedIncrementArea.area values.reverse =
  -PairedIncrementArea.area values := by
  induction values with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = -0; ring1
  | cons first rest ih =>
    rw [Data.List.Reverse.reverse_cons, PairedAreaBlocks.area_append,
      reverse_total,
      singleton_total,
      ih]
    change -PairedIncrementArea.area rest + (Stokes.edgeArea first PrimitivePoint.zero + 0) +
      Stokes.edgeArea (PairedIncrementArea.total rest) first =
        -(Stokes.edgeArea first (PairedIncrementArea.total rest) + PairedIncrementArea.area rest)
    simp only [Stokes.edgeArea, PrimitivePoint.zero, -eq_self, -iff_self]
    ring1

/-- Reversing the dyadic sample interval negates its original bilinear area. -/
private theorem dyadic_area_reverse (values : InverseRootPolynomial.Coordinate → Stokes.PrimitivePoint) (depth : Nat)
  (first last : InverseRootPolynomial.Coordinate) :
    DyadicBilinearBoundaryRibbon.dyadicArea values depth last first =
      -DyadicBilinearBoundaryRibbon.dyadicArea values depth first last := by
  induction depth generalizing first last with
  | zero => dsimp only [DyadicBilinearBoundaryRibbon.dyadicArea_zero, Stokes.edgeArea, -eq_self, -iff_self]; ring1
  | succ depth ih =>
    have middle : PreparedBoxPartitions.midpoint last first = PreparedBoxPartitions.midpoint first last := by
      dsimp only [PreparedBoxPartitions.midpoint, -eq_self, -iff_self]
      apply Fraction.Field.mul_right_cancel_of_ne (by decide : (2 : InverseRootPolynomial.Coordinate) ≠ 0)
      rw [add_mul, add_mul, Fraction.Field.div_mul_cancel_of_ne _ _ (by decide),
        Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
      ring1
    rw [DyadicBilinearBoundaryRibbon.dyadicArea_succ, DyadicBilinearBoundaryRibbon.dyadicArea_succ, middle,
      ih (PreparedBoxPartitions.midpoint first last) last, ih first (PreparedBoxPartitions.midpoint first last)]
    ring1

/-- Normalizing the original source parameter to the retained orientation gives the corresponding signed dyadic area. -/
private theorem normalized_source_area (values : InverseRootPolynomial.Coordinate → Stokes.PrimitivePoint) (forward :
  Bool) (depth : Nat) :
    PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments (fun parameter => values
      (OrientedBounds.orientParameter forward parameter)) depth 0 1) =
      if forward then PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments values depth 0 1)
      else -PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments values depth 0 1) := by
  cases forward with
  | true => rfl
  | false =>
    change PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments (fun parameter => values (1 - parameter))
      depth 0 1) = -_
    have affine := (DyadicBilinearBoundaryRibbon.dyadicArea_congr
      (fun parameter => congrArg values (show 1 - parameter = 1 + (-1) * parameter by ring1)) depth 0 1).trans
      (DyadicBilinearBoundaryRibbon.dyadicArea_affine values 1 (-1) depth 0 1)
    simp only [mul_zero, mul_one, add_zero, show (1 : InverseRootPolynomial.Coordinate) + -1 = 0 by ring1, -eq_self,
      -iff_self] at affine
    rw [DyadicPairedPrimitivePaths.increments_area, DyadicPairedPrimitivePaths.increments_area,
      affine,
        dyadic_area_reverse]
    simp only [(show ∀ x : Fraction.Rational, x - 0 = x by intro x; ring1), sub_self, Stokes.edgeArea, -eq_self,
      -iff_self]
    ring1

/-- Reversing the original block order and orienting every stored block equals orienting the complete flattened
increment list. -/
private theorem orient_blocks (blocks : List (List Stokes.PrimitivePoint)) :
    (blocks.reverse.map
      (orientIncrements
      false)).flatten =
      orientIncrements
      false blocks.flatten := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    rw [Data.List.Reverse.reverse_cons, Data.List.Map.map_append, Data.List.Flatten.flatten_append]
    rw [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, Data.List.Append.append_nil,
      List.flatten_cons]
    rw [ih]
    simp only
      [orientIncrements,
      if_neg Bool.false_ne_true, Data.List.Reverse.reverse_append, Data.List.Map.map_append, -eq_self, -iff_self]
    rfl

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {program : ExteriorProgram lifted
    differential} {prepared :
    ExteriorProgram.SurfacePreparation
    regular domains program}
  {requested : Coordinate} {minimum : Nat}

/-- The retained source-path cache contains exactly one path per original parent plan. -/
theorem sourcePaths_length (comparison : prepared.ClosedBoundaryComparison other requested minimum) :
    comparison.sourcePaths.length = comparison.original.plans.length :=
  Data.List.OfFn.Basic.length_ofFn

/-- Read the original retained parent reference sample's actual dyadic depth. -/
@[expose] def sourceReferenceDepth (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (index : Fin comparison.original.plans.length) : Nat :=
  (comparison.entries.get index).depth

/-- Read the retained original parent path's area with the selected traversal sign. -/
@[expose] def sourceReferenceArea (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (forward : Bool) (index : Fin comparison.original.plans.length) : Gaussian :=
  let path := comparison.sourcePaths[index.val]'(index.isLt.trans_eq
    (sourcePaths_length
    comparison).symm)
  if forward then PairedIncrementArea.area path else -PairedIncrementArea.area path

/-- The original oriented dyadic source sample has exactly the retained signed reference area. -/
private theorem source_reference_area (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (forward : Bool) (index : Fin comparison.original.plans.length) :
    PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments
      (fun parameter => comparison.sourceValues index (OrientedBounds.orientParameter forward parameter))
      (comparison.sourceReferenceDepth index) 0 1) = comparison.sourceReferenceArea forward index := by
  have readback : comparison.sourcePaths[index.val]'(index.isLt.trans_eq
    (sourcePaths_length
    comparison).symm) =
      DyadicPairedPrimitivePaths.increments (comparison.sourceValues index) (comparison.sourceReferenceDepth index) 0 1
        := by
    dsimp only [ClosedBoundaryComparison.sourcePaths, SourceComparison.sourceReferencePaths, -eq_self, -iff_self]
    rw [Data.List.OfFn.Basic.getElem_ofFn]
    rfl
  exact
    (normalized_source_area
    _ _ _).trans
    (congrArg (fun path => if forward then PairedIncrementArea.area path else -PairedIncrementArea.area path)
      readback).symm

/-- Changing the source orientation preserves the closed unit parameter interval. -/
private theorem orient_unit (forward : Bool) {parameter : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧
  parameter ≤ 1) :
    0 ≤ OrientedBounds.orientParameter forward parameter ∧ OrientedBounds.orientParameter forward parameter ≤ 1 := by
  cases forward with
  | true => exact inside
  | false => exact ⟨Fraction.Order.Arithmetic.sub_nonneg_direct inside.2,
      (Fraction.Order.Arithmetic.sub_le_sub_direct le_rfl inside.1).trans_eq ((show ∀ x : Fraction.Rational, x - 0 = x
        by intro x; ring1) _)⟩

/-- The original paired source-density bound controls increments in either retained orientation. -/
private theorem source_oriented_increment (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (forward : Bool) (index : Fin comparison.original.plans.length) (a b : InverseRootPolynomial.Coordinate)
    (al : 0 ≤ a) (au : a ≤ 1) (bl : 0 ≤ b) (bu : b ≤ 1) :
    PrimitivePoint.Bounded
      ((comparison.sourceValues index (OrientedBounds.orientParameter forward b)).sub
        (comparison.sourceValues index (OrientedBounds.orientParameter forward a)))
      (comparison.sourceDensity index * (b - a)^2) := by
  have left := (comparison.entries.get index).source.increment_bound

      (orient_unit
      forward ⟨al, au⟩)
      (orient_unit
      forward ⟨bl, bu⟩)
  have right := (comparison.entries.get index).otherSource.increment_bound

      (orient_unit
      forward ⟨al, au⟩)
      (orient_unit
      forward ⟨bl, bu⟩)
  have step : (OrientedBounds.orientParameter forward b - OrientedBounds.orientParameter forward a)^2 = (b - a)^2 := by
    cases forward with
    | true => rfl
    | false => change ((1 - b) - (1 - a))^2 = _; ring1
  rw [step] at left right
  have leftBound := left.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Basic.le_max_left (PairedParentCharts.ChartParent comparison.original index).data.sourceSlope
      (PairedParentCharts.ChartParent comparison.original index).otherData.sourceSlope)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have rightBound := right.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Basic.le_max_right (PairedParentCharts.ChartParent comparison.original index).data.sourceSlope
      (PairedParentCharts.ChartParent comparison.original index).otherData.sourceSlope)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  constructor
  · change Fraction.Order.Basic.LessEqual _ _ at leftBound ⊢
    simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at leftBound
    convert leftBound using 1
    rfl
    simp only [ClosedBoundaryComparison.sourceDensity, -eq_self, -iff_self]
    rfl
  · change Fraction.Order.Basic.LessEqual _ _ at rightBound ⊢
    simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at rightBound
    convert rightBound using 1
    rfl
    simp only [ClosedBoundaryComparison.sourceDensity, -eq_self, -iff_self]
    rfl

/-- The retained original reference request pays its dyadic sampling error at the cached reference depth. -/
private theorem source_reference_rate (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (index : Fin comparison.original.plans.length) :
    16 * (comparison.sourceDensity index)^2 * ((1 / 2 :
      InverseRootPolynomial.Coordinate)^(comparison.sourceReferenceDepth index))^2 ≤
      (comparison.entries.get index).referenceError :=
  (comparison.entries.get index).reference_rate

/-- Pay one full parent resampling against the actual original-bank path. The original reference request already pays
its sampling error; only the physical mesh width remains to be selected by the retained surface. -/
theorem source_run_resampling (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (forward : Bool) (index : Fin comparison.original.plans.length) {points : List InverseRootPolynomial.Coordinate}
      {width : InverseRootPolynomial.Coordinate}
    (actual : List Stokes.PrimitivePoint)
    (readback : actual = SourceListResampling.increments
      (fun parameter => comparison.sourceValues index (OrientedBounds.orientParameter forward parameter)) 0 points)
    (chain : SourceResampling.Chain 0 points 1) (steps : SourceResampling.widths 0 points width) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area actual - comparison.sourceReferenceArea forward
      index) ≤
      max (16 * (comparison.sourceDensity index)^2 * width^2) (comparison.entries.get index).referenceError := by
  have estimate := SourceDyadicResampling.dyadic_resampling_bound _

      (source_oriented_increment
      comparison forward index) chain steps (comparison.sourceReferenceDepth index)
  have actualBound := (congrArg₂ (fun left right => Data.Gaussian.Norm.Basic.normSq (left - right))
    (congrArg PairedIncrementArea.area readback)
      (source_reference_area
      comparison forward index).symm).trans_le estimate
  rcases le_total width ((1 / 2 : InverseRootPolynomial.Coordinate)^(comparison.sourceReferenceDepth index)) with
    smaller | larger
  · rw [Fraction.Order.Basic.max_eq_right smaller] at actualBound
    exact actualBound.trans
      ((source_reference_rate
      comparison index).trans (Fraction.Order.Basic.le_max_right _ _))
  · rw [Fraction.Order.Basic.max_eq_left larger] at actualBound
    exact actualBound.trans (Fraction.Order.Basic.le_max_left _ _)

/-- The retained original source path's total is its complete forward parent endpoint increment. -/
private theorem sourcePath_total (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (index : Fin comparison.original.plans.length) :
    PairedIncrementArea.total (comparison.sourcePaths[index.val]'(index.isLt.trans_eq
      (sourcePaths_length
      comparison).symm)) =
      SourceChordRuns.sourceParentIncrement comparison true index := by
  dsimp only [ClosedBoundaryComparison.sourcePaths, SourceComparison.sourceReferencePaths, -eq_self, -iff_self]
  rw [Data.List.OfFn.Basic.getElem_ofFn]
  exact DyadicPairedPrimitivePaths.increments_total _ _ 0 1

/-- The oriented retained source path's total is its original parent endpoint increment in the same direction. -/
private theorem sourcePath_oriented_total (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (forward : Bool) (index : Fin comparison.original.plans.length) :
    PairedIncrementArea.total
      (orientIncrements
      forward
      (comparison.sourcePaths[index.val]'(index.isLt.trans_eq
        (sourcePaths_length
        comparison).symm))) =
      SourceChordRuns.sourceParentIncrement comparison forward index := by
  have bound :=
    sourcePath_total
    comparison index
  have oriented :=
    orient_total
    forward
    (comparison.sourcePaths[index.val]'(index.isLt.trans_eq
      (sourcePaths_length
      comparison).symm))
  cases forward with
  | true => exact oriented.trans bound
  | false =>
    apply oriented.trans ((congrArg (PrimitivePoint.zero.sub) bound).trans ?_)
    apply congrArg₂ PrimitivePoint.mk <;>
      simp only [SourceChordRuns.sourceParentIncrement, if_pos (rfl : true = true), if_neg Bool.false_ne_true,
        PrimitivePoint.sub, PrimitivePoint.zero, -eq_self, -iff_self] <;> ring1

/-- Select the occurrence's actual source paths from one retained bank read, reversing stored increments when the
physical side runs backwards. -/
@[expose] def sourceOccurrenceBlocks (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (forward : Bool) : List (List Stokes.PrimitivePoint) :=
  let bank := comparison.sourcePaths
  let indices := if forward then comparison.parentIndices outer else (comparison.parentIndices outer).reverse
  indices.map (fun index =>
    orientIncrements
    forward
    (bank[index.val]'(index.isLt.trans_eq
      (sourcePaths_length
      comparison).symm)))

/-- The retained occurrence blocks read exactly the original signed reference areas in their oriented parent order. -/
private theorem sourceOccurrenceBlocks_areas (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (forward : Bool) :
    (comparison.sourceOccurrenceBlocks outer forward).map PairedIncrementArea.area =
      (if forward then comparison.parentIndices outer else (comparison.parentIndices outer).reverse).map
        (comparison.sourceReferenceArea forward) := by
  rw
    [sourceOccurrenceBlocks,
    Data.List.Map.map_map]
  apply Map.map_congr_left
  intro index _
  cases forward with
  | true => rfl
  | false =>
      exact (negate_area _).trans (reverse_area _)

/-- The finite sum of the original scalar differences is the difference of their finite sums. -/
private theorem sum_differences {α : Type} (entries : List α) (left right : α → InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => left entry - right entry)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map left) - Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (entries.map right) := by
  induction entries with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons entry rest ih =>
    change (left entry - right entry) + _ = (left entry + _) - (right entry + _)
    rw [ih]
    ring1

/-- Keep the individual parent errors available when aggregating an entire component, so each original parent is counted
only once. -/
theorem source_runs_resampling_eq (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (forward : Bool) {vertical : Bool}
    (runs : List (SourceChordRuns.SourceChordRun comparison vertical))
    (ordered : runs.map SourceChordRun.parent =
      if forward then comparison.parentIndices outer else (comparison.parentIndices outer).reverse) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (runs.map (fun run => PairedIncrementArea.area run.values -
      comparison.sourceReferenceArea forward run.parent)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((runs.map SourceChordRun.values).map PairedIncrementArea.area) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum ((comparison.sourceOccurrenceBlocks outer forward).map
          PairedIncrementArea.area) := by
  have references := congrArg (List.map (comparison.sourceReferenceArea forward)) ordered
  rw [Data.List.Map.map_map] at references
  change runs.map (fun run => comparison.sourceReferenceArea forward run.parent) = _ at references
  rw
    [sum_differences,
    references, ←
    sourceOccurrenceBlocks_areas,
    Data.List.Map.map_map]
  rfl

/-- The exact original-parent order identifies the reference sum. Only the fixed parent-run count is paid, never the
number of fine trace vertices. -/
theorem source_runs_resampling_bound (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (forward : Bool) {vertical : Bool}
    (runs : List (SourceChordRuns.SourceChordRun comparison vertical))
    (ordered : runs.map SourceChordRun.parent =
      if forward then comparison.parentIndices outer else (comparison.parentIndices outer).reverse)
    {error : InverseRootPolynomial.Coordinate}
    (bounds : ∀ run ∈ runs, Data.Gaussian.Norm.Basic.normSq
      (PairedIncrementArea.area run.values - comparison.sourceReferenceArea forward run.parent) ≤ error) :
    Data.Gaussian.Norm.Basic.normSq
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum ((runs.map SourceChordRun.values).map PairedIncrementArea.area) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum ((comparison.sourceOccurrenceBlocks outer forward).map
          PairedIncrementArea.area)) ≤
      (runs.length : InverseRootPolynomial.Coordinate)^2 * error := by
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (runs.map (fun run => PairedIncrementArea.area run.values - comparison.sourceReferenceArea forward run.parent))
      error (by
      intro value member
      obtain ⟨run, present, rfl⟩ := Map.mem_map.mp member
      exact bounds run present)
  rw [comparison.source_runs_resampling_eq outer forward runs ordered, Data.List.Map.length_map] at estimate
  exact estimate.trans_eq (by ring1)

/-- The retained occurrence blocks have exactly the original parent endpoint totals in their oriented order. -/
theorem sourceOccurrenceBlocks_totals (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (forward : Bool) :
    (comparison.sourceOccurrenceBlocks outer forward).map PairedIncrementArea.total =
      (if forward then comparison.parentIndices outer else (comparison.parentIndices outer).reverse).map
        (SourceChordRuns.sourceParentIncrement comparison forward) := by
  rw
    [sourceOccurrenceBlocks,
    Data.List.Map.map_map]
  exact Map.map_congr_left (fun index _ =>
    sourcePath_oriented_total
    comparison forward index)

/-- The backward occurrence slice is the reversal and negation of its actual forward stored increments. -/
private theorem sourceOccurrenceBlocks_reverse
    (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) :
    (comparison.sourceOccurrenceBlocks outer false).flatten =

        orientIncrements
        false (comparison.sourceOccurrenceBlocks outer true).flatten := by
  let bank := comparison.sourcePaths
  let read := fun index : Fin comparison.original.plans.length =>
    bank[index.val]'(index.isLt.trans_eq
      (sourcePaths_length
      comparison).symm)
  have reversed : comparison.sourceOccurrenceBlocks outer false =
      ((comparison.parentIndices outer).map read).reverse.map
        (orientIncrements
        false) := by
    rw [← Data.List.Reverse.map_reverse, Data.List.Map.map_map]
    rfl
  exact (congrArg List.flatten reversed).trans
    (orient_blocks
    _)

/-- Correct physical-side orientation using the original stored increments. The reversal changes the full area sign, not
merely the endpoint total. -/
theorem sourceOccurrenceBlocks_area_orientation
    (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (forward : Bool) :
    (if forward then PairedIncrementArea.area (comparison.sourceOccurrenceBlocks outer forward).flatten
      else -PairedIncrementArea.area (comparison.sourceOccurrenceBlocks outer forward).flatten) =
        PairedIncrementArea.area (comparison.sourceOccurrenceBlocks outer true).flatten := by
  cases forward with
  | true => rfl
  | false =>
    rw
      [sourceOccurrenceBlocks_reverse]
    change -PairedIncrementArea.area ((comparison.sourceOccurrenceBlocks outer true).flatten.reverse.map
      (PrimitivePoint.zero.sub)) = _
    rw
      [negate_area,
      reverse_area,
      neg_neg]

/-- Correcting the retained traversal direction recovers the exact original forward occurrence total. -/
theorem sourceOccurrenceBlocks_total_orientation
    (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (forward : Bool) :
    (if forward then PairedIncrementArea.total (comparison.sourceOccurrenceBlocks outer forward).flatten
      else PrimitivePoint.zero.sub (PairedIncrementArea.total (comparison.sourceOccurrenceBlocks outer
        forward).flatten)) =
        PairedIncrementArea.total (comparison.sourceOccurrenceBlocks outer true).flatten := by
  cases forward with
  | true => rfl
  | false =>
    rw
      [sourceOccurrenceBlocks_reverse,
      orient_total]
    change PrimitivePoint.zero.sub (PrimitivePoint.zero.sub
      (PairedIncrementArea.total (comparison.sourceOccurrenceBlocks outer true).flatten)) = _
    exact
      negate_twice
      _

/-- The actual grouped fine source paths and the original occurrence slice have the same total; their internal areas
need not be equal. -/
theorem source_total_ofFn
    (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (forward : Bool)
    {vertical : Bool} {count : Nat} {source : Fin count → SourceChordRuns.StoredSourceChord comparison vertical}
    (grouped : SourceChordRuns.SourceChordGrouping comparison vertical (List.ofFn source))
    (totals : (grouped.runs.map SourceChordRun.values).map PairedIncrementArea.total =
      (if forward then comparison.parentIndices outer else (comparison.parentIndices outer).reverse).map
        (SourceChordRuns.sourceParentIncrement comparison forward)) :
    PairedIncrementArea.total (List.ofFn (fun i => (source i).increments)).flatten =
      PairedIncrementArea.total (comparison.sourceOccurrenceBlocks outer forward).flatten := by
  have flattened := grouped.values_flatten
  rw [OfFn.Basic.map_ofFn] at flattened
  exact (congrArg PairedIncrementArea.total flattened.symm).trans
    ((PairedAreaBlocks.total_flatten _).trans
      ((congrArg PairedIncrementArea.total
        (totals.trans (comparison.sourceOccurrenceBlocks_totals outer forward).symm)).trans
          (PairedAreaBlocks.total_flatten _).symm))

/-- The retained source occurrence area splits into the original block areas and the polygon of their exact oriented
parent totals. -/
theorem sourceOccurrenceBlocks_area (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (forward : Bool) :
    PairedIncrementArea.area (comparison.sourceOccurrenceBlocks outer forward).flatten =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((comparison.sourceOccurrenceBlocks outer forward).map
        PairedIncrementArea.area) +
        PairedIncrementArea.area ((if forward then comparison.parentIndices outer else (comparison.parentIndices
          outer).reverse).map
          (SourceChordRuns.sourceParentIncrement comparison forward)) :=
  (PairedAreaBlocks.area_flatten _).trans
    (congrArg (fun totals => Data.Gaussian.Norm.Sum.Basic.gaussianSum ((comparison.sourceOccurrenceBlocks outer
      forward).map PairedIncrementArea.area) + PairedIncrementArea.area totals)
      (comparison.sourceOccurrenceBlocks_totals outer forward))

/-- Identical retained parent-total polygons cancel, leaving exactly the difference of original block-area sums. -/
theorem source_area_difference (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (outer : Fin prepared.occurrences.length) (forward : Bool) (blocks : List (List Stokes.PrimitivePoint)) (source :
      List Stokes.PrimitivePoint)
    (regrouped : PairedIncrementArea.area source = Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map
      PairedIncrementArea.area) +
      PairedIncrementArea.area ((if forward then comparison.parentIndices outer else (comparison.parentIndices
        outer).reverse).map
        (SourceChordRuns.sourceParentIncrement comparison forward))) :
    PairedIncrementArea.area source - PairedIncrementArea.area (comparison.sourceOccurrenceBlocks outer forward).flatten
      =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map PairedIncrementArea.area) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum ((comparison.sourceOccurrenceBlocks outer forward).map
        PairedIncrementArea.area) := by
  rw [regrouped, comparison.sourceOccurrenceBlocks_area outer forward]
  ring1

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
