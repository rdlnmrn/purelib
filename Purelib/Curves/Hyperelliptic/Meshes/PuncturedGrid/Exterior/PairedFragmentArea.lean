module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Integration.Path.WeightedPathComparison
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

public section

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann

/-! Complete finite area comparison inside a retained common fragment.
All analytic bounds come from the actual two grid banks and source models;
the supplied finite parameters carry geometry only. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
open Purelib.Integration.Path.WeightedPathComparison
open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum stage fine : Nat}
  {box otherBox : Rational.Box}
  {sample : Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}

/-- The common retained fragment-query density is nonnegative at every face stage. -/
theorem queryDensity_nonnegative (entry : PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : PairedFragmentQueries.Fragment
  entry) (index : Nat) :
    0 ≤ PairedFragmentValues.queryDensity entry piece index :=
  (Face.FragmentQueries.queryDensity_nonnegative occurrence.compared.entered.bounds
    piece.column piece.row entry.source.localRequest index).trans
    (Basic.le_max_left ..)

/-- The common retained source-slope density is nonnegative. -/
theorem sourceDensity_nonnegative (entry : PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) : 0 ≤ PairedFragmentValues.sourceDensity
  entry :=
  entry.plan.data.sourceSlope_nonnegative.trans (Basic.le_max_left ..)

/-- The paired trace density combining actual parent movement, query error and retained source slope. -/
@[expose] def traceDensity (entry : PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (piece : PairedFragmentQueries.Fragment entry)
  (index : Nat) : Coordinate :=
  2 * (PairedFragmentValues.queryDensity entry piece index *
    entry.plan.parent.edge.pointMovement +
    PairedFragmentValues.sourceDensity entry)

/-- The fragment-query density weighted by the actual containing box's squared diagonal. -/
@[expose] def traceError (entry : PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (piece : PairedFragmentQueries.Fragment entry)
  (index : Nat) : Coordinate :=
  PairedFragmentValues.queryDensity entry piece index *
    (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq

set_option genInjectivity false in
/-- Cached coefficients valid at every later face index, selected without
reading a fine primitive sample or assuming a successful accuracy test. -/
structure UniformFragmentBounds (entry : PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : PairedFragmentQueries.Fragment
  entry) where
  /-- The cached common uniform query-density bound. -/ query : Coordinate
  /-- The cached query bound is the maximum of the two original uniform domain bounds. -/ query_eq : query = max
    (Face.FragmentQueries.uniformQueryDensity occurrence.compared.entered.bounds
    piece.column piece.row)
    (Face.FragmentQueries.uniformQueryDensity
      (occurrence.recastComparison other).entered.bounds piece.column piece.row)
  /-- The cached uniform query bound is nonnegative. -/ query_nonnegative : 0 ≤ query
  /-- The cached query bound dominates both-component query density at every stage. -/ query_bound : ∀ index,
    PairedFragmentValues.queryDensity entry piece index ≤ query
  /-- The cached common uniform trace-density bound. -/ density : Coordinate
  /-- The trace bound combines the cached query bound, actual parent movement and original source density. -/ density_eq
    : density = 2 * (query * entry.plan.parent.edge.pointMovement +
    PairedFragmentValues.sourceDensity entry)
  /-- The cached uniform trace-density bound is nonnegative. -/ density_nonnegative : 0 ≤ density
  /-- The cached trace-density bound applies at every face-refinement stage. -/ density_bound : ∀ index,
    PairedFragmentArea.traceDensity entry piece index ≤ density

constructive_injectivity UniformFragmentBounds

/-- Cache stage-independent query and trace-density bounds from the two original domain certificates.

The construction keeps the selected parent's actual movement and source slope, without evaluating a later primitive
sample. -/
@[expose] def uniformFragmentBounds (entry :
  PairedFragmentQueries.SourceEntry plan sample otherSample fine) (piece :
  PairedFragmentQueries.Fragment entry) :
    UniformFragmentBounds entry piece := by
  let query := max (Face.FragmentQueries.uniformQueryDensity
    occurrence.compared.entered.bounds piece.column piece.row)
    (Face.FragmentQueries.uniformQueryDensity
      (occurrence.recastComparison other).entered.bounds piece.column piece.row)
  have bounded (index : Nat) : PairedFragmentValues.queryDensity entry piece
    index ≤ query :=
    Basic.max_le ((Face.FragmentQueries.queryDensity_uniform_le
      occurrence.compared.entered.bounds
      piece.column piece.row entry.source.localRequest index).trans (Basic.le_max_left ..))
      (((Face.FragmentQueries.queryDensity_uniform_le
        (occurrence.recastComparison other).entered.bounds piece.column piece.row
        entry.otherSource.localRequest index).trans (Basic.le_max_right ..)))
  have queryNonnegative := (PairedFragmentArea.queryDensity_nonnegative
    entry piece 0).trans (bounded 0)
  have movementNonnegative : 0 ≤ entry.plan.parent.edge.pointMovement := Gaussian.Norm.Basic.normSq_nonneg _
  let density := 2 * (query * entry.plan.parent.edge.pointMovement +
    PairedFragmentValues.sourceDensity entry)
  have densityNonnegative : 0 ≤ density := Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Arithmetic.mul_nonneg_direct queryNonnegative movementNonnegative)
      (PairedFragmentArea.sourceDensity_nonnegative entry))
  refine ⟨query, rfl, queryNonnegative, bounded, density, rfl, densityNonnegative, ?_⟩
  intro index
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Arithmetic.mul_le_mul_of_nonneg_right_direct (bounded
      index) movementNonnegative) le_rfl) (by decide)

/-- A paid source-radius minimum bounds the paired query tail by the cached uniform density times the radius. -/
theorem UniformFragmentBounds.query_tail_bound {entry :
  PairedFragmentQueries.SourceEntry plan sample otherSample fine} {piece :
  PairedFragmentQueries.Fragment entry}
    (bounds : UniformFragmentBounds entry piece) {radius
      : Coordinate} (tail :
      PairedQueryTail entry piece radius)
    (positive : 0 < radius) (sourcePaid :
      PairedFragmentValues.sourceQueryMinimum radius ≤ minimum) :
    tail.ceiling ≤ 32 * radius * bounds.query := by
  have small := PairedFragmentValues.source_query_radii_lt entry positive
    sourcePaid
  have first := tail.first.ceiling_le_uniform positive.le (tail.first.source_eq.trans_lt small.1).le
  have second := tail.second.ceiling_le_uniform positive.le (tail.second.source_eq.trans_lt small.2).le
  have firstBound : Face.FragmentQueries.uniformQueryDensity
    occurrence.compared.entered.bounds
      piece.column piece.row ≤ bounds.query :=
    (Basic.le_max_left ..).trans_eq bounds.query_eq.symm
  have secondBound : Face.FragmentQueries.uniformQueryDensity
      (occurrence.recastComparison other).entered.bounds piece.column piece.row ≤ bounds.query :=
    (Basic.le_max_right ..).trans_eq bounds.query_eq.symm
  have factor : 0 ≤ 32 * radius := Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le
  rw [tail.ceiling_eq]
  exact Basic.max_le (first.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct firstBound
    factor))
    (second.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct secondBound factor))

/-- Allocate a source-query radius paying the actual fragment box's diagonal-weighted trace error. -/
@[expose] def UniformFragmentBounds.traceRadius {entry :
  PairedFragmentQueries.SourceEntry plan sample otherSample fine} {piece :
  PairedFragmentQueries.Fragment entry}
    (bounds : UniformFragmentBounds entry piece) (target
      : Coordinate) : Coordinate :=
  Rational.Budget.Weighted.allowance target
    (32 * bounds.query * (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq)

/-- A positive requested trace tolerance gives a strictly positive allocated source radius. -/
theorem UniformFragmentBounds.traceRadius_positive {entry :
  PairedFragmentQueries.SourceEntry plan sample otherSample fine} {piece :
  PairedFragmentQueries.Fragment entry}
    (bounds : UniformFragmentBounds entry piece) {target
      : Coordinate} (positive : 0 < target) :
    0 < bounds.traceRadius target :=
  Rational.Budget.Weighted.allowance_positive positive
    (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide +kernel)
      bounds.query_nonnegative)
      (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq_nonneg)

/-- The allocated positive radius pays the trace error at every stage after the retained paired query tail.

The original source minimum remains an explicit requirement. -/
theorem UniformFragmentBounds.traceError_requested {entry :
  PairedFragmentQueries.SourceEntry plan sample otherSample fine} {piece :
  PairedFragmentQueries.Fragment entry}
    (bounds : UniformFragmentBounds entry piece) {target
      : Coordinate} (positive : 0 < target)
    (tail : PairedQueryTail entry piece
      (bounds.traceRadius target))
    (sourcePaid : PairedFragmentValues.sourceQueryMinimum
      (bounds.traceRadius target) ≤ minimum) {index : Nat} (later : tail.index ≤ index) :
    PairedFragmentArea.traceError entry piece index ≤ target := by
  have query := (tail.accurate index later).trans (bounds.query_tail_bound tail (bounds.traceRadius_positive positive)
    sourcePaid)
  have diagonal := (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq_nonneg
  have weighted := Arithmetic.mul_le_mul_of_nonneg_right_direct query diagonal
  have paid := Rational.Budget.Weighted.mul_allowance_le positive.le
    (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Coordinate) ≤ 32) bounds.query_nonnegative) diagonal)
  exact weighted.trans ((by ring1 :
    32 * bounds.traceRadius target * bounds.query * (occurrence.compared.entered.domain.geometry.box piece.column
      piece.row).diagonalSq =
      (32 * bounds.query * (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq) *
        bounds.traceRadius target).trans_le paid)

/-- The original parent's squared point displacement equals its full movement times the squared parameter displacement.
-/
private theorem point_movement (entry : PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (first last : Coordinate) :
    Gaussian.Norm.Basic.normSq (entry.plan.parent.edge.point last - entry.plan.parent.edge.point first) =
      entry.plan.parent.edge.pointMovement * (last - first)^2 := by
  have zeroDifference (value : Fraction.Rational) : value - 0 = value := by ring1
  have full := entry.plan.parent.edge.localSegment.normSq_pointAt_sub_pointAt 1 0
  simp only [zeroDifference, one_pow, Fraction.Field.one_mul, -eq_self, -iff_self] at full
  have segment := entry.plan.parent.edge.localSegment.normSq_pointAt_sub_pointAt last first
  exact segment.trans ((congrArg (fun value => (last - first)^2 * value) full.symm).trans (Fraction.Field.mul_comm ..))

/-- The common retained source slope is bounded by the complete paired trace density. -/
private theorem source_le_trace (entry : PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : PairedFragmentQueries.Fragment
  entry) (index : Nat) :
    PairedFragmentValues.sourceDensity entry ≤
      PairedFragmentArea.traceDensity entry piece index := by
  have extra : 0 ≤ PairedFragmentValues.queryDensity entry piece index *
    entry.plan.parent.edge.pointMovement :=
    Arithmetic.mul_nonneg_direct
      (PairedFragmentArea.queryDensity_nonnegative entry piece index)
    (Gaussian.Norm.Basic.normSq_nonneg (entry.plan.parent.edge.point 1 - entry.plan.parent.edge.point 0))
  have nonnegative := add_nonneg extra
    (PairedFragmentArea.sourceDensity_nonnegative entry)
  exact (le_add_of_nonneg_left extra).trans ((le_add_of_nonneg_right nonnegative).trans_eq (by
      unfold PairedFragmentArea.traceDensity;
      ring1))

/-- Both aligned grid increments obey the common trace-density bound inside the retained fragment.

Original source increments and grid-to-source errors share the same parent movement and parameter displacement. -/
theorem grid_increment_bound (evaluated :
  PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (piece : PairedFragmentQueries.Fragment entry) {index : Nat}
    (data : FirstData occurrence index) (otherData :
      SecondData occurrence other index)
    (first last : Coordinate)
    (firstInside : piece.interval.lower ≤ first ∧ first ≤ piece.interval.upper)
    (lastInside : piece.interval.lower ≤ last ∧ last ≤ piece.interval.upper) :
    PrimitivePoint.Bounded
      ((PairedFragmentValues.gridValues entry piece data otherData last).sub
        (PairedFragmentValues.gridValues entry piece data otherData first))
      (PairedFragmentArea.traceDensity entry piece index * (last - first)^2)
        := by
  have errors := PairedFragmentValues.paired_query_error evaluated entry
    member piece data otherData first last firstInside lastInside
  have sources := PairedFragmentValues.source_increment_bound entry piece
    first last firstInside lastInside
  rw [PairedFragmentArea.point_movement] at errors
  have scalar {a b : InverseRootPolynomial.Gaussian}
      (error : Gaussian.Basic.Canonical.normSq (a - b) ≤
        PairedFragmentValues.queryDensity entry piece index *
        (entry.plan.parent.edge.pointMovement * (last - first)^2))
      (source : Gaussian.Basic.Canonical.normSq b ≤
        PairedFragmentValues.sourceDensity entry * (last - first)^2) :
      Gaussian.Basic.Canonical.normSq a ≤ PairedFragmentArea.traceDensity
        entry piece index * (last - first)^2 := by
    have estimate := Gaussian.Norm.Bounds.normSq_add_le_two (a - b) b
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at estimate
    rw [sub_add_cancel] at estimate
    exact estimate.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct error source) (by decide)).trans_eq
      (by unfold PairedFragmentArea.traceDensity; ring1))
  exact ⟨scalar errors.1 sources.1, scalar errors.2 sources.2⟩

/-- Every parameter in the retained fragment maps into its original indexed domain box. -/
theorem fragment_contains (entry : PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (piece : PairedFragmentQueries.Fragment entry)
    (parameter : Coordinate) (inside : piece.interval.lower ≤ parameter ∧ parameter
      ≤ piece.interval.upper) :
    (occurrence.compared.entered.domain.geometry.box piece.column piece.row).Contains (entry.plan.parent.edge.point
      parameter) := by
  rw [Integration.PreparedParentSplitting.prepared_point_eq entry.plan.parent parameter]
  exact piece.contains_query parameter inside

/-- The finite sum of consecutive parameter differences telescopes to the endpoint difference. -/
theorem parameter_length {count : Nat} (parameters : Fin (count + 1) → Coordinate) :
    FiniteSum.Fin.sumFin (fun edge : Fin count => parameters edge.succ - parameters edge.castSucc) =
      parameters (Fin.last count) - parameters 0 := by
  induction count with
  | zero => exact (sub_self _).symm
  | succ count ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      change (parameters 1 - parameters 0) +
        FiniteSum.Fin.sumFin (fun edge : Fin count => parameters edge.succ.succ - parameters edge.castSucc.succ) = _
      rw [ih (fun vertex => parameters vertex.succ)]
      change (parameters 1 - parameters 0) + (parameters (Fin.last (count + 1)) - parameters 1) = _
      ring1

/-- Read the parameter displacement in the selected forward or reverse orientation. -/
@[expose] def parameterStep (forward : Bool) (first last : Coordinate) : Coordinate
  :=
  if forward then last - first else first - last

/-- Squaring an oriented parameter step gives the squared unoriented displacement. -/
theorem parameterStep_sq (forward : Bool) (first last : Coordinate) :
    (PairedFragmentArea.parameterStep forward first last)^2 = (last -
      first)^2 := by
  cases forward with
  | true => rfl
  | false => change (first - last)^2 = (last - first)^2; ring1

/-- A parameter step is nonnegative when its endpoints follow the selected orientation. -/
theorem parameterStep_nonnegative (forward : Bool) (first last : Coordinate)
    (ordered : if forward then first ≤ last else last ≤ first) : 0 ≤
      PairedFragmentArea.parameterStep forward first last := by
  cases forward <;> exact Arithmetic.sub_nonneg_direct ordered

/-- The finite sum of oriented parameter steps is the correspondingly oriented endpoint displacement. -/
theorem parameterSteps_total {count : Nat} (forward : Bool) (parameters : Fin (count + 1) →
  Coordinate) :
    FiniteSum.Fin.sumFin (fun edge : Fin count =>
      PairedFragmentArea.parameterStep forward (parameters edge.castSucc)
      (parameters edge.succ)) =
      PairedFragmentArea.parameterStep forward (parameters 0) (parameters
        (Fin.last count)) := by
  cases forward with
  | true => exact PairedFragmentArea.parameter_length parameters
  | false =>
    have equal := FiniteSum.Fin.sumFin_congr (n := count)
      (left := fun edge => PairedFragmentArea.parameterStep false
        (parameters edge.castSucc) (parameters edge.succ))
      (right := fun edge => -parameters edge.succ - -parameters edge.castSucc)
      (fun edge => by change parameters edge.castSucc - parameters edge.succ = _; ring1)
    exact equal.trans ((PairedFragmentArea.parameter_length (fun vertex =>
      -parameters vertex)).trans (by
      change -parameters (Fin.last count) - -parameters 0 = parameters 0 - parameters (Fin.last count)
      ring1))

/-- Every intermediate sample is retained. The bound has no multiplicative
vertex count; coincident parameters and nonuniform subdivisions are allowed. -/
theorem fragment_area_bound (evaluated :
  PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (piece : PairedFragmentQueries.Fragment entry) {index count : Nat}
    (data : FirstData occurrence index) (otherData :
      SecondData occurrence other index)
    (parameters : Fin (count + 1) → Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (forward : Bool)
    (ordered : ∀ edge : Fin count, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    (grid : Periods.CenteredBilinearPath.Sample (fun vertex =>
      PairedFragmentValues.gridValues entry piece data otherData (parameters
      vertex)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      PairedFragmentValues.sourceValues entry (parameters vertex))) :
    Gaussian.Norm.Basic.normSq (grid.centeredArea - source.centeredArea) ≤
      40 * PairedFragmentArea.traceError entry piece index *
        PairedFragmentArea.traceDensity entry piece index *
        (PairedFragmentArea.parameterStep forward (parameters 0) (parameters
          (Fin.last count)))^2 := open Purelib.Integration in by
  rw [← PairedFragmentArea.parameterSteps_total forward parameters]
  apply Path.WeightedPathComparison.Sample.weighted_full_comparison grid source
    (fun edge : Fin count => PairedFragmentArea.parameterStep forward
      (parameters edge.castSucc) (parameters edge.succ))
    (fun edge => PairedFragmentArea.parameterStep_nonnegative forward _ _
      (ordered edge))
  · intro vertex
    have errors := PairedFragmentValues.centered_query_error evaluated entry
      member piece data otherData parameters inside grid source vertex
    have distance := (occurrence.compared.entered.domain.geometry.box piece.column piece.row).normSq_sub_le_diagonalSq
      (PairedFragmentArea.fragment_contains entry piece _ (inside vertex))
        (PairedFragmentArea.fragment_contains entry piece _ (inside 0))
    have upper := Arithmetic.mul_le_mul_of_nonneg_left_direct distance
      (PairedFragmentArea.queryDensity_nonnegative entry piece index)
    exact ⟨errors.1.trans upper, errors.2.trans upper⟩
  · intro edge
    rw [PairedFragmentArea.parameterStep_sq]
    exact PairedFragmentArea.grid_increment_bound evaluated entry member
      piece data otherData _ _ (inside edge.castSucc) (inside edge.succ)
  · intro edge
    rw [PairedFragmentArea.parameterStep_sq]
    have bound := PairedFragmentValues.source_increment_bound entry piece _
      _ (inside edge.castSucc) (inside edge.succ)
    have upper := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (PairedFragmentArea.source_le_trace entry piece index)
      (Arithmetic.sq_nonneg_direct (parameters edge.succ - parameters edge.castSucc))
    exact ⟨bound.1.trans upper, bound.2.trans upper⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
