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
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}

/-- The common retained fragment-query density is nonnegative at every face stage. -/
theorem queryDensity_nonnegative (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment
  entry) (index : Nat) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece index :=
  (Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity_nonnegative occurrence.compared.entered.bounds
    piece.column piece.row entry.source.localRequest index).trans
    (Fraction.Order.Basic.le_max_left ..)

/-- The common retained source-slope density is nonnegative. -/
theorem sourceDensity_nonnegative (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) : 0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity
  entry :=
  entry.plan.data.sourceSlope_nonnegative.trans (Fraction.Order.Basic.le_max_left ..)

/-- The paired trace density combining actual parent movement, query error and retained source slope. -/
@[expose] def traceDensity (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry)
  (index : Nat) : Coordinate :=
  2 * (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece index *
    entry.plan.parent.edge.pointMovement +
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity entry)

/-- The fragment-query density weighted by the actual containing box's squared diagonal. -/
@[expose] def traceError (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry)
  (index : Nat) : Coordinate :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece index *
    (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq

set_option genInjectivity false in
/-- Cached coefficients valid at every later face index, selected without
reading a fine primitive sample or assuming a successful accuracy test. -/
structure UniformFragmentBounds (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment
  entry) where
  /-- The cached common uniform query-density bound. -/ query : Normalization.InverseRootPolynomial.Coordinate
  /-- The cached query bound is the maximum of the two original uniform domain bounds. -/ query_eq : query = max
    (Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.uniformQueryDensity occurrence.compared.entered.bounds
    piece.column piece.row)
    (Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.uniformQueryDensity
      (occurrence.recastComparison other).entered.bounds piece.column piece.row)
  /-- The cached uniform query bound is nonnegative. -/ query_nonnegative : 0 ≤ query
  /-- The cached query bound dominates both-component query density at every stage. -/ query_bound : ∀ index,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece index ≤ query
  /-- The cached common uniform trace-density bound. -/ density : Normalization.InverseRootPolynomial.Coordinate
  /-- The trace bound combines the cached query bound, actual parent movement and original source density. -/ density_eq
    : density = 2 * (query * entry.plan.parent.edge.pointMovement +
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity entry)
  /-- The cached uniform trace-density bound is nonnegative. -/ density_nonnegative : 0 ≤ density
  /-- The cached trace-density bound applies at every face-refinement stage. -/ density_bound : ∀ index,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity entry piece index ≤ density

constructive_injectivity UniformFragmentBounds

/-- Cache stage-independent query and trace-density bounds from the two original domain certificates.

The construction keeps the selected parent's actual movement and source slope, without evaluating a later primitive
sample. -/
@[expose] def uniformFragmentBounds (entry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine) (piece :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.UniformFragmentBounds entry piece := by
  let query := max (Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.uniformQueryDensity
    occurrence.compared.entered.bounds piece.column piece.row)
    (Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.uniformQueryDensity
      (occurrence.recastComparison other).entered.bounds piece.column piece.row)
  have bounded (index : Nat) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece
    index ≤ query :=
    Fraction.Order.Basic.max_le ((Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity_uniform_le
      occurrence.compared.entered.bounds
      piece.column piece.row entry.source.localRequest index).trans (Fraction.Order.Basic.le_max_left ..))
      (((Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity_uniform_le
        (occurrence.recastComparison other).entered.bounds piece.column piece.row
        entry.otherSource.localRequest index).trans (Fraction.Order.Basic.le_max_right ..)))
  have queryNonnegative := (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative
    entry piece 0).trans (bounded 0)
  have movementNonnegative : 0 ≤ entry.plan.parent.edge.pointMovement := Gaussian.Norm.Basic.normSq_nonneg _
  let density := 2 * (query * entry.plan.parent.edge.pointMovement +
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity entry)
  have densityNonnegative : 0 ≤ density := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct queryNonnegative movementNonnegative)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.sourceDensity_nonnegative entry))
  refine ⟨query, rfl, queryNonnegative, bounded, density, rfl, densityNonnegative, ?_⟩
  intro index
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (bounded
      index) movementNonnegative) le_rfl) (by decide)

/-- A paid source-radius minimum bounds the paired query tail by the cached uniform density times the radius. -/
theorem UniformFragmentBounds.query_tail_bound {entry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine} {piece :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry}
    (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.UniformFragmentBounds entry piece) {radius
      : Normalization.InverseRootPolynomial.Coordinate} (tail :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.PairedQueryTail entry piece radius)
    (positive : 0 < radius) (sourcePaid :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceQueryMinimum radius ≤ minimum) :
    tail.ceiling ≤ 32 * radius * bounds.query := by
  have small := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.source_query_radii_lt entry positive
    sourcePaid
  have first := tail.first.ceiling_le_uniform positive.le (tail.first.source_eq.trans_lt small.1).le
  have second := tail.second.ceiling_le_uniform positive.le (tail.second.source_eq.trans_lt small.2).le
  have firstBound : Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.uniformQueryDensity
    occurrence.compared.entered.bounds
      piece.column piece.row ≤ bounds.query :=
    (Fraction.Order.Basic.le_max_left ..).trans_eq bounds.query_eq.symm
  have secondBound : Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.uniformQueryDensity
      (occurrence.recastComparison other).entered.bounds piece.column piece.row ≤ bounds.query :=
    (Fraction.Order.Basic.le_max_right ..).trans_eq bounds.query_eq.symm
  have factor : 0 ≤ 32 * radius := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le
  rw [tail.ceiling_eq]
  exact Fraction.Order.Basic.max_le (first.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstBound
    factor))
    (second.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct secondBound factor))

/-- Allocate a source-query radius paying the actual fragment box's diagonal-weighted trace error. -/
@[expose] def UniformFragmentBounds.traceRadius {entry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine} {piece :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry}
    (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.UniformFragmentBounds entry piece) (target
      : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  Rational.Budget.Weighted.allowance target
    (32 * bounds.query * (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq)

/-- A positive requested trace tolerance gives a strictly positive allocated source radius. -/
theorem UniformFragmentBounds.traceRadius_positive {entry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine} {piece :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry}
    (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.UniformFragmentBounds entry piece) {target
      : Normalization.InverseRootPolynomial.Coordinate} (positive : 0 < target) :
    0 < bounds.traceRadius target :=
  Rational.Budget.Weighted.allowance_positive positive
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      bounds.query_nonnegative)
      (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq_nonneg)

/-- The allocated positive radius pays the trace error at every stage after the retained paired query tail.

The original source minimum remains an explicit requirement. -/
theorem UniformFragmentBounds.traceError_requested {entry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine} {piece :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry}
    (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.UniformFragmentBounds entry piece) {target
      : Normalization.InverseRootPolynomial.Coordinate} (positive : 0 < target)
    (tail : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.PairedQueryTail entry piece
      (bounds.traceRadius target))
    (sourcePaid : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceQueryMinimum
      (bounds.traceRadius target) ≤ minimum) {index : Nat} (later : tail.index ≤ index) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError entry piece index ≤ target := by
  have query := (tail.accurate index later).trans (bounds.query_tail_bound tail (bounds.traceRadius_positive positive)
    sourcePaid)
  have diagonal := (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq_nonneg
  have weighted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct query diagonal
  have paid := Rational.Budget.Weighted.mul_allowance_le positive.le
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 32) bounds.query_nonnegative) diagonal)
  exact weighted.trans ((by ring1 :
    32 * bounds.traceRadius target * bounds.query * (occurrence.compared.entered.domain.geometry.box piece.column
      piece.row).diagonalSq =
      (32 * bounds.query * (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq) *
        bounds.traceRadius target).trans_le paid)

/-- The original parent's squared point displacement equals its full movement times the squared parameter displacement.
-/
private theorem point_movement (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (first last : Normalization.InverseRootPolynomial.Coordinate) :
    Data.Gaussian.Norm.Basic.normSq (entry.plan.parent.edge.point last - entry.plan.parent.edge.point first) =
      entry.plan.parent.edge.pointMovement * (last - first)^2 := by
  have zeroDifference (value : Purelib.Data.Rat.Fraction.Rational) : value - 0 = value := by ring1
  have full := entry.plan.parent.edge.localSegment.normSq_pointAt_sub_pointAt 1 0
  simp only [zeroDifference, one_pow, Fraction.Field.one_mul, -eq_self, -iff_self] at full
  have segment := entry.plan.parent.edge.localSegment.normSq_pointAt_sub_pointAt last first
  exact segment.trans ((congrArg (fun value => (last - first)^2 * value) full.symm).trans (Fraction.Field.mul_comm ..))

/-- The common retained source slope is bounded by the complete paired trace density. -/
private theorem source_le_trace (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment
  entry) (index : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity entry ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity entry piece index := by
  have extra : 0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece index *
    entry.plan.parent.edge.pointMovement :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative entry piece index)
    (Gaussian.Norm.Basic.normSq_nonneg (entry.plan.parent.edge.point 1 - entry.plan.parent.edge.point 0))
  have nonnegative := add_nonneg extra
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.sourceDensity_nonnegative entry)
  exact (le_add_of_nonneg_left extra).trans ((le_add_of_nonneg_right nonnegative).trans_eq (by
      unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity;
      ring1))

/-- Both aligned grid increments obey the common trace-density bound inside the retained fragment.

Original source increments and grid-to-source errors share the same parent movement and parameter displacement. -/
theorem grid_increment_bound (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry) {index : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index) (otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index)
    (first last : Normalization.InverseRootPolynomial.Coordinate)
    (firstInside : piece.interval.lower ≤ first ∧ first ≤ piece.interval.upper)
    (lastInside : piece.interval.lower ≤ last ∧ last ≤ piece.interval.upper) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data otherData last).sub
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data otherData first))
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity entry piece index * (last - first)^2)
        := by
  have errors := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.paired_query_error evaluated entry
    member piece data otherData first last firstInside lastInside
  have sources := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.source_increment_bound entry piece
    first last firstInside lastInside
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.point_movement] at errors
  have scalar {a b : Normalization.InverseRootPolynomial.Gaussian}
      (error : Gaussian.Basic.Canonical.normSq (a - b) ≤
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece index *
        (entry.plan.parent.edge.pointMovement * (last - first)^2))
      (source : Gaussian.Basic.Canonical.normSq b ≤
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity entry * (last - first)^2) :
      Gaussian.Basic.Canonical.normSq a ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity
        entry piece index * (last - first)^2 := by
    have estimate := Gaussian.Norm.Bounds.normSq_add_le_two (a - b) b
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at estimate
    rw [sub_add_cancel] at estimate
    exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct error source) (by decide)).trans_eq
      (by unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity; ring1))
  exact ⟨scalar errors.1 sources.1, scalar errors.2 sources.2⟩

/-- Every parameter in the retained fragment maps into its original indexed domain box. -/
theorem fragment_contains (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry)
    (parameter : Normalization.InverseRootPolynomial.Coordinate) (inside : piece.interval.lower ≤ parameter ∧ parameter
      ≤ piece.interval.upper) :
    (occurrence.compared.entered.domain.geometry.box piece.column piece.row).Contains (entry.plan.parent.edge.point
      parameter) := by
  rw [Integration.PreparedParentSplitting.prepared_point_eq entry.plan.parent parameter]
  exact piece.contains_query parameter inside

/-- The finite sum of consecutive parameter differences telescopes to the endpoint difference. -/
theorem parameter_length {count : Nat} (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate) :
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
@[expose] def parameterStep (forward : Bool) (first last : Normalization.InverseRootPolynomial.Coordinate) : Coordinate
  :=
  if forward then last - first else first - last

/-- Squaring an oriented parameter step gives the squared unoriented displacement. -/
theorem parameterStep_sq (forward : Bool) (first last : Normalization.InverseRootPolynomial.Coordinate) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward first last)^2 = (last -
      first)^2 := by
  cases forward with
  | true => rfl
  | false => change (first - last)^2 = (last - first)^2; ring1

/-- A parameter step is nonnegative when its endpoints follow the selected orientation. -/
theorem parameterStep_nonnegative (forward : Bool) (first last : Normalization.InverseRootPolynomial.Coordinate)
    (ordered : if forward then first ≤ last else last ≤ first) : 0 ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward first last := by
  cases forward <;> exact Fraction.Order.Arithmetic.sub_nonneg_direct ordered

/-- The finite sum of oriented parameter steps is the correspondingly oriented endpoint displacement. -/
theorem parameterSteps_total {count : Nat} (forward : Bool) (parameters : Fin (count + 1) →
  Normalization.InverseRootPolynomial.Coordinate) :
    FiniteSum.Fin.sumFin (fun edge : Fin count =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters edge.castSucc)
      (parameters edge.succ)) =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters 0) (parameters
        (Fin.last count)) := by
  cases forward with
  | true => exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameter_length parameters
  | false =>
    have equal := FiniteSum.Fin.sumFin_congr (n := count)
      (left := fun edge => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep false
        (parameters edge.castSucc) (parameters edge.succ))
      (right := fun edge => -parameters edge.succ - -parameters edge.castSucc)
      (fun edge => by change parameters edge.castSucc - parameters edge.succ = _; ring1)
    exact equal.trans ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameter_length (fun vertex =>
      -parameters vertex)).trans (by
      change -parameters (Fin.last count) - -parameters 0 = parameters 0 - parameters (Fin.last count)
      ring1))

/-- Every intermediate sample is retained. The bound has no multiplicative
vertex count; coincident parameters and nonuniform subdivisions are allowed. -/
theorem fragment_area_bound (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry) {index count : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index) (otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (forward : Bool)
    (ordered : ∀ edge : Fin count, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    (grid : Periods.CenteredBilinearPath.Sample (fun vertex =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data otherData (parameters
      vertex)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry (parameters vertex))) :
    Data.Gaussian.Norm.Basic.normSq (grid.centeredArea - source.centeredArea) ≤
      40 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError entry piece index *
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity entry piece index *
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters 0) (parameters
          (Fin.last count)))^2 := open Purelib.Integration in by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterSteps_total forward parameters]
  apply Path.WeightedPathComparison.Sample.weighted_full_comparison grid source
    (fun edge : Fin count => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward
      (parameters edge.castSucc) (parameters edge.succ))
    (fun edge => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_nonnegative forward _ _
      (ordered edge))
  · intro vertex
    have errors := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.centered_query_error evaluated entry
      member piece data otherData parameters inside grid source vertex
    have distance := (occurrence.compared.entered.domain.geometry.box piece.column piece.row).normSq_sub_le_diagonalSq
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains entry piece _ (inside vertex))
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains entry piece _ (inside 0))
    have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative entry piece index)
    exact ⟨errors.1.trans upper, errors.2.trans upper⟩
  · intro edge
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.grid_increment_bound evaluated entry member
      piece data otherData _ _ (inside edge.castSucc) (inside edge.succ)
  · intro edge
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
    have bound := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.source_increment_bound entry piece _
      _ (inside edge.castSucc) (inside edge.succ)
    have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.source_le_trace entry piece index)
      (Fraction.Order.Arithmetic.sq_nonneg_direct (parameters edge.succ - parameters edge.castSucc))
    exact ⟨bound.1.trans upper, bound.2.trans upper⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
