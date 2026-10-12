module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Integration.Path.WeightedPathComparison
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann
open Purelib

/-! Both differentials are read at the same fine fragment parameters.
Pointwise errors and source increments are proved from retained certificates,
not supplied as analytic assumptions by the consumer. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
  (SourceEntry Fragment firstQueryDensity secondQueryDensity)

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
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

/-- The original domain primitive readings for the first differential at one face stage. -/
@[expose] def FirstData (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (index : Nat) :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives occurrence.compared.entered.domain differential
    index

/-- The recast original domain primitive readings for the second differential at the same stage. -/
@[expose] def SecondData (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (other : Hyperelliptic.Differentials.Basic.Differential genus) (index : Nat) :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives (occurrence.recastComparison
    other).entered.domain other index

/-- Pair the two aligned grid values at one point of the original retained parent fragment. -/
@[expose] def gridValues (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry)
  {index : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index) (otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index) (parameter :
      Normalization.InverseRootPolynomial.Coordinate) : PrimitivePoint :=
  ⟨data.anchors.alignedValue data.offsets piece.column piece.row (entry.plan.parent.edge.point parameter),
    otherData.anchors.alignedValue otherData.offsets piece.column piece.row (entry.plan.parent.edge.point parameter)⟩

/-- Pair the two cached source primitive values at one point of the original retained parent. -/
@[expose] def sourceValues (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (parameter : Normalization.InverseRootPolynomial.Coordinate) : PrimitivePoint :=
  ⟨entry.certified.source.primitive.value.eval (entry.plan.parent.edge.point parameter),
    entry.certified.otherSource.primitive.value.eval (entry.plan.parent.edge.point parameter)⟩

/-- The common error density dominating both original fragment-query densities. -/
@[expose] def queryDensity (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry)
  (index : Nat) : Coordinate :=
  max (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.firstQueryDensity entry piece index)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.secondQueryDensity entry piece index)

/-- The common slope bound dominating both retained source primitive densities. -/
@[expose] def sourceDensity (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) : Coordinate :=
  max entry.plan.data.sourceSlope entry.plan.otherData.sourceSlope

/-- A common source index can be selected before the paired source plan is
built, using the uniform bound on every retained base inverse-root model. -/
@[expose] def sourceQueryMinimum (radius : Normalization.InverseRootPolynomial.Coordinate) : Nat :=
  Rational.Geometric.Search.firstQuarterBelow (1 / 16) 0 radius

/-- The uniform source-query minimum makes every later quarter-radius error smaller than the positive target radius.

The original inverse-root scale is bounded by one sixteenth. -/
theorem source_radius_lt {scale radius : Normalization.InverseRootPolynomial.Coordinate} {index : Nat}
    (small : scale ≤ 1 / 16) (positive : 0 < radius) (later :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceQueryMinimum radius ≤ index) :
    Rational.Geometric.Basic.quarterRadius scale index < radius := by
  have scaled : Rational.Geometric.Basic.quarterRadius scale index ≤ Rational.Geometric.Basic.quarterRadius (1 / 16)
    index := by
    rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct small (Fraction.Order.Arithmetic.pow_nonneg_direct
      (by decide) index)
  exact scaled.trans_lt ((quarterRadius_antitone (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1 / 16) later).trans_lt
    (Rational.Geometric.Search.firstQuarterBelow_accurate (1 / 16) (by decide) 0 radius positive))

/-- Both retained source requests have radii below the common positive radius once its uniform minimum is paid. -/
theorem source_query_radii_lt (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) {radius : Normalization.InverseRootPolynomial.Coordinate}
    (positive : 0 < radius) (minimumPaid :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceQueryMinimum radius ≤ minimum) :
    Rational.Geometric.Basic.quarterRadius entry.source.localRequest.neighborhood.base.model.bound
        entry.source.localRequest.request.index < radius ∧
      Rational.Geometric.Basic.quarterRadius entry.otherSource.localRequest.neighborhood.base.model.bound
        entry.otherSource.localRequest.request.index < radius := by
  have floor : minimum ≤ plan.floor := by rw [plan.floor_eq]; exact Data.Nat.Order.le_max_left ..
  exact ⟨source_radius_lt entry.source.localRequest.neighborhood.base.model.bound_small positive
      (minimumPaid.trans (floor.trans entry.source.index_ge)),
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.source_radius_lt
      entry.otherSource.localRequest.neighborhood.base.model.bound_small positive
      (minimumPaid.trans (floor.trans entry.otherSource.index_ge))⟩

/-- The first original fragment query's retained refinement tail at the specified radius. -/
@[expose] def FirstQueryTail (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry)
  (radius : Normalization.InverseRootPolynomial.Coordinate) :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.QueryTail occurrence.compared.entered.bounds piece.column
    piece.row entry.source.localRequest radius

/-- The recast second fragment query's retained refinement tail at that same radius. -/
@[expose] def SecondQueryTail (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment
  entry) (radius : Normalization.InverseRootPolynomial.Coordinate) :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.QueryTail (occurrence.recastComparison other).entered.bounds
    piece.column piece.row entry.otherSource.localRequest radius

set_option genInjectivity false in
/-- Both differential requests retain their source-error floors. Only the
shared face-refinement index is advanced by this constructor. -/
structure PairedQueryTail (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry)
  (radius : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The retained first-differential query tail. -/ first :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstQueryTail entry piece radius
  /-- The retained recast second-differential query tail. -/ second :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondQueryTail entry piece radius
  /-- The cached common face-refinement threshold. -/ index : Nat
  /-- The common threshold is the maximum of the two retained tail stages. -/ index_eq : index = max first.index
    second.index
  /-- The cached common error-density ceiling. -/ ceiling : Normalization.InverseRootPolynomial.Coordinate
  /-- The common ceiling is the maximum of the two retained tail ceilings. -/ ceiling_eq : ceiling = max first.ceiling
    second.ceiling
  /-- Every later shared face stage has paired query density at most the cached common ceiling. -/ accurate : ∀ later,
    index ≤ later → Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece later ≤
    ceiling

constructive_injectivity PairedQueryTail

/-- Combine the two retained query tails at their maximum stage and error ceiling.

Only the face-refinement stage advances; both original source requests remain fixed. -/
@[expose] def pairedQueryTail (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment
  entry)
    (radius : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < radius) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.PairedQueryTail entry piece radius := by
  let first := Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryTail occurrence.compared.entered.bounds
    piece.column piece.row entry.source.localRequest radius positive
  let second := Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryTail
    (occurrence.recastComparison other).entered.bounds
    piece.column piece.row entry.otherSource.localRequest radius positive
  refine ⟨first, second, max first.index second.index, rfl, max first.ceiling second.ceiling, rfl, ?_⟩
  intro later after
  exact Fraction.Order.Basic.max_le ((first.accurate later ((Data.Nat.Order.le_max_left ..).trans after)).trans
    (Fraction.Order.Basic.le_max_left ..))
    ((second.accurate later ((Data.Nat.Order.le_max_right ..).trans after)).trans (Fraction.Order.Basic.le_max_right
      ..))

/-- Bound the common tail ceiling using both original numerator and inverse-model bounds.

The positive radius and paid uniform source minimum control the retained source errors. -/
theorem PairedQueryTail.ceiling_le {entry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine} {piece :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry}
    {radius : Normalization.InverseRootPolynomial.Coordinate} (tail :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.PairedQueryTail entry piece radius) (positive : 0
      < radius)
    (minimumPaid : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceQueryMinimum radius ≤ minimum)
      :
    tail.ceiling ≤ max
      (24 * radius * (occurrence.compared.entered.bounds.numerator piece.column piece.row *
        occurrence.compared.entered.bounds.inverse))
      (24 * radius * ((occurrence.recastComparison other).entered.bounds.numerator piece.column piece.row *
        (occurrence.recastComparison other).entered.bounds.inverse)) := by
  have small := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.source_query_radii_lt entry positive
    minimumPaid
  have first := tail.first.ceiling_le (tail.first.source_eq.trans_lt small.1).le
  have second := tail.second.ceiling_le (tail.second.source_eq.trans_lt small.2).le
  rw [tail.ceiling_eq]
  exact Fraction.Order.Basic.max_le (first.trans (Fraction.Order.Basic.le_max_left ..)) (second.trans
    (Fraction.Order.Basic.le_max_right ..))

/-- Bound both grid-to-source increment errors by the common query density and actual parent displacement.

The two parameters stay inside the same retained fragment, and both differentials share its geometry. -/
theorem paired_query_error (evaluated :
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
      (((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data otherData
        last).sub (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data
        otherData first)).sub
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry last).sub
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry first)))
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece index *
          Data.Gaussian.Norm.Basic.normSq (entry.plan.parent.edge.point last - entry.plan.parent.edge.point first))
          := by
  have left := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.first_fragment_error evaluated entry
    member piece data first last firstInside lastInside
  have right := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.second_fragment_error evaluated entry
    member piece otherData first last firstInside lastInside
  exact ⟨by
      change Fraction.Order.Basic.LessEqual _ _
      have h := left.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Basic.le_max_left
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.firstQueryDensity entry piece index)
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.secondQueryDensity entry piece index))
        (Gaussian.Norm.Basic.normSq_nonneg _))
      change Fraction.Order.Basic.LessEqual _ _ at h
      simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity,
        Topology.Polygon.Stokes.PrimitivePoint.sub,
        Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using h,
    by
      change Fraction.Order.Basic.LessEqual _ _
      have h := right.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Basic.le_max_right
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.firstQueryDensity entry piece index)
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.secondQueryDensity entry piece index))
        (Gaussian.Norm.Basic.normSq_nonneg _))
      change Fraction.Order.Basic.LessEqual _ _ at h
      simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity,
        Topology.Polygon.Stokes.PrimitivePoint.sub,
        Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using h⟩

/-- Bound both cached source primitive increments by the common retained slope and squared parameter displacement. -/
theorem source_increment_bound (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment
  entry)
    (first last : Normalization.InverseRootPolynomial.Coordinate)
    (firstInside : piece.interval.lower ≤ first ∧ first ≤ piece.interval.upper)
    (lastInside : piece.interval.lower ≤ last ∧ last ≤ piece.interval.upper) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry last).sub
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry first))
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity entry * (last - first)^2) := by
  have firstUnit : 0 ≤ first ∧ first ≤ 1 := ⟨piece.within.1.trans firstInside.1, firstInside.2.trans piece.within.2⟩
  have lastUnit : 0 ≤ last ∧ last ≤ 1 := ⟨piece.within.1.trans lastInside.1, lastInside.2.trans piece.within.2⟩
  have left := entry.certified.source.increment_bound firstUnit lastUnit
  have right := entry.certified.otherSource.increment_bound firstUnit lastUnit
  exact ⟨by
      change Fraction.Order.Basic.LessEqual _ _
      have h := left.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Basic.le_max_left entry.plan.data.sourceSlope entry.plan.otherData.sourceSlope)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      change Fraction.Order.Basic.LessEqual _ _ at h
      simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity,
        Topology.Polygon.Stokes.PrimitivePoint.sub,
        Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using h,
    by
      change Fraction.Order.Basic.LessEqual _ _
      have h := right.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Basic.le_max_right entry.plan.data.sourceSlope entry.plan.otherData.sourceSlope)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      change Fraction.Order.Basic.LessEqual _ _ at h
      have recastPoint (parameter : Normalization.InverseRootPolynomial.Coordinate) :
          (Integration.PreparedEdgeRecasting.recastCenteredEdge other entry.plan.parent).edge.point parameter =
            entry.plan.parent.edge.point parameter := rfl
      simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity,
        Topology.Polygon.Stokes.PrimitivePoint.sub,
        Gaussian.Norm.Basic.normSq_eq_canonical, recastPoint, -eq_self, -iff_self] using h⟩

/-- The finite sample may retain arbitrary repeated or nonuniform parameters.
Centering reuses its cached values; only the actual geometric query error remains. -/
theorem centered_query_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry) {index count : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index) (otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (grid : Periods.CenteredBilinearPath.Sample (fun vertex =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data otherData (parameters
      vertex)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry (parameters vertex))) (vertex
      : Fin (count + 1)) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((grid.centered vertex).sub (source.centered vertex))
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece index *
        Data.Gaussian.Norm.Basic.normSq
        (entry.plan.parent.edge.point (parameters vertex) - entry.plan.parent.edge.point (parameters 0))) := by
  rw [grid.centered_eq, source.centered_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.paired_query_error evaluated entry member piece
    data otherData (parameters 0) (parameters vertex) (inside 0) (inside vertex)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
