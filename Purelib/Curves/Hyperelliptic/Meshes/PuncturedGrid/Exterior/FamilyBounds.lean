module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.OfFn.Basic
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Init.Data.List.OfFn
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
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
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Data.Rat.Fraction.Order

public section

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Approximation.Rational.Geometric

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Topology.Polygon

/-! Select aggregate coefficients before owner acquisition, then retain
the fragment coefficients and synchronized query requests. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries (SourceEntry Fragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData
  sourceQueryMinimum pairedQueryTail sourceDensity queryDensity)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (traceError traceDensity
  uniformFragmentBounds queryDensity_nonnegative)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest (OwnerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (FragmentAreaBudget maximum
  maximum_nonnegative le_maximum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (JoinedFragmentFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Geometry.Rational.Box}
  {sample : Primitives.Sample cap differential stage box}
  {otherSample : Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}
  {evaluated :
    ParentEvaluation
    plan sample otherSample fine}
  {data : FirstData occurrence index}
    {otherData : SecondData occurrence
    other index}

/-- The maximum original query-density bound of both differentials in one retained face cell. -/
@[expose] def preOwnerCellQuery (occurrence : SurfaceOccurrence regular domains differential) (other :
  Differential genus)
    (column : Fin (occurrence.compared.entered.domain.steps + 1))
    (row : Fin (occurrence.compared.entered.domain.steps + 1)) : Coordinate :=
  max (FragmentQueries.uniformQueryDensity occurrence.compared.entered.bounds column row)
    (FragmentQueries.uniformQueryDensity
      (occurrence.recastComparison other).entered.bounds column row)

/-- The original per-column maxima of the retained two-differential query-density bounds. -/
@[expose] def preOwnerQueryRows (occurrence : SurfaceOccurrence regular domains differential) (other :
  Differential genus) : List Coordinate :=
  List.ofFn (fun column => PairedFragmentBlocks.maximum id (List.ofFn
    (FamilyBounds.preOwnerCellQuery occurrence other column)))

/-- The weighted radius allowance for the original cell's query density and squared diagonal. -/
@[expose] def preOwnerCellRadius (occurrence : SurfaceOccurrence regular domains differential) (other :
  Differential genus)
    (column row : Fin (occurrence.compared.entered.domain.steps + 1)) (target : Coordinate) :
      Coordinate :=
  Weighted.allowance target (32 * FamilyBounds.preOwnerCellQuery
    occurrence other column row *
    (occurrence.compared.entered.domain.geometry.box column row).diagonalSq)

/-- The common quarter-decay threshold for both original cell models at the supplied radius. -/
@[expose] def preOwnerCellIndex (occurrence : SurfaceOccurrence regular domains differential) (other :
  Differential genus)
    (column row : Fin (occurrence.compared.entered.domain.steps + 1)) (radius : Coordinate) : Nat
      :=
  max (Search.firstQuarterBelow (occurrence.compared.entered.domain.patch.transported.cell column row).model.bound 0
    radius)
    (Search.firstQuarterBelow ((occurrence.recastComparison other).entered.domain.patch.transported.cell column
      row).model.bound 0 radius)

set_option genInjectivity false in
/-- The retained radius and exact source and face thresholds for one original cell query.

The specification equalities bind all three cached values to the supplied cell geometry and target. -/
structure CellQuery (occurrence : SurfaceOccurrence regular domains differential) (other :
  Differential genus)
    (column row : Fin (occurrence.compared.entered.domain.steps + 1)) (target : Coordinate) where
  /-- The cached original cell query radius. -/ radius : Coordinate
  /-- The cached radius is the exact weighted allowance for this cell and target. -/ radius_eq : radius =
    FamilyBounds.preOwnerCellRadius occurrence other column row
    target
  /-- The cached minimum source stage for this cell radius. -/ sourceMinimum : Nat
  /-- The source threshold is exactly the original radius-dependent query minimum. -/ source_eq : sourceMinimum =
    PairedFragmentValues.sourceQueryMinimum radius
  /-- The cached common face threshold for both original cell models. -/ faceIndex : Nat
  /-- The face threshold is exactly the original two-model quarter-decay threshold. -/ face_eq : faceIndex =
    FamilyBounds.preOwnerCellIndex occurrence other column row radius

constructive_injectivity CellQuery

/-- Cache the exact radius, source minimum and two-model face threshold of the original cell query. -/
@[expose] def CellQuery.build (occurrence : SurfaceOccurrence regular domains differential) (other :
  Differential genus)
    (column row : Fin (occurrence.compared.entered.domain.steps + 1)) (target : Coordinate) :
    CellQuery occurrence other column row target :=
  let radius := FamilyBounds.preOwnerCellRadius occurrence other
    column row target
  ⟨radius, rfl, PairedFragmentValues.sourceQueryMinimum radius, rfl,
    FamilyBounds.preOwnerCellIndex occurrence other column row
    radius, rfl⟩

/-- The retained cell query bounds the original fragment trace error once its source and face stages are paid. -/
theorem CellQuery.accurate {entry : SourceEntry plan sample otherSample fine} (piece :
  PairedFragmentQueries.Fragment entry)
    {requested : Coordinate} (query :
      CellQuery occurrence other piece.column piece.row
      requested)
    (positive : 0 < requested) (sourcePaid : query.sourceMinimum ≤ minimum)
    {later : Nat} (facePaid : query.faceIndex ≤ later) : PairedFragmentArea.traceError entry piece later ≤ requested :=
      by
  let bounds := PairedFragmentArea.uniformFragmentBounds entry piece
  have radiusEq : bounds.traceRadius requested = query.radius := query.radius_eq.symm
  let tail := PairedFragmentValues.pairedQueryTail entry piece (bounds.traceRadius requested)
    (bounds.traceRadius_positive positive)
  have sourceEq : PairedFragmentValues.sourceQueryMinimum (bounds.traceRadius requested) = query.sourceMinimum :=
    (congrArg PairedFragmentValues.sourceQueryMinimum radiusEq).trans query.source_eq.symm
  have faceEq : tail.index = query.faceIndex :=
    (congrArg (FamilyBounds.preOwnerCellIndex occurrence other
      piece.column piece.row) radiusEq).trans query.face_eq.symm
  exact bounds.traceError_requested positive tail (sourceEq.trans_le sourcePaid) (faceEq.trans_le facePaid)

/-- The complete dependent row of original cell-query certificates at one retained column. -/
@[expose] def CellQueryRow (occurrence : SurfaceOccurrence regular domains differential) (other :
  Differential genus)
    (column : Fin (occurrence.compared.entered.domain.steps + 1)) (target : Coordinate) :=
  DependentVector (fun row => CellQuery
    occurrence other column row target)

/-- Read the retained source threshold of this exact cell query. -/
@[expose] def cellSourceWeight {column : Fin (occurrence.compared.entered.domain.steps + 1)} {requested :
  Coordinate}
    (row : Fin (occurrence.compared.entered.domain.steps + 1)) (query :
      CellQuery occurrence other column row requested) :
      Nat := query.sourceMinimum

/-- Read the retained face threshold of this exact cell query. -/
@[expose] def cellFaceWeight {column : Fin (occurrence.compared.entered.domain.steps + 1)} {requested :
  Coordinate}
    (row : Fin (occurrence.compared.entered.domain.steps + 1)) (query :
      CellQuery occurrence other column row requested) :
      Nat := query.faceIndex

/-- The maximum original source-query threshold in the retained column. -/
@[expose] def rowSourceWeight {requested : Coordinate} (column : Fin
  (occurrence.compared.entered.domain.steps + 1))
    (row : CellQueryRow occurrence other column
      requested) : Nat := row.maximum FamilyBounds.cellSourceWeight

/-- The maximum original face-query threshold in the retained column. -/
@[expose] def rowFaceWeight {requested : Coordinate} (column : Fin
  (occurrence.compared.entered.domain.steps + 1))
    (row : CellQueryRow occurrence other column
      requested) : Nat := row.maximum FamilyBounds.cellFaceWeight

set_option genInjectivity false in
/-- All query requirements are selected from the fixed face geometry, before any fragment readings or owner requests are
constructed. -/
structure PreOwnerQueries (occurrence : SurfaceOccurrence regular domains differential) (other :
  Differential genus) (target : Coordinate) where
  /-- The complete retained matrix of original cell-query certificates. -/ rows : DependentVector (fun
    column => CellQueryRow occurrence other column
    target)
  /-- The cached maximum source threshold across every original cell. -/ sourceMinimum : Nat
  /-- The source threshold is the exact maximum of the retained column thresholds. -/ source_eq : sourceMinimum =
    rows.maximum FamilyBounds.rowSourceWeight
  /-- The cached maximum face threshold across every original cell. -/ faceIndex : Nat
  /-- The face threshold is the exact maximum of the retained column thresholds. -/ face_eq : faceIndex = rows.maximum
    FamilyBounds.rowFaceWeight

constructive_injectivity PreOwnerQueries

/-- Build all original cell-query certificates once and cache their common source and face thresholds. -/
@[expose] def PreOwnerQueries.build (occurrence : SurfaceOccurrence regular domains differential) (other
  : Differential genus)
    (target : Coordinate) :
      PreOwnerQueries occurrence other target :=
  let rows := DependentVector.ofFn (fun column => DependentVector.ofFn
    (fun row => CellQuery.build occurrence other column
      row target))
  ⟨rows, rows.maximum FamilyBounds.rowSourceWeight, rfl, rows.maximum
    FamilyBounds.rowFaceWeight, rfl⟩

/-- The retained complete query bank bounds every original fragment trace error at paid source and face stages. -/
theorem PreOwnerQueries.accurate {requested : Coordinate} (queries :
  PreOwnerQueries occurrence other requested)
    (positive : 0 < requested) (sourcePaid : queries.sourceMinimum ≤ minimum)
    {later : Nat} (facePaid : queries.faceIndex ≤ later)
    {entry : SourceEntry plan sample otherSample fine} (piece : PairedFragmentQueries.Fragment
      entry) : PairedFragmentArea.traceError entry piece later ≤ requested := by
  have sourceLe := (DependentVector.get_le_maximum
    FamilyBounds.cellSourceWeight (queries.rows.get piece.column)
    piece.row).trans
    ((DependentVector.get_le_maximum FamilyBounds.rowSourceWeight
      queries.rows piece.column).trans
      (queries.source_eq.symm.trans_le sourcePaid))
  have faceLe := (DependentVector.get_le_maximum
    FamilyBounds.cellFaceWeight (queries.rows.get piece.column)
    piece.row).trans
    ((DependentVector.get_le_maximum FamilyBounds.rowFaceWeight
      queries.rows piece.column).trans
      (queries.face_eq.symm.trans_le facePaid))
  exact ((queries.rows.get piece.column).get piece.row).accurate piece positive sourceLe faceLe

set_option genInjectivity false in
/-- Acquire both differentials at one certified stage. The retained shared face banks, rather than separately acquired
local primitives, own the values. -/
structure OwnerFaceAcquisition {requested tolerance junctionTolerance : Coordinate}
    (queries : PreOwnerQueries occurrence other
      requested)
    (owners : OwnerRequest occurrence other tolerance)
    (junctionOwners : OwnerRequest occurrence other junctionTolerance) (floor : Nat) where
  /-- The shared acquisition stage paying queries, piece owners, junction owners and floor. -/ index : Nat
  /-- The shared stage is the exact maximum of the four original thresholds. -/ index_eq : index = max floor (max
    queries.faceIndex (max owners.index junctionOwners.index))
  /-- The original first differential's face primitive bank at that stage. -/ first : FacePrimitiveBank
    differential index domains
  /-- The original second differential's face primitive bank at that same stage. -/ second :
    FacePrimitiveBank other index domains

constructive_injectivity OwnerFaceAcquisition

namespace OwnerFaceAcquisition
variable {requested tolerance junctionTolerance : Coordinate}
  {queries : PreOwnerQueries occurrence other
    requested}
  {owners : OwnerRequest occurrence other
    tolerance}
  {junctionOwners : OwnerRequest
    occurrence other junctionTolerance} {floor : Nat}

/-- Acquire both original face primitive banks once at the shared paid stage. -/
@[expose] def build (queries : PreOwnerQueries
  occurrence other requested)
    (owners : OwnerRequest occurrence other tolerance)
    (junctionOwners : OwnerRequest occurrence other junctionTolerance) (floor : Nat) :
    OwnerFaceAcquisition queries owners junctionOwners
      floor :=
  let index := max floor (max queries.faceIndex (max owners.index junctionOwners.index))
  ⟨index, rfl, FacePrimitiveBank.build differential index domains, FacePrimitiveBank.build other index domains⟩

/-- The requested acquisition floor is paid at the retained stage. -/
theorem floor_le (acquired : OwnerFaceAcquisition
  queries owners junctionOwners floor) : floor ≤ acquired.index :=
  acquired.index_eq ▸ Data.Nat.Order.le_max_left _ _

/-- The retained query threshold is paid at the acquisition stage. -/
theorem queries_le (acquired : OwnerFaceAcquisition
  queries owners junctionOwners floor) : queries.faceIndex ≤ acquired.index :=
  acquired.index_eq ▸ (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The original physical-piece owner threshold is paid at the acquisition stage. -/
theorem owners_le (acquired : OwnerFaceAcquisition
  queries owners junctionOwners floor) : owners.index ≤ acquired.index :=
  acquired.index_eq ▸ (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans
    (Data.Nat.Order.le_max_right _ _))

/-- The original owner-junction threshold is paid at the acquisition stage. -/
theorem junctions_le (acquired : OwnerFaceAcquisition
  queries owners junctionOwners floor) : junctionOwners.index ≤ acquired.index :=
  acquired.index_eq ▸ (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans
    (Data.Nat.Order.le_max_right _ _))

/-- Read the first differential's original shared face data with its retained domain alignment. -/
@[expose] def firstData (acquired : OwnerFaceAcquisition
  queries owners junctionOwners floor) : FirstData occurrence acquired.index :=
  occurrence.compared.sharedData acquired.first occurrence.aligned

/-- Read the second differential's original shared face data with its retained recast alignment. -/
@[expose] def secondData (acquired :
  OwnerFaceAcquisition queries owners junctionOwners
  floor) : SecondData occurrence other acquired.index :=
  (occurrence.recastComparison other).sharedData acquired.second (occurrence.recastComparison_aligned other)

end OwnerFaceAcquisition

/-- Retain the already prepared covers and both grid budgets when selecting a new source floor. No source primitive has
been evaluated by this adapter. -/
@[expose] def withMinimum (plan : PairedSourcePlan occurrence other target minimum) (next : Nat)
  :
    PairedSourcePlan occurrence other target next :=
  let floor := max next (max plan.first.minimumIndex plan.second.minimumIndex)
  ⟨plan.positive, plan.first, plan.second, floor, rfl,
    PairedParentRequest.Request.build regular other
      plan.parents.left plan.parents.right plan.parents.proper (target / 4)
      (Field.div_pos_direct plan.positive (by decide)) floor⟩

/-- Changing the source floor preserves the original retained parent slope. -/
theorem withMinimum_slope (plan : PairedSourcePlan occurrence other target minimum) (next : Nat)
  :
    (FamilyBounds.withMinimum plan next).parents.slope =
      plan.parents.slope := plan.parents.slope_eq.symm

set_option genInjectivity false in
/-- Both parity-aware cap primitives are sampled at the same computed source stage. The supplied floor can synchronize
other retained requests. -/
structure SourceCapSamples (plan : PairedSourcePlan occurrence other target minimum) (floor :
  Nat) where
  /-- The common cap sampling stage for both original differentials. -/ index : Nat
  /-- The sample stage is the exact maximum of the requested floor and original source plan stage. -/ index_eq : index =
    max floor plan.index
  /-- The retained first differential's parity-aware cap sample. -/ first : Primitives.Sample cap differential index
    collar.box
  /-- The retained second differential's parity-aware cap sample at the same stage. -/ second : Primitives.Sample cap
    other index collar.box

constructive_injectivity SourceCapSamples

namespace SourceCapSamples
variable {floor : Nat}

/-- Acquire both original cap primitive samples at the common source-plan stage. -/
@[expose] def build (plan : PairedSourcePlan occurrence other target minimum) (floor : Nat) :
  SourceCapSamples plan floor :=
  let index := max floor plan.index
  ⟨index, rfl, Primitives.Sample.build cap differential index collar.box,
    Primitives.Sample.build cap other index collar.box⟩

/-- The requested source floor is paid at the retained cap sample stage. -/
theorem floor_le (samples : SourceCapSamples plan floor)
  : floor ≤ samples.index :=
  samples.index_eq ▸ Data.Nat.Order.le_max_left _ _

/-- The original source plan threshold is paid at the retained cap sample stage. -/
theorem plan_le (samples : SourceCapSamples plan floor)
  : plan.index ≤ samples.index :=
  samples.index_eq ▸ Data.Nat.Order.le_max_right _ _

/-- The original paired-parent request threshold is paid at the retained cap sample stage. -/
theorem parents_le (samples : SourceCapSamples plan
  floor) : plan.parents.index ≤ samples.index :=
  (Data.Nat.Order.le_max_left _ _).trans samples.plan_le

end SourceCapSamples

/-- The maximum point-movement bound of the original retained prepared parents. -/
@[expose] def preOwnerMovement (occurrence : SurfaceOccurrence regular domains differential) :
  Coordinate :=
  PairedFragmentBlocks.maximum (fun parent => parent.edge.pointMovement) occurrence.compared.entered.cache.parents

set_option genInjectivity false in
/-- Coefficients selected from retained preparation, before source or owner primitive evaluation. -/
structure PreOwnerBounds (plan : PairedSourcePlan occurrence other target minimum) where
  /-- The cached original per-column query-density maxima. -/ queryRows : List Coordinate
  /-- The cached rows are exactly the original pre-acquisition query-density rows. -/ rows_eq : queryRows =
    FamilyBounds.preOwnerQueryRows occurrence other
  /-- The cached maximum query-density bound across the original face cells. -/ query : Coordinate
  /-- The query-density cache is the maximum of the retained row bounds. -/ query_eq : query =
    PairedFragmentBlocks.maximum id queryRows
  /-- The cached maximum movement bound of the original parent edges. -/ movement : Coordinate
  /-- The movement cache is exactly the original retained-parent maximum. -/ movement_eq : movement =
    FamilyBounds.preOwnerMovement occurrence
  /-- The cached uniform trace density from the original query, movement and source slope bounds. -/ density :
    Coordinate
  /-- The density cache is twice the retained query-movement product plus original parent slope. -/ density_eq : density
    = 2 * (query * movement + plan.parents.slope)
  /-- The retained uniform density is nonnegative. -/ density_nonnegative : 0 ≤ density

constructive_injectivity PreOwnerBounds

/-- Cache the original query-density and parent-movement maxima and their resulting nonnegative trace density. -/
@[expose] def PreOwnerBounds.build (plan : PairedSourcePlan occurrence other target minimum) :
  PreOwnerBounds plan := by
  let rows := FamilyBounds.preOwnerQueryRows occurrence other
  let query := PairedFragmentBlocks.maximum id rows
  let movement := FamilyBounds.preOwnerMovement occurrence
  exact ⟨rows, rfl, query, rfl, movement, rfl, 2 * (query * movement + plan.parents.slope), rfl,
    Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (Arithmetic.mul_nonneg_direct (PairedFragmentBlocks.maximum_nonnegative ..)
        (PairedFragmentBlocks.maximum_nonnegative ..))
        plan.parents.slope_nonnegative)⟩

/-- Reuse the cached coefficients unchanged when the source floor is set. -/
@[expose] def PreOwnerBounds.withMinimum (bounds :
  PreOwnerBounds plan) (next : Nat) :
  PreOwnerBounds
  (FamilyBounds.withMinimum plan next) :=
  ⟨bounds.queryRows, bounds.rows_eq, bounds.query, bounds.query_eq, bounds.movement, bounds.movement_eq,
    bounds.density, bounds.density_eq.trans
      (congrArg (fun slope => 2 * (bounds.query * bounds.movement + slope))
        (FamilyBounds.withMinimum_slope plan next).symm),
    bounds.density_nonnegative⟩

/-- Each retained source entry's density is bounded by its original paired-parent slope. -/
theorem sourceDensity_le_slope (evaluated : ParentEvaluation plan sample otherSample fine)
    {entry : SourceEntry plan sample otherSample fine} (member : entry ∈ evaluated.retained) :
    PairedFragmentValues.sourceDensity entry ≤ plan.parents.slope := by
  have present := Map.mem_map_of_mem (f := fun entry : SourceEntry plan sample otherSample fine =>
    entry.plan) member
  have retained := Eq.mp (congrArg (fun plans => entry.plan ∈ plans) evaluated.plans_eq) present
  have bounded := plan.parents.plan_bounds entry.plan retained
  exact Basic.max_le bounded.1 bounded.2

/-- The cached pre-acquisition density bounds every original retained fragment at every later face index. -/
theorem PreOwnerBounds.density_bound (bounds :
  PreOwnerBounds plan) (evaluated :
  ParentEvaluation plan sample otherSample fine)
    {entry : SourceEntry plan sample otherSample fine} (member : entry ∈ evaluated.retained)
    (piece : PairedFragmentQueries.Fragment entry) (later : Nat) : PairedFragmentArea.traceDensity entry piece later ≤
      bounds.density := by
  have row := PairedFragmentBlocks.le_maximum (value := id) (Purelib.Data.List.OfFn.Basic.mem_ofFn.mpr ⟨piece.row, rfl⟩
    :
    FamilyBounds.preOwnerCellQuery occurrence other piece.column
      piece.row ∈ List.ofFn (FamilyBounds.preOwnerCellQuery
      occurrence other piece.column))
  have column := PairedFragmentBlocks.le_maximum (value := id) (Purelib.Data.List.OfFn.Basic.mem_ofFn.mpr ⟨piece.column,
    rfl⟩ :
    PairedFragmentBlocks.maximum id (List.ofFn
      (FamilyBounds.preOwnerCellQuery occurrence other piece.column))
      ∈ FamilyBounds.preOwnerQueryRows occurrence other)
  have queryLe : FamilyBounds.preOwnerCellQuery occurrence other
    piece.column piece.row ≤ bounds.query :=
    (row.trans column).trans_eq ((congrArg (PairedFragmentBlocks.maximum id) bounds.rows_eq.symm).trans
      bounds.query_eq.symm)
  have uniform := (PairedFragmentArea.uniformFragmentBounds entry piece).query_bound later
  have queryBound : PairedFragmentValues.queryDensity entry piece later ≤ bounds.query := uniform.trans queryLe
  have parentMember := Map.mem_map_of_mem
    (f := fun entry : SourceEntry plan sample otherSample fine => entry.plan.parent) member
  have present := Eq.mp (congrArg (fun parents => entry.plan.parent ∈ parents)
    (Evaluation.source_parents evaluated)) parentMember
  have movementBound : entry.plan.parent.edge.pointMovement ≤ bounds.movement :=
    (PairedFragmentBlocks.le_maximum (value := fun parent : PreparedSubdivisionModelCore.CenteredEdge curve differential
      => parent.edge.pointMovement) present).trans_eq bounds.movement_eq.symm
  have queryNonnegative : 0 ≤ bounds.query := (PairedFragmentArea.queryDensity_nonnegative entry piece later).trans
    queryBound
  have weighted := (Arithmetic.mul_le_mul_of_nonneg_right_direct queryBound
    (Data.Gaussian.Norm.Basic.normSq_nonneg _)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct movementBound queryNonnegative)
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct weighted
      (FamilyBounds.sourceDensity_le_slope evaluated member)) (by
      decide : (0 : Coordinate) ≤ 2)).trans_eq bounds.density_eq.symm

/-- Discharge the cached owner error using the requests selected before face acquisition. Source magnitudes, trace
densities and query errors are derived from the actual retained fragments, uniformly at every later face index. -/
theorem JoinedFragmentFamily.error_lt_of_queries {Vertex : Type} {count : Nat}
    {values : Vertex → Stokes.PrimitivePoint}
    {traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex}
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (bounds : PreOwnerBounds plan) {requested :
      Coordinate} (positive : 0 < requested)
    (budget : FragmentAreaBudget bounds.density
      (JoinedFragmentFamily.familyLocalTarget (count + count + 1) plan.parents.slope requested))
    (queries : PreOwnerQueries occurrence other
      budget.tolerance)
    (sourcePaid : queries.sourceMinimum ≤ minimum) (facePaid : queries.faceIndex ≤ index)
    (allowances : ∀ fragment ∈ family.fragments, fragment.allowance ≤ 1)
    (owners : ∀ fragment ∈ family.fragments, fragment.budget.tolerance ≤ budget.tolerance) :
    family.error < requested :=
  family.error_lt_of_cap plan.parents.slope_nonnegative positive budget family.fragments_length allowances
    (fun fragment _ => FamilyBounds.sourceDensity_le_slope evaluated
      fragment.member)
    (fun fragment _ => bounds.density_bound evaluated fragment.member fragment.piece index)
    owners
    (fun fragment _ => queries.accurate budget.tolerance_positive sourcePaid facePaid fragment.piece)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds
