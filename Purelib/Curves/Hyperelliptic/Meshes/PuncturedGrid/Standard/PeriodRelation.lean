module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.FamilyReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalCut
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily
public import Purelib.Integration.Budget.WeightedPair
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Integration

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

public section

/-! Requested comparison of original standard A/B samples with the actual
weighted chord-period samples at one common stage. Both coefficient rows
allocate their component and synchronization errors internally. Physical
corrections stay explicit on the same canonical cochain and triangle bank. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow
    lifted integral index} {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {prepared : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutChordPrograms lifted source} {components :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples prepared.programs differential}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

set_option genInjectivity false in
/-- The original two-row period allocation and its primitive and synchronization requests.

Both retained integer coefficient rows pay their component errors on the same segment and domain banks. -/
structure PeriodRelationPreparation
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (minimum numericalFloor : Nat) (target : Fraction.Rational) : Type 3 where
  /-- The common component allowance paid by both original coefficient rows. -/ allocation :
    Budget.WeightedPair.TwoPeriodBudget periods.a.coefficients periods.b.coefficients target
  /-- The primitive-family request on the retained segments and domain bank. -/ budget :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.ofSegments segments domains differential)
    (Data.Vector.Basic.vectorOfFn (fun _ => allocation.component)) numericalFloor
  /-- The retained common-stage movement request for the actual component streams. -/ movement :
    Budget.SynchronizedSamples.StageRequest components.streams allocation.component (Data.Vector.Basic.vectorOfFn (fun _
    => minimum))

constructive_injectivity PeriodRelationPreparation

set_option genInjectivity false in
/-- The prepared standard and weighted chord-period readings on one retained common stage.

The cache preserves its two-row allocation, original family readings and actual sampled components. -/
structure PeriodRelationReadings
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (minimum numericalFloor : Nat) (target : Fraction.Rational) (extraPoints : List Gaussian.Basic.Canonical) : Type 3
      where
  /-- The retained two-row primitive and movement preparation. -/ preparation :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationPreparation periods segments domains
    minimum numericalFloor target
  /-- The original standard and chord-family readings with their physical corrections. -/ readings :
    FamilyReadings row preparation.budget
    preparation.movement.stages minimum ((target / 4) / 4) extraPoints
  /-- The cached component samples at the retained common stage. -/ common :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CommonStage readings components minimum

constructive_injectivity PeriodRelationReadings

namespace PeriodRelationReadings

variable {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared
  components}
  {segments : Data.Vector.DependentVector (fun entry =>
    Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period)}
  {minimum numericalFloor : Nat} {target : Fraction.Rational} {extraPoints : List Gaussian.Basic.Canonical}

/-- Allocate both original period rows and prepare their component and synchronization requests. -/
@[expose] def prepare (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span
  prepared components)
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (minimum numericalFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationPreparation periods segments domains
      minimum numericalFloor target :=
  let allocation := Budget.WeightedPair.TwoPeriodBudget.build periods.a.coefficients periods.b.coefficients target
    positive
  let budget := Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget.build
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.ofSegments segments domains differential)
    (Data.Vector.Basic.vectorOfFn (fun _ => allocation.component)) (fun entry => by
        rw [Data.Vector.Basic.vectorOfFn_apply];
        exact allocation.component_positive) numericalFloor
  let movement := Budget.SynchronizedSamples.StageRequest.build components.streams allocation.component
    allocation.component_positive (Data.Vector.Basic.vectorOfFn (fun _ => minimum))
  ⟨allocation, budget, movement⟩

/-- The standard route preparation retains the chord family's own floors. -/
@[expose] def StandardPreparation
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationPreparation periods segments
      domains minimum numericalFloor target)
    (charts : Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests.RouteRequests preparation.budget) (extraPoints :
      List Gaussian.Basic.Canonical) :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings.Preparation row differential
    minimum ((target / 4) / 4) domains extraPoints
    (max preparation.budget.index charts.index)

/-- Read the retained standard and chord families from one supplied sufficiently late numerical bank, then cache their
common-stage components. -/
@[expose] def readWith
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationPreparation periods segments
      domains minimum numericalFloor target)
    (charts : Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests.RouteRequests preparation.budget)
    (standard : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.StandardPreparation
      preparation charts extraPoints)
    {stage : Nat} (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains)
    (later : standard.index ≤ stage) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments domains minimum
      numericalFloor target extraPoints :=
  let readings := FamilyReadings.readWith row
    preparation.budget preparation.movement.stages minimum ((target / 4) / 4)
    extraPoints charts standard numerics later
  ⟨preparation, readings, Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.commonSamples readings components
    minimum⟩

/-- The period-relation readings retain the supplied numerical stage and primitive bank with the original family floors.
-/
@[expose] def SharedAt
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints)
    {stage : Nat} (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains) : Prop :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings.SharedAt
    request.readings.standard numerics
    (max request.preparation.budget.index request.readings.charts.index)

/-- Reading from the supplied numerical bank preserves its exact stage and bank ownership. -/
theorem readWith_shared
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationPreparation periods segments
      domains minimum numericalFloor target)
    (charts : Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests.RouteRequests preparation.budget)
    (standard : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.StandardPreparation
      preparation charts extraPoints)
    {stage : Nat} (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains)
    (later : standard.index ≤ stage) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.SharedAt
      (Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.readWith preparation charts
      standard numerics later) numerics :=
  FamilyReadings.readWith_shared row preparation.budget
    preparation.movement.stages minimum ((target / 4) / 4)
    extraPoints charts standard numerics later

/-- Transport an existing triangle cache along equal stages and certified bank identity, preserving its value vector. -/
@[expose] def transportTriangles {before after : Nat}
    {original : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) before domains}
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings original lifted.mesh)
    (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) after domains)
    (sameIndex : before = after) (sameBank : HEq original numerics) :
    { result : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings numerics lifted.mesh //
      result.values = triangles.values } := by
  cases sameIndex
  cases eq_of_heq sameBank
  exact ⟨triangles, rfl⟩

/-- Transport the retained triangle cache along certified bank ownership.
The executable vector is returned unchanged, not rebuilt from its specification. -/
@[expose] def sharedTriangles
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints)
    {stage : Nat} (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.SharedAt request
      numerics) :
    { triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings numerics lifted.mesh //
      triangles.values = request.readings.standard.triangles.values } :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.transportTriangles
    request.readings.standard.triangles numerics shared.1 shared.2.1

/-- Prepare the two-row relation and acquire its original shared numerical and component caches.

The construction uses the actual coefficient allocation and standard chart threshold, preserving all supplied segment
and domain owners. -/
@[expose] def build (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span
  prepared components)
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (minimum numericalFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (extraPoints : List Gaussian := []) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments domains minimum
      numericalFloor target extraPoints :=
  let preparation := Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.prepare periods
    segments domains minimum numericalFloor target positive
  let positiveQuarter := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  let charts := Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests.RouteRequests.build preparation.budget
  let standard := Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings.prepare row
    differential minimum ((target / 4) / 4)
    (Fraction.Order.Field.div_pos_direct positiveQuarter (by decide)) domains extraPoints
    (max preparation.budget.index charts.index)
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.readWith preparation charts standard
    (Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build
      (Periods.PeriodMatrix.standardDifferential differential) standard.index domains) le_rfl

set_option genInjectivity false in
/-- Two scalar readings with their exact sample specifications. -/
structure CachedPeriodPair (aSample bSample : Gaussian.Basic.Canonical) where
  /-- The cached original A-period sample. -/ aValue : Gaussian.Basic.Canonical
  /-- The cached original B-period sample. -/ bValue : Gaussian.Basic.Canonical
  /-- The cached A-value equals its original specified sample. -/ a_sample_eq : aValue = aSample
  /-- The cached B-value equals its original specified sample. -/ b_sample_eq : bValue = bSample

constructive_injectivity CachedPeriodPair

/-- Cached integer combinations of the already sampled components. -/
@[expose] def Values
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints) :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.CachedPeriodPair
    (periods.a.approximation.sample request.common.common.stage)
    (periods.b.approximation.sample request.common.common.stage)

/-- Cache both integer combinations of the already sampled common-stage components with their original sample
equalities. -/
@[expose] def cache
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints) :
      Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values request :=
  ⟨periods.a.coefficients.combine request.common.common.values,
    periods.b.coefficients.combine request.common.common.values,
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.cached_weighted_eq request.common periods.a,
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.cached_weighted_eq request.common periods.b⟩

/-- The coefficient charge of the constant component vector equals the charge of its scalar value. -/
private theorem constant_charge {count : Nat} {weights : Data.Vector Int count}
    (coefficients : Periods.WeightedPeriods.Coefficients weights) (component : Fraction.Rational) :
    coefficients.charge (fun entry => 2 * (4 * (Data.Vector.Basic.vectorOfFn (fun _ : Fin count => component)) entry +
      component)) =
      coefficients.charge (fun _ => 2 * (4 * component + component)) := open Purelib.Algebra in by
  unfold Periods.WeightedPeriods.Coefficients.charge
  apply congrArg (coefficients.countValue * ·)
  apply FiniteSum.Fin.sumFin_congr
  intro entry
  dsimp only
  rw [Data.Vector.Basic.vectorOfFn_apply]

/-- The original weighted A-chain reading meets its allocated quarter-target error at the retained common stage. -/
@[expose] def AWeightedAccurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Chord.Spanning.CutCycleChain.edgeValue periods.a.chain
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.readings.standard.triangles.values) -
      periods.a.approximation.sample request.common.common.stage) < target / 4

/-- The first retained coefficient row pays the weighted A-chain comparison at the common cached stage. -/
theorem a_weighted_accurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.AWeightedAccurate request := by
  have bound := Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.weighted_common_bound (budget :=
    request.preparation.budget)
    (sampleFloor := minimum) segments request.preparation.movement request.readings request.common periods.a
  exact bound.trans_lt
    ((Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.constant_charge
    periods.a.coefficients request.preparation.allocation.component).trans_lt
    request.preparation.allocation.first_paid)

/-- The original weighted B-chain reading meets its allocated quarter-target error at the retained common stage. -/
@[expose] def BWeightedAccurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Chord.Spanning.CutCycleChain.edgeValue periods.b.chain
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.readings.standard.triangles.values) -
      periods.b.approximation.sample request.common.common.stage) < target / 4

/-- The second retained coefficient row pays the weighted B-chain comparison at the common cached stage. -/
theorem b_weighted_accurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.BWeightedAccurate request := by
  have bound := Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.weighted_common_bound (budget :=
    request.preparation.budget)
    (sampleFloor := minimum) segments request.preparation.movement request.readings request.common periods.b
  exact bound.trans_lt
    ((Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.constant_charge
    periods.b.coefficients request.preparation.allocation.component).trans_lt
    request.preparation.allocation.last_paid)

/-- Two quarter-target comparisons through the same chain yield the full-target standard versus corrected weighted
comparison. -/
private theorem combine {chain physical standard weighted : Gaussian.Basic.Canonical} {target : Fraction.Rational}
    (standardError : Data.Gaussian.Norm.Basic.normSq (chain + physical - standard) < target / 4)
    (weightedError : Data.Gaussian.Norm.Basic.normSq (chain - weighted) < target / 4) :
    Data.Gaussian.Norm.Basic.normSq (standard - (weighted + physical)) < target := by
  have first : Data.Gaussian.Norm.Basic.normSq (-(chain + physical - standard)) < target / 4 := by
    rw [Gaussian.Norm.Basic.normSq_neg]
    exact standardError
  rw [show standard - (weighted + physical) = -(chain + physical - standard) + (chain - weighted) by ring1]
  have bound := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct first weightedError))
  exact bound.trans_eq ((by ring1 : 2 * (target / 4 + target / 4) = (target / 4) * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- Replace a weighted sample by its equal retained cached value without changing the physical correction or bound. -/
private theorem replace_weighted {standard physical weighted cached : Gaussian.Basic.Canonical} {target :
  Fraction.Rational}
    (equal : cached = weighted) (bound : Data.Gaussian.Norm.Basic.normSq (standard - (weighted + physical)) <
      target) :
    Data.Gaussian.Norm.Basic.normSq (standard - (cached + physical)) < target :=
  (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (standard - (value + physical))) equal).trans_lt bound

variable
  {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
  (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
  (period : Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodRow curve)
  (periodEq : period = (Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
    branches).rows index)
  {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal index
      period periodEq).span prepared components}

/-- Original standard A and the actual weighted chord-period sample
agree below the request after retaining the certified physical correction.
No component bound, common-stage condition, or transport equality is supplied. -/
@[expose] def APeriodAccurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints) : Prop :=
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.readings.standard.triangles.values
    Data.Gaussian.Norm.Basic.normSq ((((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve
      branches).aProgram differential index).integral.model
        request.common.common.stage).integralSample -
      (periods.a.approximation.sample request.common.common.stage +
        Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine periods.aGeometry.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))))) < target

/-- The original standard A-period agrees within the target with the weighted chord sample plus its retained physical
correction. -/
theorem a_period_accurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.APeriodAccurate normal period
      periodEq request :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.combine
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalCut.a_chord_chain_accurate normal period periodEq periods
    request.readings.standard _
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.common_standard_later request.common))
      request.a_weighted_accurate

/-- Original standard B and the actual weighted chord-period sample
agree below the request after retaining the certified physical correction.
No component bound, common-stage condition, or transport equality is supplied. -/
@[expose] def BPeriodAccurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints) : Prop :=
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.readings.standard.triangles.values
    Data.Gaussian.Norm.Basic.normSq ((((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve
      branches).bProgram differential index).integral.model
        request.common.common.stage).integralSample -
      (periods.b.approximation.sample request.common.common.stage +
        Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine periods.bGeometry.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))))) < target

/-- The original standard B-period agrees within the target with the weighted chord sample plus its retained physical
correction. -/
theorem b_period_accurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.BPeriodAccurate normal period
      periodEq request :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.combine
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalCut.b_chord_chain_accurate normal period periodEq periods
    request.readings.standard _
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.common_standard_later request.common))
      request.b_weighted_accurate

/-- The original standard A-period meets the target against the cached A-value and its actual physical correction. -/
@[expose] def ACachedAccurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values request) : Prop
      :=
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.readings.standard.triangles.values
    Data.Gaussian.Norm.Basic.normSq ((((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve
      branches).aProgram differential index).integral.model
        request.common.common.stage).integralSample -
      (values.aValue + Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine periods.aGeometry.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))))) < target

/-- The retained cached A-value preserves the original corrected period comparison. -/
theorem a_cached_accurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values request) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.ACachedAccurate normal period
      periodEq request values :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.replace_weighted values.a_sample_eq
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.a_period_accurate normal period
    periodEq request)

/-- The original standard B-period meets the target against the cached B-value and its actual physical correction. -/
@[expose] def BCachedAccurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values request) : Prop
      :=
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.readings.standard.triangles.values
    Data.Gaussian.Norm.Basic.normSq ((((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve
      branches).bProgram differential index).integral.model
        request.common.common.stage).integralSample -
      (values.bValue + Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine periods.bGeometry.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))))) < target

/-- The retained cached B-value preserves the original corrected period comparison. -/
theorem b_cached_accurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values request) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.BCachedAccurate normal period
      periodEq request values :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.replace_weighted values.b_sample_eq
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.b_period_accurate normal period
    periodEq request)

end PeriodRelationReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation
