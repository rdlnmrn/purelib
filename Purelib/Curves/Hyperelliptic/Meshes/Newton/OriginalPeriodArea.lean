module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Paired.Increments
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalRegionsComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! The original corrected A/B area pairing consumes the actual shared
Newton surface comparison. Physical and terminal corrections stay visible. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} (prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  {fine : Polynomial.Geometry.Grid.ClearGrid curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid fine)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames fine} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank fine)

/-- Scalar alias for the actual corrected A/B walks, keeping dependent
signatures compact without replacing their program ownership. -/
def resplitPeriodArea (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index : Fin genus => Path.BoundaryRibbon.area
    (Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (prepared.aWalk index).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
        lifted.vertices _)) newSheet))
    (Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (prepared.bWalk index).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
        lifted.vertices _)) newSheet)))

/-- The energy commutator boundary of the resplit A/B word values is exactly
twice the resplit Hermitian A/B area. This is the exact bridge from the
Hermitian period-area comparison to the two-differential energy boundary. -/
theorem energyBoundaryArea_resplitPeriodArea (newSheet : Fin 2)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    Energy.Polygon.energyBoundaryArea
        (Data.Vector.Basic.vectorOfFn fun index : Fin genus =>
          Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
            (included.resplit (prepared.aWalk index).closed.walk
              (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid lifted.vertices _)) newSheet))
        (Data.Vector.Basic.vectorOfFn fun index : Fin genus =>
          Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
            (included.resplit (prepared.bWalk index).closed.walk
              (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid lifted.vertices _)) newSheet)) =
      2 * Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared included edges vertices newSheet
        value := by
  unfold Energy.Polygon.energyBoundaryArea Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea
  rw [← FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro cycle
  rw [Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    Topology.Polygon.Stokes.commutatorBoundaryArea_eq]
  unfold Energy.Polygon.energyPrimitivePoint Path.BoundaryRibbon.area
  ring1

/-- Polarized form of the energy/resplit bridge: the energy commutator
boundary of two resplit word-value families is exactly twice the sum of the
corresponding Hermitian word areas. This is the quadratic form consumed by
`close` for a coefficient combination. -/
theorem energyBoundaryArea_wordValues (newSheet : Fin 2)
    (first second : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    Energy.Polygon.energyBoundaryArea
        (Data.Vector.Basic.vectorOfFn fun index : Fin genus =>
          Topology.Surface.Sewing.SewingRetraction.wordValue first (edges.indexedEdges vertices
            (included.resplit (prepared.aWalk index).closed.walk
              (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid lifted.vertices _)) newSheet))
        (Data.Vector.Basic.vectorOfFn fun index : Fin genus =>
          Topology.Surface.Sewing.SewingRetraction.wordValue second (edges.indexedEdges vertices
            (included.resplit (prepared.bWalk index).closed.walk
              (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid lifted.vertices _)) newSheet)) =
      2 * FiniteSum.Fin.sumFin (fun index : Fin genus =>
        Path.BoundaryRibbon.area
          (Topology.Surface.Sewing.SewingRetraction.wordValue first (edges.indexedEdges vertices
            (included.resplit (prepared.aWalk index).closed.walk
              (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid lifted.vertices _)) newSheet))
          (Topology.Surface.Sewing.SewingRetraction.wordValue second (edges.indexedEdges vertices
            (included.resplit (prepared.bWalk index).closed.walk
              (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid lifted.vertices _)) newSheet))) := by
  unfold Energy.Polygon.energyBoundaryArea
  rw [← FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro cycle
  rw [Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    Topology.Polygon.Stokes.commutatorBoundaryArea_eq]
  unfold Energy.Polygon.energyPrimitivePoint Path.BoundaryRibbon.area
  ring1

/-- Both terminal corrections in the ordered identity. The cross of the
ending word with the preceding total differs from the even ending's own
internal cross; both are retained. -/
def resplitEndCorrection (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical) : Gaussian :=
  let ending := edges.indexedEdges vertices
    (included.resplit (bank.loopProduct paired.split.ending.labels)
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet
  Path.BoundaryRibbon.area (Path.Paired.Increments.total
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitReadings included edges vertices bank newSheet value
    paired.split.pairs))
    (Topology.Surface.Sewing.SewingRetraction.wordValue value ending +
      Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      (Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet))) +
    Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.terminalCross included edges vertices bank newSheet value
      paired.split.ending

variable {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation
  base.bank.toBranchCellBank} {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- Exact readback of the two cached polygon families into the original
corrected A/B pairing. This uses the actual ordered exterior compiler. -/
theorem original_polygons_period_area (newSheet : Fin 2) (excision :
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    {fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential} {regularError
      branchError : Fraction.Rational} {floor : Nat}
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
    (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values) :
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    ∀ {regular : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed regularError
      floor compiled.regulars}
      {branch : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank
        (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) fixed branchError floor
        excision.entries},
      (regularSamples : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples
        readings surface regular) →
      (branchSamples : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings surface
        branch) →
      let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values
      regularSamples.polygons + branchSamples.polygons =
        current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
          current.edges current.vertices newSheet value -
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms := by
  intro reference compiled regular branch regularSamples branchSamples value
  have formula :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary.Ordered.Paired.Prepared.resplit_exterior_area_formula
    grid.shrunk.included current.edges current.vertices reference prepared
    newSheet compiled value (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh
      readings.values)
  have regularRead := regularSamples.polygons_eq
  have branchRead := Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branch_polygons_eq paired newSheet excision
    branchSamples
  have scalar (regular branch inner ending cross terminal connector regularTerm whole : Gaussian.Basic.Canonical)
      (regularEq : regular = regularTerm) (branchEq : branch = inner + ending - terminal)
      (wholeEq : whole = inner + ending + cross + (regularTerm + connector)) :
      regular + branch = whole - (cross + terminal) - connector := by
    rw [regularEq, branchEq, wholeEq]
    ring1
  exact scalar _ _ _ _ _ _ _ _ _ regularRead branchRead formula

/-- Exact proposition for the retained original period-area estimate. The
Newton owner, cached readings, samples, physical corrections and finite budget
are the same arguments as in `original_period_area_accurate`. -/
@[reducible] def periodAreaEstimate (newSheet : Fin 2) (excision :
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (positive : 0 < error) (floor : Nat) : Prop :=
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let part := Rational.Budget.Aggregate.perTerm error 2
    let partPositive := Rational.Budget.Aggregate.perTerm_positive positive 2
    let regular := Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.build fixed
      (Rational.Budget.Aggregate.perTerm part compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.build bank
      (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) fixed
      (Rational.Budget.Aggregate.perTerm part excision.entries.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor excision.entries
    ∀ stage (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains) (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
      (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
        max regular.index branch.index ≤ stage →
      let regularSamples :=
        Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples.build readings
        surface regular
      let branchSamples := Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples.build
        readings surface branch
      let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values
      let physical := current.edges.chainArea current.vertices value
        (grid.shrunk.included.resplit base.bank.exterior
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
          current.edges current.vertices newSheet value -
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms
      Data.Gaussian.Norm.Basic.normSq (surface.boundaryArea - (regularSamples.corrections +
        branchSamples.corrections) - (physical + physical)) < error

/-- A computed all-later request for the corrected original A/B area
formula on the same Newton surface. There are no caller transport
equalities or unaccounted region areas. The remaining physical, sewing,
connector and ending corrections are named explicitly in the estimate. -/
theorem original_period_area_accurate (newSheet : Fin 2) (excision :
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let part := Rational.Budget.Aggregate.perTerm error 2
    let partPositive := Rational.Budget.Aggregate.perTerm_positive positive 2
    let regular := Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.build fixed
      (Rational.Budget.Aggregate.perTerm part compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.build bank
      (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) fixed
      (Rational.Budget.Aggregate.perTerm part excision.entries.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor excision.entries
    ∀ stage (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains) (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
      (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
        max regular.index branch.index ≤ stage →
      let regularSamples :=
        Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples.build readings
        surface regular
      let branchSamples := Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples.build
        readings surface branch
      let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values
      let physical := current.edges.chainArea current.vertices value
        (grid.shrunk.included.resplit base.bank.exterior
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
          current.edges current.vertices newSheet value -
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms
      Data.Gaussian.Norm.Basic.normSq (surface.boundaryArea - (regularSamples.corrections +
        branchSamples.corrections) - (physical + physical)) < error := by
  intro reference compiled part partPositive regular branch stage shared readings surface later regularSamples
    branchSamples value physical
  have estimate := Hyperelliptic.Meshes.Newton.OriginalRegionsComparison.original_regions_accurate ordered newSheet
    (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) excision fixed error positive floor
    stage shared readings surface later
  have read := Hyperelliptic.Meshes.Newton.OriginalPeriodArea.original_polygons_period_area prepared newSheet excision
    readings surface regularSamples branchSamples
  exact (congrArg (fun polygon => Data.Gaussian.Norm.Basic.normSq
    (surface.boundaryArea - (regularSamples.corrections + branchSamples.corrections) - (polygon + polygon)))
      read.symm).trans_lt estimate

/-- Build the original magnitude bank and bound the corrected original A/B period area at every sufficient stage.

The comparison consumes the same retained Newton surface and keeps its physical boundary, sewing, connector and terminal
corrections explicitly. -/
theorem original_period_area_accurate_automatic (newSheet : Fin 2) (excision :
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (error : Fraction.Rational) (positive : 0 <
      error) (floor : Nat) :
    let fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential :=
      Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank.build domains differential
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let part := Rational.Budget.Aggregate.perTerm error 2
    let partPositive := Rational.Budget.Aggregate.perTerm_positive positive 2
    let regular := Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.build fixed
      (Rational.Budget.Aggregate.perTerm part compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.build bank
      (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) fixed
      (Rational.Budget.Aggregate.perTerm part excision.entries.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor excision.entries
    ∀ stage (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains) (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
      (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
        max regular.index branch.index ≤ stage →
      let regularSamples :=
        Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples.build readings
        surface regular
      let branchSamples := Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples.build
        readings surface branch
      let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values
      let physical := current.edges.chainArea current.vertices value
        (grid.shrunk.included.resplit base.bank.exterior
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
          current.edges current.vertices newSheet value -
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms
      Data.Gaussian.Norm.Basic.normSq (surface.boundaryArea - (regularSamples.corrections +
        branchSamples.corrections) - (physical + physical)) < error := by
  intro fixed reference compiled part partPositive regular branch stage shared readings surface later
  exact Hyperelliptic.Meshes.Newton.OriginalPeriodArea.original_period_area_accurate prepared newSheet excision fixed
    error positive floor
    stage shared readings surface later

/-- The existing owner certificate, specialized before any curve builders
are substituted into its dependent telescope. -/
private theorem periodAreaEstimate_accurate (newSheet : Fin 2) (excision :
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    periodAreaEstimate (grid := grid) (current := current) (domains := domains)
      prepared newSheet excision fixed error positive floor := by
  exact Hyperelliptic.Meshes.Newton.OriginalPeriodArea.original_period_area_accurate
    (curve := curve) (branches := branches) (higher := higher)
    (base := base) (lifted := lifted) (bank := bank) (ordered := ordered) (paired := paired)
    (grid := grid) (current := current) (domains := domains)
    prepared newSheet excision fixed error positive floor

/-- Construct the retained original period-area comparison from the curve and its branch isolation data.

The framed grid, ordered paired programs, Newton refinement, domain bank and magnitude bank are built once and remain
the owners of the resulting all-later estimate. -/
theorem original_period_area_accurate_ofCurve (newSheet : Fin 2) (differential :
  Hyperelliptic.Differentials.Basic.Differential genus)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat)
    {target radius : Fraction.Rational} (targetPositive : 0 < target) (radiusPositive : 0 < radius) :
    let base := Meshes.FramedPuncturedGrid.ofData curve branches higher
    let lifted := Meshes.LiftedPuncturedGrid.build base
    let bank := Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.build lifted
    let ordered := Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.ordered bank
      0
    let paired := Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.paired ordered
    let prepared := Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.prepare paired
    let grid := RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid.build
      (RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation.build base.bank.toBranchCellBank)
      targetPositive radiusPositive
    let current := Meshes.LiftedPuncturedGrid.build grid.punctured
    let domains := Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank.build current.frames
      grid.faces.regulars
    let excision := Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.build grid current
    let fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential :=
      Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank.build domains differential
    periodAreaEstimate (grid := grid) (current := current) (domains := domains)
      prepared newSheet excision fixed error positive floor := by
  intro base lifted bank ordered paired prepared grid current domains excision fixed
  exact periodAreaEstimate_accurate
    (curve := curve) (branches := branches) (higher := higher)
    (base := base) (lifted := lifted) (bank := bank) (ordered := ordered) (paired := paired)
    (grid := grid) (current := current) (domains := domains)
    prepared newSheet excision fixed error positive floor

end Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
