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

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid

open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

open Purelib.Approximation.Rational.Budget

open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

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

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered} (prepared :
    Paired.PeriodPrograms.Prepared paired)
  {fine : Geometry.Grid.ClearGrid curve.polynomial (Branches.Cuts.Ambient curve)}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid fine)
  {frames : SquareRoot.Grid.RootFrames fine} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : VertexBank fine)

/-- Scalar alias for the actual corrected A/B walks, keeping dependent
signatures compact without replacing their program ownership. -/
def resplitPeriodArea (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index : Fin genus => Path.BoundaryRibbon.area
    (SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (prepared.aWalk index).closed.walk (VertexBank.coordinate_onGrid
        lifted.vertices _)) newSheet))
    (SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (prepared.bWalk index).closed.walk (VertexBank.coordinate_onGrid
        lifted.vertices _)) newSheet)))

/-- The energy commutator boundary of the resplit A/B word values is exactly
twice the resplit Hermitian A/B area. This is the exact bridge from the
Hermitian period-area comparison to the two-differential energy boundary. -/
theorem energyBoundaryArea_resplitPeriodArea (newSheet : Fin 2)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    Energy.Polygon.energyBoundaryArea
        (Vector.Basic.vectorOfFn fun index : Fin genus =>
          SewingRetraction.wordValue value (edges.indexedEdges vertices
            (included.resplit (prepared.aWalk index).closed.walk
              (VertexBank.coordinate_onGrid lifted.vertices _)) newSheet))
        (Vector.Basic.vectorOfFn fun index : Fin genus =>
          SewingRetraction.wordValue value (edges.indexedEdges vertices
            (included.resplit (prepared.bWalk index).closed.walk
              (VertexBank.coordinate_onGrid lifted.vertices _)) newSheet)) =
      2 * OriginalPeriodArea.resplitPeriodArea prepared included edges vertices newSheet
        value := by
  unfold Energy.Polygon.energyBoundaryArea OriginalPeriodArea.resplitPeriodArea
  rw [← FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro cycle
  rw [Vector.Basic.vectorOfFn_apply,
    Vector.Basic.vectorOfFn_apply,
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
        (Vector.Basic.vectorOfFn fun index : Fin genus =>
          SewingRetraction.wordValue first (edges.indexedEdges vertices
            (included.resplit (prepared.aWalk index).closed.walk
              (VertexBank.coordinate_onGrid lifted.vertices _)) newSheet))
        (Vector.Basic.vectorOfFn fun index : Fin genus =>
          SewingRetraction.wordValue second (edges.indexedEdges vertices
            (included.resplit (prepared.bWalk index).closed.walk
              (VertexBank.coordinate_onGrid lifted.vertices _)) newSheet)) =
      2 * FiniteSum.Fin.sumFin (fun index : Fin genus =>
        Path.BoundaryRibbon.area
          (SewingRetraction.wordValue first (edges.indexedEdges vertices
            (included.resplit (prepared.aWalk index).closed.walk
              (VertexBank.coordinate_onGrid lifted.vertices _)) newSheet))
          (SewingRetraction.wordValue second (edges.indexedEdges vertices
            (included.resplit (prepared.bWalk index).closed.walk
              (VertexBank.coordinate_onGrid lifted.vertices _)) newSheet))) := by
  unfold Energy.Polygon.energyBoundaryArea
  rw [← FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro cycle
  rw [Vector.Basic.vectorOfFn_apply,
    Vector.Basic.vectorOfFn_apply,
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
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet
  Path.BoundaryRibbon.area (Path.Paired.Increments.total
    (Inclusion.PairedArea.resplitReadings included edges vertices bank newSheet value
    paired.split.pairs))
    (SewingRetraction.wordValue value ending +
      SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      (Branches.BranchCutLifts.otherSheet newSheet))) +
    OrderedBranchPolygons.terminalCross included edges vertices bank newSheet value
      paired.split.ending

variable {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation
  base.bank.toBranchCellBank} {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {differential : Differentials.Basic.Differential genus}

/-- Exact readback of the two cached polygon families into the original
corrected A/B pairing. This uses the actual ordered exterior compiler. -/
theorem original_polygons_period_area (newSheet : Fin 2) (excision :
  AllHoles.Excision.AllHoleExcision grid current)
    {fixed : Face.MagnitudeBank.FaceMagnitudeBank domains differential} {regularError
      branchError : Fraction.Rational} {floor : Nat}
    {stage : Nat} {shared : Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
    (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values) :
    let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    ∀ {regular : RegularRegionRequests fixed regularError
      floor compiled.regulars}
      {branch : BranchRegionRequests bank
        (OrderedBranchPolygons.branchSheet ordered newSheet) fixed branchError floor
        excision.entries},
      (regularSamples : RegularRegionRequests.Samples
        readings surface regular) →
      (branchSamples : BranchRegionRequests.Samples readings surface
        branch) →
      let value := CanonicalEdgeValues.edgeValuation current.mesh readings.values
      regularSamples.polygons + branchSamples.polygons =
        current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
          current.edges current.vertices newSheet value -
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms := by
  intro reference compiled regular branch regularSamples branchSamples value
  have formula :=
    Inclusion.OrderedBoundary.Ordered.Paired.Prepared.resplit_exterior_area_formula
    grid.shrunk.included current.edges current.vertices reference prepared
    newSheet compiled value (CanonicalEdgeValues.edgeValuation_reverse current.mesh
      readings.values)
  have regularRead := regularSamples.polygons_eq
  have branchRead := OrderedBranchPolygons.branch_polygons_eq paired newSheet excision
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
  AllHoles.Excision.AllHoleExcision grid current)
    (fixed : Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (positive : 0 < error) (floor : Nat) : Prop :=
    let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let part := Aggregate.perTerm error 2
    let partPositive := Aggregate.perTerm_positive positive 2
    let regular := RegularRegionRequests.build fixed
      (Aggregate.perTerm part compiled.regulars.length)
      (Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := BranchRegionRequests.build bank
      (OrderedBranchPolygons.branchSheet ordered newSheet) fixed
      (Aggregate.perTerm part excision.entries.length)
      (Aggregate.perTerm_positive partPositive _) floor excision.entries
    ∀ stage (shared : Face.PrimitiveData.FacePrimitiveBank differential stage
      domains) (readings : TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
      (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
        max regular.index branch.index ≤ stage →
      let regularSamples :=
        RegularRegionRequests.Samples.build readings
        surface regular
      let branchSamples := BranchRegionRequests.Samples.build
        readings surface branch
      let value := CanonicalEdgeValues.edgeValuation current.mesh readings.values
      let physical := current.edges.chainArea current.vertices value
        (grid.shrunk.included.resplit base.bank.exterior
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
          current.edges current.vertices newSheet value -
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms
      Gaussian.Norm.Basic.normSq (surface.boundaryArea - (regularSamples.corrections +
        branchSamples.corrections) - (physical + physical)) < error

/-- A computed all-later request for the corrected original A/B area
formula on the same Newton surface. There are no caller transport
equalities or unaccounted region areas. The remaining physical, sewing,
connector and ending corrections are named explicitly in the estimate. -/
theorem original_period_area_accurate (newSheet : Fin 2) (excision :
  AllHoles.Excision.AllHoleExcision grid current)
    (fixed : Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let part := Aggregate.perTerm error 2
    let partPositive := Aggregate.perTerm_positive positive 2
    let regular := RegularRegionRequests.build fixed
      (Aggregate.perTerm part compiled.regulars.length)
      (Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := BranchRegionRequests.build bank
      (OrderedBranchPolygons.branchSheet ordered newSheet) fixed
      (Aggregate.perTerm part excision.entries.length)
      (Aggregate.perTerm_positive partPositive _) floor excision.entries
    ∀ stage (shared : Face.PrimitiveData.FacePrimitiveBank differential stage
      domains) (readings : TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
      (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
        max regular.index branch.index ≤ stage →
      let regularSamples :=
        RegularRegionRequests.Samples.build readings
        surface regular
      let branchSamples := BranchRegionRequests.Samples.build
        readings surface branch
      let value := CanonicalEdgeValues.edgeValuation current.mesh readings.values
      let physical := current.edges.chainArea current.vertices value
        (grid.shrunk.included.resplit base.bank.exterior
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
          current.edges current.vertices newSheet value -
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms
      Gaussian.Norm.Basic.normSq (surface.boundaryArea - (regularSamples.corrections +
        branchSamples.corrections) - (physical + physical)) < error := by
  intro reference compiled part partPositive regular branch stage shared readings surface later regularSamples
    branchSamples value physical
  have estimate := OriginalRegionsComparison.original_regions_accurate ordered newSheet
    (OrderedBranchPolygons.branchSheet ordered newSheet) excision fixed error positive floor
    stage shared readings surface later
  have read := OriginalPeriodArea.original_polygons_period_area prepared newSheet excision
    readings surface regularSamples branchSamples
  exact (congrArg (fun polygon => Gaussian.Norm.Basic.normSq
    (surface.boundaryArea - (regularSamples.corrections + branchSamples.corrections) - (polygon + polygon)))
      read.symm).trans_lt estimate

/-- Build the original magnitude bank and bound the corrected original A/B period area at every sufficient stage.

The comparison consumes the same retained Newton surface and keeps its physical boundary, sewing, connector and terminal
corrections explicitly. -/
theorem original_period_area_accurate_automatic (newSheet : Fin 2) (excision :
  AllHoles.Excision.AllHoleExcision grid current)
    (differential : Differentials.Basic.Differential genus) (error : Fraction.Rational) (positive : 0 <
      error) (floor : Nat) :
    let fixed : Face.MagnitudeBank.FaceMagnitudeBank domains differential :=
      Face.MagnitudeBank.FaceMagnitudeBank.build domains differential
    let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let part := Aggregate.perTerm error 2
    let partPositive := Aggregate.perTerm_positive positive 2
    let regular := RegularRegionRequests.build fixed
      (Aggregate.perTerm part compiled.regulars.length)
      (Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := BranchRegionRequests.build bank
      (OrderedBranchPolygons.branchSheet ordered newSheet) fixed
      (Aggregate.perTerm part excision.entries.length)
      (Aggregate.perTerm_positive partPositive _) floor excision.entries
    ∀ stage (shared : Face.PrimitiveData.FacePrimitiveBank differential stage
      domains) (readings : TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
      (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
        max regular.index branch.index ≤ stage →
      let regularSamples :=
        RegularRegionRequests.Samples.build readings
        surface regular
      let branchSamples := BranchRegionRequests.Samples.build
        readings surface branch
      let value := CanonicalEdgeValues.edgeValuation current.mesh readings.values
      let physical := current.edges.chainArea current.vertices value
        (grid.shrunk.included.resplit base.bank.exterior
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
          current.edges current.vertices newSheet value -
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms
      Gaussian.Norm.Basic.normSq (surface.boundaryArea - (regularSamples.corrections +
        branchSamples.corrections) - (physical + physical)) < error := by
  intro fixed reference compiled part partPositive regular branch stage shared readings surface later
  exact OriginalPeriodArea.original_period_area_accurate prepared newSheet excision fixed
    error positive floor
    stage shared readings surface later

/-- The existing owner certificate, specialized before any curve builders
are substituted into its dependent telescope. -/
private theorem periodAreaEstimate_accurate (newSheet : Fin 2) (excision :
  AllHoles.Excision.AllHoleExcision grid current)
    (fixed : Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    periodAreaEstimate (grid := grid) (current := current) (domains := domains)
      prepared newSheet excision fixed error positive floor := by
  exact OriginalPeriodArea.original_period_area_accurate
    (curve := curve) (branches := branches) (higher := higher)
    (base := base) (lifted := lifted) (bank := bank) (ordered := ordered) (paired := paired)
    (grid := grid) (current := current) (domains := domains)
    prepared newSheet excision fixed error positive floor

/-- Construct the retained original period-area comparison from the curve and its branch isolation data.

The framed grid, ordered paired programs, Newton refinement, domain bank and magnitude bank are built once and remain
the owners of the resulting all-later estimate. -/
theorem original_period_area_accurate_ofCurve (newSheet : Fin 2) (differential :
  Differentials.Basic.Differential genus)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat)
    {target radius : Fraction.Rational} (targetPositive : 0 < target) (radiusPositive : 0 < radius) :
    let base := Meshes.FramedPuncturedGrid.ofData curve branches higher
    let lifted := Meshes.LiftedPuncturedGrid.build base
    let bank := BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.build lifted
    let ordered := BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.ordered bank
      0
    let paired := OrderedBranchPairs.Ordered.paired ordered
    let prepared := Paired.PeriodPrograms.prepare paired
    let grid := RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid.build
      (RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation.build base.bank.toBranchCellBank)
      targetPositive radiusPositive
    let current := Meshes.LiftedPuncturedGrid.build grid.punctured
    let domains := Face.DomainBanks.FaceDomainBank.build current.frames
      grid.faces.regulars
    let excision := AllHoles.Excision.AllHoleExcision.build grid current
    let fixed : Face.MagnitudeBank.FaceMagnitudeBank domains differential :=
      Face.MagnitudeBank.FaceMagnitudeBank.build domains differential
    periodAreaEstimate (grid := grid) (current := current) (domains := domains)
      prepared newSheet excision fixed error positive floor := by
  intro base lifted bank ordered paired prepared grid current domains excision fixed
  exact periodAreaEstimate_accurate
    (curve := curve) (branches := branches) (higher := higher)
    (base := base) (lifted := lifted) (bank := bank) (ordered := ordered) (paired := paired)
    (grid := grid) (current := current) (domains := domains)
    prepared newSheet excision fixed error positive floor

end Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
