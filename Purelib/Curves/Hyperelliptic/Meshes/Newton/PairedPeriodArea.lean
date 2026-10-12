module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedRegionsComparison
import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib

public section

/-! The two cached polygon families read back to the polarization of the
actual resplit period identity, retaining every terminal and connector term. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedPeriodArea

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} (prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Integration in
open Purelib.Polynomial in
/-- The polygon readback concerns the original ordered A/B owner. In
particular, polarization does not discard the even ending's terminal cross. -/
theorem original_paired_polygons_period_area (newSheet : Fin 2) (excision :
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    {leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential}
      {rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential}
    {regularError branchError : Fraction.Rational} {floor : Nat}
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains} {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      rightDifferential stage domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
      current.cutPolygon.patch rightReadings.values) :
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    ∀ {regular : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed
      regularError floor compiled.regulars}
      {branch : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank
        (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) leftFixed rightFixed
        branchError floor excision.entries},
      (regularSamples : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples leftReadings
        rightReadings leftSurface rightSurface regular) →
      (branchSamples : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings
        rightReadings leftSurface rightSurface branch) →
      regularSamples.polygons + branchSamples.polygons =
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
            coefficient
        current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
          current.edges current.vertices newSheet value -
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms) := by
  intro reference compiled regular branch regularSamples branchSamples
  let first := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values
  let second := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values
  let branchWord := fun index => current.edges.indexedEdges current.vertices
    (grid.shrunk.included.resplit (bank.rows.get index).reference.walk
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet index)
  have regularRead := regularSamples.polygons_eq.trans
    (Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization.extract_word_sum first second (fun occurrence =>
      occurrence.word) compiled.regulars).symm
  have branchRead := branchSamples.polygons_eq.trans
    ((Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.Ordered.branch_entries_sum ordered excision
    (fun index => Path.PairedIncrementArea.area ((branchWord index).map (fun edge => (⟨first edge, second edge⟩ :
      Topology.Polygon.Stokes.PrimitivePoint))))).symm.trans
      (Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization.extract_word_sum first second branchWord
        ordered.prepared.labels).symm)
  rw [regularRead, branchRead]
  have combine : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
    coefficient => Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Mesh.RetracingWords.wordArea
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
    occurrence.word) compiled.regulars) +
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Geometry.Grid.CellBoundary.sumValues (fun index => Topology.Mesh.RetracingWords.wordArea
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
        (branchWord index)) ordered.prepared.labels) =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Mesh.RetracingWords.wordArea
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
        occurrence.word) compiled.regulars +
        Geometry.Grid.CellBoundary.sumValues (fun index => Topology.Mesh.RetracingWords.wordArea
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
          (branchWord index)) ordered.prepared.labels) := by
    unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
    ring1
  refine combine.trans (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr
    (fun coefficient => ?_))
  let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
    coefficient
  have anti := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix_reverse first second
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh leftReadings.values)
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh rightReadings.values)
      coefficient
  have formula :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary.Ordered.Paired.Prepared.resplit_exterior_area_formula
    grid.shrunk.included current.edges current.vertices reference prepared
    newSheet compiled value anti
  have branchEq := Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branch_area_sum grid.shrunk.included current.edges
    current.vertices paired newSheet value
  have scalar (regular branch inner ending cross terminal connector whole : Gaussian.Basic.Canonical)
      (branchEq : branch = inner + ending - terminal)
      (wholeEq : whole = inner + ending + cross + (regular + connector)) :
      regular + branch = whole - (cross + terminal) - connector := by
    rw [branchEq, wholeEq]
    ring1
  exact scalar _ _ _ _ _ _ _ _ branchEq formula

/-- One constructed all-later comparison on the shared Newton surface.
The physical, terminal, connector and cut corrections all remain visible. -/
theorem original_paired_period_area_accurate (newSheet : Fin 2) (excision :
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    (leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
      (rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let part := Rational.Budget.Aggregate.perTerm error 2
    let partPositive := Rational.Budget.Aggregate.perTerm_positive positive 2
    let regular := Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.build leftFixed rightFixed
      (Rational.Budget.Aggregate.perTerm part compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.build bank
      (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) leftFixed rightFixed
      (Rational.Budget.Aggregate.perTerm part excision.entries.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor excision.entries
    ∀ stage (leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential stage
      domains) (rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential
      stage domains)
      (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank
        current.mesh) (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
        rightBank current.mesh)
      (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
        leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
        current.cutPolygon.patch rightReadings.values),
      max regular.index branch.index ≤ stage →
      let regularSamples := Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples.build
        leftReadings rightReadings leftSurface rightSurface regular
      let branchSamples := Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples.build
        leftReadings rightReadings leftSurface rightSurface branch
      let physical := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
        coefficient =>
        let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
            coefficient
        current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
          Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
            current.vertices newSheet value -
          Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
            current.edges current.vertices newSheet value -
          Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms)
      Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeListArea
        (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues leftSurface rightSurface)
        current.cutPolygon.patch.cut.boundary -
        (regularSamples.corrections + branchSamples.corrections) - (physical + physical)) < error := by
  intro reference compiled part partPositive regular branch stage leftBank rightBank leftReadings rightReadings
    leftSurface rightSurface later regularSamples branchSamples physical
  have estimate := Hyperelliptic.Meshes.Newton.OriginalPairedRegionsComparison.original_paired_regions_accurate ordered
    newSheet (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) excision leftFixed
    rightFixed error positive floor
    stage leftBank rightBank leftReadings rightReadings leftSurface rightSurface later
  have read := Hyperelliptic.Meshes.Newton.PairedPeriodArea.original_paired_polygons_period_area prepared newSheet
    excision leftReadings rightReadings leftSurface rightSurface regularSamples branchSamples
  exact (congrArg (fun polygon => Data.Gaussian.Norm.Basic.normSq
    (Topology.Polygon.Stokes.edgeListArea (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues leftSurface
      rightSurface) current.cutPolygon.patch.cut.boundary -
      (regularSamples.corrections + branchSamples.corrections) - (polygon + polygon))) read.symm).trans_lt estimate

end Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedPeriodArea
