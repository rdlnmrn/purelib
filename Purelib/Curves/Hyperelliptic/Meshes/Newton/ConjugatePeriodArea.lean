module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchAggregate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Periods.NewtonConjugatePeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateRegionsComparison
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
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Budget

open Purelib.Topology

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib

public section

/-! The two cached polygon families read back to the polarization of the
actual resplit period identity, retaining every terminal and connector term. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePeriodArea

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered} (prepared :
    Paired.PeriodPrograms.Prepared paired)
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus}

open Purelib.Integration in
open Purelib.Polynomial in
/-- The polygon readback concerns the original ordered A/B owner. In
particular, polarization does not discard the even ending's terminal cross. -/
theorem original_conjugate_polygons_period_area (newSheet : Fin 2) (excision :
  AllHoles.Excision.AllHoleExcision grid current)
    {leftFixed : Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential}
      {rightFixed : Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential}
    {regularError branchError : Fraction.Rational} {floor : Nat}
    {stage : Nat} {leftBank : Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains} {rightBank : Face.PrimitiveData.FacePrimitiveBank
      rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh)
    (leftSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values) (rightSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample
      current.cutPolygon.patch rightReadings.values)
    (pair : Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface) :
    let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    ∀ {regular : PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed
      regularError floor compiled.regulars}
      {branch : PairedBranchAggregate.PairedBranchRequests bank
        (OrderedBranchPolygons.branchSheet ordered newSheet) leftFixed rightFixed
        branchError floor excision.entries},
      (regularSamples : ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples
        leftReadings rightReadings leftSurface rightSurface pair regular) →
      (branchSamples : ConjugateBranchAggregate.PairedBranchRequests.ConjugateSamples
        leftReadings rightReadings leftSurface rightSurface pair branch) →
      regularSamples.polygons + branchSamples.polygons =
        BilinearPolarization.extract (fun coefficient =>
        let value := BilinearPolarization.mix (fun edge =>
          Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
          current.mesh leftReadings.values edge))
          (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
            coefficient
        current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
          current.edges current.vertices newSheet value -
        Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms) := by
  intro reference compiled regular branch regularSamples branchSamples
  let first := fun edge => Gaussian.Basic.conj
    (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge)
  let second := CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values
  let branchWord := fun index => current.edges.indexedEdges current.vertices
    (grid.shrunk.included.resplit (bank.rows.get index).reference.walk
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      (OrderedBranchPolygons.branchSheet ordered newSheet index)
  have regularRead := regularSamples.polygons_eq.trans
    (Surface.Boundary.PolarizedWordArea.BilinearPolarization.extract_word_sum first second (fun occurrence =>
      occurrence.word) compiled.regulars).symm
  have branchRead := branchSamples.polygons_eq.trans
    ((Branch.RegionAggregate.Ordered.branch_entries_sum ordered excision
    (fun index => Path.PairedIncrementArea.area ((branchWord index).map (fun edge => (⟨first edge, second edge⟩ :
      Polygon.Stokes.PrimitivePoint))))).symm.trans
      (Surface.Boundary.PolarizedWordArea.BilinearPolarization.extract_word_sum first second branchWord
        ordered.prepared.labels).symm)
  rw [regularRead, branchRead]
  have combine : BilinearPolarization.extract (fun
    coefficient => Geometry.Grid.CellBoundary.sumValues (fun occurrence => Mesh.RetracingWords.wordArea
    (BilinearPolarization.mix first second coefficient)
    occurrence.word) compiled.regulars) +
      BilinearPolarization.extract (fun coefficient =>
        Geometry.Grid.CellBoundary.sumValues (fun index => Mesh.RetracingWords.wordArea
        (BilinearPolarization.mix first second coefficient)
        (branchWord index)) ordered.prepared.labels) =
      BilinearPolarization.extract (fun coefficient =>
        Geometry.Grid.CellBoundary.sumValues (fun occurrence => Mesh.RetracingWords.wordArea
        (BilinearPolarization.mix first second coefficient)
        occurrence.word) compiled.regulars +
        Geometry.Grid.CellBoundary.sumValues (fun index => Mesh.RetracingWords.wordArea
          (BilinearPolarization.mix first second coefficient)
          (branchWord index)) ordered.prepared.labels) := by
    unfold BilinearPolarization.extract
    ring1
  refine combine.trans (BilinearPolarization.extract_congr
    (fun coefficient => ?_))
  let value := BilinearPolarization.mix first second
    coefficient
  have anti := BilinearPolarization.mix_reverse first second
    (by
      intro edge
      change Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
        current.mesh leftReadings.values edge.reverse) =
        -Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
          leftReadings.values edge)
      rw [CanonicalEdgeValues.edgeValuation_reverse]
      rfl)
    (CanonicalEdgeValues.edgeValuation_reverse current.mesh rightReadings.values)
      coefficient
  have formula :=
    Inclusion.OrderedBoundary.Ordered.Paired.Prepared.resplit_exterior_area_formula
    grid.shrunk.included current.edges current.vertices reference prepared
    newSheet compiled value anti
  have branchEq := OrderedBranchPolygons.branch_area_sum grid.shrunk.included current.edges
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
theorem original_conjugate_period_area_accurate (newSheet : Fin 2) (excision :
  AllHoles.Excision.AllHoleExcision grid current)
    (leftFixed : Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
      (rightFixed : Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let part := Aggregate.perTerm error 2
    let partPositive := Aggregate.perTerm_positive positive 2
    let regular := PairedRegularAggregate.PairedRegularRequests.build leftFixed rightFixed
      (Aggregate.perTerm part compiled.regulars.length)
      (Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := PairedBranchAggregate.PairedBranchRequests.build bank
      (OrderedBranchPolygons.branchSheet ordered newSheet) leftFixed rightFixed
      (Aggregate.perTerm part excision.entries.length)
      (Aggregate.perTerm_positive partPositive _) floor excision.entries
    ∀ stage (leftBank : Face.PrimitiveData.FacePrimitiveBank leftDifferential stage
      domains) (rightBank : Face.PrimitiveData.FacePrimitiveBank rightDifferential
      stage domains)
      (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank
        current.mesh) (rightReadings : TrianglePrimitiveReadings.TriangleReadings
        rightBank current.mesh)
      (leftSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
        leftReadings.values) (rightSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample
        current.cutPolygon.patch rightReadings.values)
      (pair : Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface),
      max regular.index branch.index ≤ stage →
      let regularSamples :=
        ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples.build leftReadings
        rightReadings leftSurface rightSurface pair regular
      let branchSamples :=
        ConjugateBranchAggregate.PairedBranchRequests.ConjugateSamples.build leftReadings
        rightReadings leftSurface rightSurface pair branch
      let physical := Periods.NewtonConjugatePeriodReadback.conjugateResplitPeriodArea prepared grid.shrunk.included
        current.edges current.vertices newSheet
        (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
          (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values) +
        BilinearPolarization.extract (fun coefficient =>
        let value := BilinearPolarization.mix (fun edge =>
          Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
          current.mesh leftReadings.values edge))
          (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
            coefficient
        current.edges.chainArea current.vertices value (grid.shrunk.included.resplit base.bank.exterior
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet -
          OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
            current.edges current.vertices newSheet value -
          Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms)
      Gaussian.Norm.Basic.normSq (pair.boundaryArea -
        (regularSamples.corrections + branchSamples.corrections) - (physical + physical)) < error := by
  intro reference compiled part partPositive regular branch stage leftBank rightBank leftReadings rightReadings
    leftSurface rightSurface pair later regularSamples branchSamples physical
  have estimate := OriginalConjugateRegionsComparison.original_conjugate_regions_accurate
    ordered newSheet (OrderedBranchPolygons.branchSheet ordered newSheet) excision leftFixed
    rightFixed error positive floor
    stage leftBank rightBank leftReadings rightReadings leftSurface rightSurface pair later
  have read := ConjugatePeriodArea.original_conjugate_polygons_period_area prepared newSheet
    excision leftReadings rightReadings leftSurface rightSurface pair regularSamples branchSamples
  let first := CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values
  let second := CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values
  let value := fun coefficient => BilinearPolarization.mix
    (fun edge => Gaussian.Basic.conj (first edge)) second coefficient
  let period := fun coefficient => OriginalPeriodArea.resplitPeriodArea prepared
    grid.shrunk.included current.edges current.vertices newSheet (value coefficient)
  let rest := fun coefficient => current.edges.chainArea current.vertices (value coefficient)
    (grid.shrunk.included.resplit base.bank.exterior
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet -
      OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
        current.edges current.vertices newSheet (value coefficient) -
      Mesh.RetracingWords.AreaTerm.total (value coefficient) compiled.connectorTerms
  have split : BilinearPolarization.extract (fun coefficient
    =>
      current.edges.chainArea current.vertices (value coefficient)
        (grid.shrunk.included.resplit base.bank.exterior
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
          period coefficient -
      OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
        current.edges current.vertices newSheet (value coefficient) -
      Mesh.RetracingWords.AreaTerm.total (value coefficient) compiled.connectorTerms) =
        BilinearPolarization.extract period +
        BilinearPolarization.extract rest := by
    unfold BilinearPolarization.extract rest
    ring1
  have identified : regularSamples.polygons + branchSamples.polygons = physical :=
    read.trans (split.trans (congrArg (· +
      BilinearPolarization.extract rest)
      (Periods.NewtonConjugatePeriodReadback.extract_conjugate_resplit prepared grid.shrunk.included current.edges
        current.vertices newSheet first second)))
  exact (congrArg (fun polygon => Gaussian.Norm.Basic.normSq
    (pair.boundaryArea -
      (regularSamples.corrections + branchSamples.corrections) - (polygon + polygon))) identified.symm).trans_lt
        estimate

end Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePeriodArea
