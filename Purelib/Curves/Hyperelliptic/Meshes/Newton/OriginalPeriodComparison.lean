module
import Purelib.Algebra.Group.Basic
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Basic
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
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Pay the original compiler's connector terms in the shared surface-to-
period comparison, preserving the physical exterior and sewn corrections. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodComparison

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
    {differential : Fin genus}

/-- The same later numerical stage pays the region comparisons and both
copies of the connector error. The conclusion no longer contains any
compiler connector term or unexplained regular-region polygon. -/
theorem original_period_comparison (newSheet : Fin 2) (excision :
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential))
    (source : Hyperelliptic.Differentials.Basic.Differential genus) (error : Fraction.Rational) (positive : 0 < error)
      (floor : Nat) :
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let localError := Rational.Budget.Aggregate.perTerm error 3
    let localPositive := Rational.Budget.Aggregate.perTerm_positive positive 3
    let part := Rational.Budget.Aggregate.perTerm localError 2
    let partPositive := Rational.Budget.Aggregate.perTerm_positive localPositive 2
    let regular := Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.build fixed
      (Rational.Budget.Aggregate.perTerm part compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.build bank
      (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) fixed
      (Rational.Budget.Aggregate.perTerm part excision.entries.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor excision.entries
    let connectors := compiled.connectorRequest current.mesh fixed source localError localPositive floor
    ∀ stage (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains)
      (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
        (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
      max (max regular.index branch.index) connectors.val ≤ stage →
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
          current.edges current.vertices newSheet value
      Data.Gaussian.Norm.Basic.normSq (surface.boundaryArea - (regularSamples.corrections +
        branchSamples.corrections) - (physical + physical)) < error := by
  intro reference compiled localError localPositive part partPositive regular branch connectors
    stage shared readings surface later regularSamples branchSamples value physical
  have region := Hyperelliptic.Meshes.Newton.OriginalPeriodArea.original_period_area_accurate prepared newSheet excision
    fixed localError localPositive floor
    stage shared readings surface ((Data.Nat.Order.le_max_left _ _).trans later)
  have connector := connectors.property stage shared readings ((Data.Nat.Order.le_max_right _ _).trans later)
  let correction := Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms
  have connectorRead : Topology.Mesh.RetracingWords.AreaTerm.total value compiled.areaTerms -
      Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Mesh.RetracingWords.wordArea value
        occurrence.word) compiled.regulars = correction := by
    exact (congrArg (fun total => total - Geometry.Grid.CellBoundary.sumValues
      (fun occurrence => Topology.Mesh.RetracingWords.wordArea value occurrence.word) compiled.regulars)
      (compiled.area_split value)).trans (Algebra.Group.add_sub_cancel_left _ _)
  have connectorBound : Data.Gaussian.Norm.Basic.normSq (-correction) ≤ localError := by
    rw [Gaussian.Norm.Basic.normSq_neg]
    exact (congrArg Data.Gaussian.Norm.Basic.normSq connectorRead.symm).trans_le connector.le
  let residual := surface.boundaryArea - (regularSamples.corrections + branchSamples.corrections) -
    ((physical - correction) + (physical - correction))
  have regionBound : Data.Gaussian.Norm.Basic.normSq residual ≤ localError := region.le
  have estimate := Gaussian.Budget.Aggregate.normSq_sum_lt [residual, -correction, -correction] positive (by
    intro term member
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact regionBound
    · rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact connectorBound
      · rcases Data.List.Membership.mem_cons.mp member with rfl | member
        · exact connectorBound
        · exact (List.not_mem_nil member).elim)
  change Data.Gaussian.Norm.Basic.normSq (residual + (-correction + (-correction + 0))) < error at estimate
  have equal : surface.boundaryArea - (regularSamples.corrections + branchSamples.corrections) - (physical + physical) =
      residual + (-correction + (-correction + 0)) := by
    unfold residual
    ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_lt estimate

end Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodComparison
