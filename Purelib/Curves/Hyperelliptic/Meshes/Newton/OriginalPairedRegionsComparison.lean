module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalPairedPartition
import Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
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
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
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

/-! The original ordered regular and branch regions account for the whole
shared cut surface, with a single requested aggregate error. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedRegionsComparison

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Integration in
/-- No original-cell area remains unexplained. Every canonical polygon
comes from the retained original compiler or original based branch bank;
all physical inner boundaries, sewn jumps and offsets remain explicit in
the cached corrections, rather than being silently declared negligible. -/
theorem original_paired_regions_accurate (ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet) (newSheet
  : Fin 2)
    (branchSheet : Hyperelliptic.Branches.BranchIsolation.Data.Index branches → Fin 2) (excision :
      Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    (leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
      (rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
      (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let reference := fun point member =>
      (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank
        point member).toLoop
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
    let branch := Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.build bank branchSheet
      leftFixed rightFixed (Rational.Budget.Aggregate.perTerm part excision.entries.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor excision.entries
    ∀ stage (leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential stage
      domains) (rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential
      stage domains) (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
      leftBank current.mesh) (rightReadings :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
      (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
        leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
        current.cutPolygon.patch rightReadings.values), max regular.index branch.index ≤ stage →
      let regularSamples := Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples.build
        leftReadings rightReadings leftSurface rightSurface regular
      let branchSamples := Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples.build
        leftReadings rightReadings leftSurface rightSurface branch
      Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeListArea
        (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues leftSurface rightSurface)
        current.cutPolygon.patch.cut.boundary - (regularSamples.corrections + branchSamples.corrections) -
        ((regularSamples.polygons + branchSamples.polygons) + (regularSamples.polygons + branchSamples.polygons))) <
          error := by
  intro reference compiled part partPositive regular branch stage leftBank rightBank leftReadings rightReadings
    leftSurface rightSurface later regularSamples branchSamples
  let selected := fun cell => Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.build
    leftSurface (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current cell)
  have regularArea := regularSamples.areas_eq selected
  have branchArea := (branchSamples.areas_eq selected).trans
    (Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.Ordered.branch_entries_sum ordered excision
      (fun index => Topology.Polygon.Stokes.edgeListArea (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues
        leftSurface rightSurface) ((selected (base.bank.cell index)).triangles.flatMap
        Topology.Polygon.Stokes.OrientedTriangle.boundary))).symm
  have partition : regularSamples.areas + branchSamples.areas = Topology.Polygon.Stokes.edgeListArea
    (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues leftSurface rightSurface)
    current.cutPolygon.patch.cut.boundary :=
    (congrArg₂ (· + ·) regularArea branchArea).trans
      (RootContinuation.NewtonOriginalPairedPartition.Ordered.original_paired_regions_area_partition
        ordered newSheet leftSurface (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues leftSurface
          rightSurface) selected)
  let regularError := regularSamples.areas - regularSamples.corrections - (regularSamples.polygons +
    regularSamples.polygons)
  let branchError := branchSamples.areas - branchSamples.corrections - (branchSamples.polygons + branchSamples.polygons)
  have regularBound : Data.Gaussian.Norm.Basic.normSq regularError ≤ part :=
    (regularSamples.aggregate_accurate partPositive ((Data.Nat.Order.le_max_left _ _).trans later)).le
  have branchBound : Data.Gaussian.Norm.Basic.normSq branchError ≤ part :=
    (branchSamples.aggregate_accurate partPositive ((Data.Nat.Order.le_max_right _ _).trans later)).le
  have estimate := Gaussian.Budget.Aggregate.normSq_sum_lt [regularError, branchError] positive (by
    intro value member
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact regularBound
    · rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact branchBound
      · exact (List.not_mem_nil member).elim)
  change Data.Gaussian.Norm.Basic.normSq (regularError + (branchError + 0)) < error at estimate
  rw [add_zero] at estimate
  have equal : Topology.Polygon.Stokes.edgeListArea (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues
    leftSurface rightSurface) current.cutPolygon.patch.cut.boundary - (regularSamples.corrections +
    branchSamples.corrections) -
      ((regularSamples.polygons + branchSamples.polygons) + (regularSamples.polygons + branchSamples.polygons)) =
      regularError + branchError := by
    rw [← partition]
    unfold regularError branchError
    ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_lt estimate

end Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedRegionsComparison
