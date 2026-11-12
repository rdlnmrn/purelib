module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PhysicalPeriodComparison
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Approximation.Rational.Budget

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Curve-data instantiation of the physical exterior-period comparison.
Named owners keep the dependent comparison statement within ordinary elaboration limits. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison

namespace CurvePhysicalComparison

variable {genus : Nat} (curve : Basic.HyperellipticCurve genus)
  (branches : Branches.BranchIsolation.Data curve) (higher : 1 < curve.polynomial.natDegree)

/-- The canonical framed punctured grid built from the original curve and branch isolation data. -/
def base := Meshes.FramedPuncturedGrid.ofData curve branches higher

/-- The lifted punctured grid on the retained canonical framed base. -/
def lifted := Meshes.LiftedPuncturedGrid.build
  (CurvePhysicalComparison.base curve branches higher)

/-- The based branch-tour bank on the original lifted grid. -/
def bank := PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.build
  (CurvePhysicalComparison.lifted curve branches higher)

/-- The retained branch-tour ordering from sheet zero. -/
def ordered := PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.ordered
  (CurvePhysicalComparison.bank curve branches higher) 0

/-- The original paired split of the retained sheet-zero branch ordering. -/
def paired := PuncturedGrid.OrderedBranchPairs.Ordered.paired
  (CurvePhysicalComparison.ordered curve branches higher)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison in
/-- The prepared period programs of the original paired branch split. -/
def prepared := PuncturedGrid.Paired.PeriodPrograms.prepare (paired curve branches higher)

variable {target radius : Fraction.Rational} (targetPositive : 0 < target) (radiusPositive : 0 < radius)

/-- The Newton grid of the original canonical branch-cell bank at the supplied positive target and radius. -/
def grid := PhysicalPeriodComparison.newtonGrid
  (CurvePhysicalComparison.base curve branches
  higher).bank.toBranchCellBank targetPositive radiusPositive

/-- The retained lifted punctured grid on the canonical Newton refinement. -/
def current := PhysicalPeriodComparison.newtonCurrent
  (CurvePhysicalComparison.base curve branches
  higher).bank.toBranchCellBank targetPositive radiusPositive

/-- The primitive face-domain bank on the original canonical Newton grid. -/
def domains := PhysicalPeriodComparison.newtonDomains
  (CurvePhysicalComparison.base curve branches
  higher).bank.toBranchCellBank targetPositive radiusPositive

/-- The complete retained hole excision for the canonical Newton grid and its lift. -/
def excision := AllHoles.Excision.AllHoleExcision.build
  (CurvePhysicalComparison.grid curve branches higher
  targetPositive radiusPositive)
  (CurvePhysicalComparison.current curve branches higher
    targetPositive radiusPositive)

/-- The original face magnitude bank for the specified standard differential on the canonical Newton domains. -/
def fixed (differential : Fin genus) := PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank.build
  (CurvePhysicalComparison.domains curve branches higher
    targetPositive radiusPositive) (Periods.PeriodMatrix.standardDifferential differential)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison in
/-- The physical-period estimate on the canonical geometric owners. -/
def Estimate (newSheet : Fin 2) (differential : Fin genus)
    (source : Differentials.Basic.Differential genus) (error : Fraction.Rational) (positive : 0 < error)
      (floor : Nat) : Prop :=
    let reference := fun point member => (PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      (CurvePhysicalComparison.grid curve branches higher
      targetPositive
      radiusPositive).punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      (CurvePhysicalComparison.grid curve branches higher
      targetPositive
      radiusPositive).shrunk.included
        (CurvePhysicalComparison.current curve branches higher
        targetPositive radiusPositive).edges
        (CurvePhysicalComparison.current
      curve branches higher targetPositive radiusPositive).vertices
      reference (PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember
        (CurvePhysicalComparison.base curve branches
        higher).bank) (CurvePhysicalComparison.ordered curve
        branches higher).prepared.partition newSheet
    let comparisonError := Aggregate.perTerm error 5
    let comparisonPositive := Aggregate.perTerm_positive positive 5
    let localError := Aggregate.perTerm comparisonError 3
    let localPositive := Aggregate.perTerm_positive comparisonPositive 3
    let part := Aggregate.perTerm localError 2
    let partPositive := Aggregate.perTerm_positive localPositive 2
    let regular := Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.build
      (CurvePhysicalComparison.fixed curve branches higher
      targetPositive radiusPositive
      differential) (Aggregate.perTerm part compiled.regulars.length)
      (Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := Branch.RegionAggregate.BranchRegionRequests.build
      (CurvePhysicalComparison.bank curve branches higher)
      (OrderedBranchPolygons.branchSheet
      (CurvePhysicalComparison.ordered curve branches
      higher) newSheet) (CurvePhysicalComparison.fixed curve
        branches higher targetPositive radiusPositive differential)
      (Aggregate.perTerm part
        (CurvePhysicalComparison.excision curve branches
        higher targetPositive radiusPositive).entries.length)
      (Aggregate.perTerm_positive partPositive _) floor
        (CurvePhysicalComparison.excision curve branches
        higher targetPositive radiusPositive).entries
    let connectors := compiled.connectorRequest
      (CurvePhysicalComparison.current curve branches higher
      targetPositive radiusPositive).mesh
      (CurvePhysicalComparison.fixed curve branches higher
        targetPositive radiusPositive differential) source localError localPositive floor
    let referenceRequest := PuncturedGrid.Inclusion.ReferenceAreaRequest.build
      (paired := paired curve branches higher)
      (CurvePhysicalComparison.grid
      curve branches higher targetPositive radiusPositive).shrunk.included
        (CurvePhysicalComparison.fixed curve branches higher
      targetPositive radiusPositive differential) newSheet comparisonError comparisonPositive
    let exteriorRequest := PuncturedGrid.Inclusion.ExteriorTotalRequest.exteriorTotalRequest
      (paired := paired curve branches higher)
      (CurvePhysicalComparison.grid curve
      branches higher targetPositive radiusPositive).shrunk.included reference compiled
        (CurvePhysicalComparison.fixed curve branches
      higher targetPositive radiusPositive differential) source
      comparisonError comparisonPositive floor
    ∀ stage (shared : PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage
      (CurvePhysicalComparison.domains curve
      branches higher targetPositive radiusPositive))
      (readings : PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
        (CurvePhysicalComparison.current curve branches higher
        targetPositive radiusPositive).mesh)
        (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
          (CurvePhysicalComparison.current curve branches
          higher targetPositive radiusPositive).cutPolygon.patch
        readings.values),
      max (max (max (max regular.index branch.index) connectors.val) referenceRequest.index) exteriorRequest.val ≤
        stage →
      let regularSamples :=
        Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples.build readings
        surface regular
      let branchSamples := Branch.RegionAggregate.BranchRegionRequests.Samples.build
        readings surface branch
      let value := PuncturedGrid.CanonicalEdgeValues.edgeValuation
        (CurvePhysicalComparison.current curve branches higher
        targetPositive radiusPositive).mesh
        readings.values
      let physical := (CurvePhysicalComparison.current curve
        branches higher targetPositive radiusPositive).edges.chainArea
        (CurvePhysicalComparison.current curve
        branches higher targetPositive radiusPositive).vertices value
          (CurvePhysicalComparison.grid curve branches higher
          targetPositive
        radiusPositive).punctured.bank.exterior newSheet +
        OriginalPeriodArea.resplitPeriodArea
          (CurvePhysicalComparison.prepared curve branches
          higher) (CurvePhysicalComparison.grid curve branches
          higher targetPositive
          radiusPositive).shrunk.included
            (CurvePhysicalComparison.current curve branches
            higher targetPositive radiusPositive).edges
          (CurvePhysicalComparison.current curve branches
            higher targetPositive radiusPositive).vertices newSheet value -
        PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired
          curve branches higher) (CurvePhysicalComparison.grid
          curve branches
          higher targetPositive radiusPositive).shrunk.included
            (CurvePhysicalComparison.current curve branches
            higher targetPositive
          radiusPositive).edges
            (CurvePhysicalComparison.current curve branches
            higher targetPositive radiusPositive).vertices newSheet value
      Gaussian.Norm.Basic.normSq (surface.boundaryArea - (regularSamples.corrections +
        branchSamples.corrections) - (physical +
        physical)) < error

/-- Instantiate the physical comparison from branch data, with no supplied
geometric owner, excision or magnitude bank. -/
theorem original_physical_period_comparison_ofData (newSheet : Fin 2) (differential : Fin genus)
    (source : Differentials.Basic.Differential genus) (error : Fraction.Rational) (positive : 0 < error)
      (floor : Nat) :
    Estimate curve branches higher
      targetPositive radiusPositive newSheet differential source error positive floor := by
  exact PhysicalPeriodComparison.original_physical_period_comparison
    (CurvePhysicalComparison.prepared curve branches higher)
    newSheet
    (CurvePhysicalComparison.excision curve branches higher
      targetPositive radiusPositive)
    (CurvePhysicalComparison.fixed curve branches higher
      targetPositive radiusPositive differential)
    source error positive floor

/-- Intrinsic curve data supplies the branch isolation and the degree bound.
The differential index excludes genus zero, where there is no period entry. -/
theorem original_physical_period_comparison_ofCurve
    (curve : Basic.HyperellipticCurve genus) {target radius : Fraction.Rational}
    (targetPositive : 0 < target) (radiusPositive : 0 < radius)
    (newSheet : Fin 2) (differential : Fin genus)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    Estimate curve
      (Branches.BranchIsolation.data curve)
      (Branches.BranchCutLifts.degreeGtOne_of_cycleIndex curve differential)
      targetPositive radiusPositive newSheet differential
      (Periods.PeriodMatrix.standardDifferential differential) error positive floor :=

    original_physical_period_comparison_ofData
    curve (Branches.BranchIsolation.data curve)
    (Branches.BranchCutLifts.degreeGtOne_of_cycleIndex curve differential)
    targetPositive radiusPositive newSheet differential
    (Periods.PeriodMatrix.standardDifferential differential) error positive floor

end CurvePhysicalComparison

end Purelib.Curves.Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison
