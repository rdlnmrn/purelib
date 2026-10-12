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

variable {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
  (branches : Hyperelliptic.Branches.BranchIsolation.Data curve) (higher : 1 < curve.polynomial.natDegree)

/-- The canonical framed punctured grid built from the original curve and branch isolation data. -/
def base := Meshes.FramedPuncturedGrid.ofData curve branches higher

/-- The lifted punctured grid on the retained canonical framed base. -/
def lifted := Meshes.LiftedPuncturedGrid.build
  (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.base curve branches higher)

/-- The based branch-tour bank on the original lifted grid. -/
def bank := Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.build
  (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.lifted curve branches higher)

/-- The retained branch-tour ordering from sheet zero. -/
def ordered := Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.ordered
  (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.bank curve branches higher) 0

/-- The original paired split of the retained sheet-zero branch ordering. -/
def paired := Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.paired
  (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.ordered curve branches higher)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison in
/-- The prepared period programs of the original paired branch split. -/
def prepared := Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.prepare (paired curve branches higher)

variable {target radius : Fraction.Rational} (targetPositive : 0 < target) (radiusPositive : 0 < radius)

/-- The Newton grid of the original canonical branch-cell bank at the supplied positive target and radius. -/
def grid := Hyperelliptic.Meshes.Newton.PhysicalPeriodComparison.newtonGrid
  (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.base curve branches
  higher).bank.toBranchCellBank targetPositive radiusPositive

/-- The retained lifted punctured grid on the canonical Newton refinement. -/
def current := Hyperelliptic.Meshes.Newton.PhysicalPeriodComparison.newtonCurrent
  (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.base curve branches
  higher).bank.toBranchCellBank targetPositive radiusPositive

/-- The primitive face-domain bank on the original canonical Newton grid. -/
def domains := Hyperelliptic.Meshes.Newton.PhysicalPeriodComparison.newtonDomains
  (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.base curve branches
  higher).bank.toBranchCellBank targetPositive radiusPositive

/-- The complete retained hole excision for the canonical Newton grid and its lift. -/
def excision := Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.build
  (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.grid curve branches higher
  targetPositive radiusPositive)
  (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve branches higher
    targetPositive radiusPositive)

/-- The original face magnitude bank for the specified standard differential on the canonical Newton domains. -/
def fixed (differential : Fin genus) := Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank.build
  (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.domains curve branches higher
    targetPositive radiusPositive) (Periods.PeriodMatrix.standardDifferential differential)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison in
/-- The physical-period estimate on the canonical geometric owners. -/
def Estimate (newSheet : Fin 2) (differential : Fin genus)
    (source : Hyperelliptic.Differentials.Basic.Differential genus) (error : Fraction.Rational) (positive : 0 < error)
      (floor : Nat) : Prop :=
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.grid curve branches higher
      targetPositive
      radiusPositive).punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.grid curve branches higher
      targetPositive
      radiusPositive).shrunk.included
        (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve branches higher
        targetPositive radiusPositive).edges
        (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current
      curve branches higher targetPositive radiusPositive).vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember
        (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.base curve branches
        higher).bank) (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.ordered curve
        branches higher).prepared.partition newSheet
    let comparisonError := Rational.Budget.Aggregate.perTerm error 5
    let comparisonPositive := Rational.Budget.Aggregate.perTerm_positive positive 5
    let localError := Rational.Budget.Aggregate.perTerm comparisonError 3
    let localPositive := Rational.Budget.Aggregate.perTerm_positive comparisonPositive 3
    let part := Rational.Budget.Aggregate.perTerm localError 2
    let partPositive := Rational.Budget.Aggregate.perTerm_positive localPositive 2
    let regular := Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.build
      (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.fixed curve branches higher
      targetPositive radiusPositive
      differential) (Rational.Budget.Aggregate.perTerm part compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.build
      (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.bank curve branches higher)
      (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet
      (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.ordered curve branches
      higher) newSheet) (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.fixed curve
        branches higher targetPositive radiusPositive differential)
      (Rational.Budget.Aggregate.perTerm part
        (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.excision curve branches
        higher targetPositive radiusPositive).entries.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor
        (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.excision curve branches
        higher targetPositive radiusPositive).entries
    let connectors := compiled.connectorRequest
      (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve branches higher
      targetPositive radiusPositive).mesh
      (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.fixed curve branches higher
        targetPositive radiusPositive differential) source localError localPositive floor
    let referenceRequest := PuncturedGrid.Inclusion.ReferenceAreaRequest.build
      (paired := paired curve branches higher)
      (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.grid
      curve branches higher targetPositive radiusPositive).shrunk.included
        (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.fixed curve branches higher
      targetPositive radiusPositive differential) newSheet comparisonError comparisonPositive
    let exteriorRequest := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.exteriorTotalRequest
      (paired := paired curve branches higher)
      (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.grid curve
      branches higher targetPositive radiusPositive).shrunk.included reference compiled
        (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.fixed curve branches
      higher targetPositive radiusPositive differential) source
      comparisonError comparisonPositive floor
    ∀ stage (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage
      (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.domains curve
      branches higher targetPositive radiusPositive))
      (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
        (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve branches higher
        targetPositive radiusPositive).mesh)
        (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
          (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve branches
          higher targetPositive radiusPositive).cutPolygon.patch
        readings.values),
      max (max (max (max regular.index branch.index) connectors.val) referenceRequest.index) exteriorRequest.val ≤
        stage →
      let regularSamples :=
        Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples.build readings
        surface regular
      let branchSamples := Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples.build
        readings surface branch
      let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
        (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve branches higher
        targetPositive radiusPositive).mesh
        readings.values
      let physical := (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve
        branches higher targetPositive radiusPositive).edges.chainArea
        (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve
        branches higher targetPositive radiusPositive).vertices value
          (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.grid curve branches higher
          targetPositive
        radiusPositive).punctured.bank.exterior newSheet +
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea
          (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.prepared curve branches
          higher) (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.grid curve branches
          higher targetPositive
          radiusPositive).shrunk.included
            (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve branches
            higher targetPositive radiusPositive).edges
          (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve branches
            higher targetPositive radiusPositive).vertices newSheet value -
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired
          curve branches higher) (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.grid
          curve branches
          higher targetPositive radiusPositive).shrunk.included
            (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve branches
            higher targetPositive
          radiusPositive).edges
            (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.current curve branches
            higher targetPositive radiusPositive).vertices newSheet value
      Data.Gaussian.Norm.Basic.normSq (surface.boundaryArea - (regularSamples.corrections +
        branchSamples.corrections) - (physical +
        physical)) < error

/-- Instantiate the physical comparison from branch data, with no supplied
geometric owner, excision or magnitude bank. -/
theorem original_physical_period_comparison_ofData (newSheet : Fin 2) (differential : Fin genus)
    (source : Hyperelliptic.Differentials.Basic.Differential genus) (error : Fraction.Rational) (positive : 0 < error)
      (floor : Nat) :
    Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.Estimate curve branches higher
      targetPositive radiusPositive newSheet differential source error positive floor := by
  exact Hyperelliptic.Meshes.Newton.PhysicalPeriodComparison.original_physical_period_comparison
    (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.prepared curve branches higher)
    newSheet
    (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.excision curve branches higher
      targetPositive radiusPositive)
    (Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.fixed curve branches higher
      targetPositive radiusPositive differential)
    source error positive floor

/-- Intrinsic curve data supplies the branch isolation and the degree bound.
The differential index excludes genus zero, where there is no period entry. -/
theorem original_physical_period_comparison_ofCurve
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) {target radius : Fraction.Rational}
    (targetPositive : 0 < target) (radiusPositive : 0 < radius)
    (newSheet : Fin 2) (differential : Fin genus)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison.CurvePhysicalComparison.Estimate curve
      (Hyperelliptic.Branches.BranchIsolation.data curve)
      (Hyperelliptic.Branches.BranchCutLifts.degreeGtOne_of_cycleIndex curve differential)
      targetPositive radiusPositive newSheet differential
      (Periods.PeriodMatrix.standardDifferential differential) error positive floor :=

    original_physical_period_comparison_ofData
    curve (Hyperelliptic.Branches.BranchIsolation.data curve)
    (Hyperelliptic.Branches.BranchCutLifts.degreeGtOne_of_cycleIndex curve differential)
    targetPositive radiusPositive newSheet differential
    (Periods.PeriodMatrix.standardDifferential differential) error positive floor

end CurvePhysicalComparison

end Purelib.Curves.Hyperelliptic.Meshes.Newton.CurvePhysicalPeriodComparison
