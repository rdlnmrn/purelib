module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.ExteriorBoundary
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Budget

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib

@[expose] public section

/-! The shared original A/B comparison after paying the reference
double-loop and compiler connectors. Only physical/sewn terms remain. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PhysicalPeriodComparison

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} (prepared :
    PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  {preparation : BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {differential : Fin genus}

/-- The Newton grid built from the checked branch cell bank. -/
def newtonGrid (original : Branches.BranchCellBank curve branches higher)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius) :
    BranchCellBank.NewtonGrid
      (BranchCellBank.NewtonPreparation.build original) target radius :=
  BranchCellBank.NewtonGrid.build
    (BranchCellBank.NewtonPreparation.build original) positive radiusPositive

/-- The lifted punctured grid of the automatically built Newton grid. -/
def newtonCurrent (original : Branches.BranchCellBank curve branches higher)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius) :
    Meshes.LiftedPuncturedGrid (PhysicalPeriodComparison.newtonGrid original positive
      radiusPositive).punctured :=
  Meshes.LiftedPuncturedGrid.build (PhysicalPeriodComparison.newtonGrid original positive
    radiusPositive).punctured

/-- The face domain bank over the automatically built Newton grid. -/
def newtonDomains (original : Branches.BranchCellBank curve branches higher)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius) :
    PuncturedGrid.Face.DomainBanks.FaceDomainBank
      (PhysicalPeriodComparison.newtonCurrent original positive radiusPositive).frames
      (PhysicalPeriodComparison.newtonGrid original positive radiusPositive).faces.regulars
        :=
  PuncturedGrid.Face.DomainBanks.FaceDomainBank.build
    (PhysicalPeriodComparison.newtonCurrent original positive radiusPositive).frames
    (PhysicalPeriodComparison.newtonGrid original positive radiusPositive).faces.regulars

/-- All nonphysical terminal and compiler corrections are paid by the
computed shared stage. The even exterior-total cross now reads the actual
fixed exterior. Its full polygon area is transported to the refined grid's
literal exterior, preserving the individual sheet and all excursions.
Its contribution remains with the sewn corrections. -/
theorem original_physical_period_comparison (newSheet : Fin 2) (excision :
  AllHoles.Excision.AllHoleExcision grid current)
    (fixed : PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential))
    (source : Differentials.Basic.Differential genus) (error : Fraction.Rational) (positive : 0 < error)
      (floor : Nat) :
    let reference := fun point member => (PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let comparisonError := Aggregate.perTerm error 5
    let comparisonPositive := Aggregate.perTerm_positive positive 5
    let localError := Aggregate.perTerm comparisonError 3
    let localPositive := Aggregate.perTerm_positive comparisonPositive 3
    let part := Aggregate.perTerm localError 2
    let partPositive := Aggregate.perTerm_positive localPositive 2
    let regular := Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.build fixed
      (Aggregate.perTerm part compiled.regulars.length)
      (Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let branch := Branch.RegionAggregate.BranchRegionRequests.build bank
      (OrderedBranchPolygons.branchSheet ordered newSheet) fixed
      (Aggregate.perTerm part excision.entries.length)
      (Aggregate.perTerm_positive partPositive _) floor excision.entries
    let connectors := compiled.connectorRequest current.mesh fixed source localError localPositive floor
    let referenceRequest := PuncturedGrid.Inclusion.ReferenceAreaRequest.build
      (paired := paired) grid.shrunk.included fixed newSheet comparisonError comparisonPositive
    let exteriorRequest := PuncturedGrid.Inclusion.ExteriorTotalRequest.exteriorTotalRequest
      (paired := paired) grid.shrunk.included reference compiled fixed source
      comparisonError comparisonPositive floor
    ∀ stage (shared : PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains)
      (readings : PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
        (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
      max (max (max (max regular.index branch.index) connectors.val) referenceRequest.index) exteriorRequest.val ≤ stage
        →
      let regularSamples :=
        Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples.build readings
        surface regular
      let branchSamples := Branch.RegionAggregate.BranchRegionRequests.Samples.build
        readings surface branch
      let value := PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values
      let physical := current.edges.chainArea current.vertices value grid.punctured.bank.exterior newSheet +
        OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet value -
        PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
          grid.shrunk.included current.edges current.vertices newSheet value
      Gaussian.Norm.Basic.normSq (surface.boundaryArea - (regularSamples.corrections +
        branchSamples.corrections) - (physical + physical)) < error := by
  intro reference compiled comparisonError comparisonPositive localError localPositive part partPositive regular branch
    connectors
    referenceRequest exteriorRequest stage shared readings surface later regularSamples branchSamples value physical
  have region := OriginalPeriodComparison.original_period_comparison prepared newSheet
    excision fixed source comparisonError comparisonPositive floor
    stage shared readings surface ((Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_left _ _).trans
      later))
  let oldPhysical := current.edges.chainArea current.vertices value
    (grid.shrunk.included.resplit base.bank.exterior
      (PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
    OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges
      current.vertices newSheet value -
    OriginalPeriodArea.resplitEndCorrection (paired := paired) grid.shrunk.included
      current.edges current.vertices newSheet value
  let residual := surface.boundaryArea - (regularSamples.corrections + branchSamples.corrections) - (oldPhysical +
    oldPhysical)
  let correction := OriginalPeriodArea.resplitEndCorrection (paired := paired)
    grid.shrunk.included current.edges current.vertices newSheet value -
    PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
      grid.shrunk.included current.edges current.vertices newSheet value
  let exteriorError := PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection
    (paired := paired) grid.shrunk.included current.edges current.vertices newSheet value -
    PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
      grid.shrunk.included current.edges current.vertices newSheet value
  have referenceBound : Gaussian.Norm.Basic.normSq (-correction) ≤ comparisonError := by
    rw [Gaussian.Norm.Basic.normSq_neg]
    exact referenceRequest.end_accurate readings ((Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_left _
      _).trans later))
  have exteriorBound : Gaussian.Norm.Basic.normSq exteriorError ≤ comparisonError :=
    exteriorRequest.property stage shared readings ((Nat.Order.le_max_right _ _).trans later)
  have regionBound : Gaussian.Norm.Basic.normSq residual ≤ comparisonError := region.le
  have exteriorArea := (grid.shrunk.included.exterior_comparison base.bank.frame grid.punctured.bank.frame
    current.edges current.vertices reference).areas value
      (PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh readings.values)
      newSheet
  have estimate := Gaussian.Budget.Aggregate.normSq_sum_lt [residual, -correction, -correction, exteriorError,
    exteriorError] positive (by
    intro term member
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact regionBound
    · rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact referenceBound
      · rcases Data.List.Membership.mem_cons.mp member with rfl | member
        · exact referenceBound
        · rcases Data.List.Membership.mem_cons.mp member with rfl | member
          · exact exteriorBound
          · rcases Data.List.Membership.mem_cons.mp member with rfl | member
            · exact exteriorBound
            · exact (List.not_mem_nil member).elim)
  change Gaussian.Norm.Basic.normSq (residual + (-correction + (-correction + (exteriorError + (exteriorError +
    0))))) < error at estimate
  have equal : surface.boundaryArea - (regularSamples.corrections + branchSamples.corrections) - (physical + physical) =
      residual + (-correction + (-correction + (exteriorError + (exteriorError + 0)))) := by
    have scalar (surface regular branch oldOuter outer periods ending exterior physical : Gaussian.Basic.Canonical)
        (same : oldOuter = outer) :
        surface - (regular + branch) - ((outer + periods - physical) + (outer + periods - physical)) =
          surface - (regular + branch) - ((oldOuter + periods - ending) + (oldOuter + periods - ending)) +
            (-(ending - exterior) + (-(ending - exterior) + ((physical - exterior) + ((physical - exterior) + 0)))) :=
              by
      rw [same]
      ring1
    exact scalar _ _ _ _ _ _ _ _ _ exteriorArea
  exact (congrArg Gaussian.Norm.Basic.normSq equal).trans_lt estimate

end Purelib.Curves.Hyperelliptic.Meshes.Newton.PhysicalPeriodComparison
