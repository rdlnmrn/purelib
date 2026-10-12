module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.RawComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.ExteriorCapJoiningEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CapEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SewnEnergy
import Purelib.Riemann.RootContinuation.NewtonRawBoundarySchedule
import Purelib.Riemann.Periods.NewtonRawPeriodSamples
import Purelib.Riemann.RootContinuation.NewtonRawCapSampling
import Purelib.Riemann.RootContinuation.NewtonRawJoiningSamples
import Purelib.Riemann.Topology.NewtonRawSurfaceSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawSamples
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! Pay the full regular exterior residual before deriving raw coercivity. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawSamples

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {radius : Fraction.Rational}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations base.bank.toBranchCellBank}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {newSheet : Fin 2} {floor : Nat}
  {raw : Hyperelliptic.Meshes.Newton.Regular.RawRequest.RegularRawRequest prepared observations preparation radius
    regular newSheet floor}

namespace RegularRawSamples

open Purelib.Data.Rat.Fraction.Compatibility

variable {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  raw.grid.domains stage}

variable {box : Rational.Box} {polynomials :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box} {first : Fin genus}

/-- Combine the actual observation-surface lower bound with the paid regular
cap and joining comparisons. The conclusion belongs to the same corrected
resplit period matrices as the original raw comparison. All error allowances
are chosen independently of coefficients and leave the positive observation margin. -/
theorem remaining_regular_raw_lower
    (sampleData : Hyperelliptic.Meshes.Newton.Regular.RawSamples.RegularRawSamples prepared observations preparation
      radius regular raw polynomials cache first)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (commonLater : raw.index ≤ stage)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (observationFace : Topology.BranchedCover.Double.Attachment.Face) :
    let values := fun basis => Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation raw.grid.lifted.mesh
      (sampleData.period.triangles.get basis).values
    let aMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared
      raw.grid.allocated.family.single.grid.shrunk.included raw.grid.lifted.edges raw.grid.lifted.vertices newSheet
      values false
    let bMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared
      raw.grid.allocated.family.single.grid.shrunk.included raw.grid.lifted.edges raw.grid.lifted.vertices newSheet
      values true
    Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients aMatrix bMatrix := by
  intro values aMatrix bMatrix
  let surfaceEnergy := Topology.NewtonRawSurfaceSamples.RawSurfaceEnergy.build raw.surface raw.sewing raw.joining
    raw.boundary cache coefficients
  have later : raw.period.cut.index ≤ stage := raw.period_le.trans commonLater
  have boundaryLater : raw.boundary.index ≤ stage := raw.boundary_le.trans commonLater
  have contactLater := raw.boundary.contacts_le.trans boundaryLater
  have remainingLater := raw.boundary.remaining_le.trans boundaryLater
  have joinedLater := raw.boundary.joining_le.trans boundaryLater
  have surfaceLater := raw.joining.surface_le.trans joinedLater
  have sewingLater := raw.joining.sewing_le.trans joinedLater
  have joiningLater := raw.joining.joining_le.trans joinedLater
  have positive := RootContinuation.NewtonRawEnergyBudget.rawEnergyAllowance_positive observations
  have annularPaid := RootContinuation.NewtonRawEnergyBudget.rawEnergyGridTarget_annular observations
    (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation)
  have remainingPaid := RootContinuation.NewtonRawEnergyBudget.rawEnergyGridTarget_remaining observations
    (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation)
  have physicalPaid : (genus : Fraction.Rational)^2 *
    Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus
    (RootContinuation.NewtonRawEnergyBudget.rawEnergyAllowance observations) ≤
      16 * (RootContinuation.NewtonRawEnergyBudget.rawEnergyAllowance observations)^2 :=
    (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_paid positive).trans_eq (by
      ring1)
  let remaining :=
    Complement.CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
    raw.grid.excision surfaceEnergy.remaining raw.grid.neighbors
  have sewnLower :=
    Hyperelliptic.Meshes.Newton.Complement.SewnEnergy.SynchronizedSurfaceRequests.remaining_sewn_energy_lower
    raw.grid.excision raw.surface.energy raw.sewing.sewing (raw.surface.energy_le.trans surfaceLater)
    (raw.sewing.sewing_le.trans sewingLater)
    sampleData.surface.surface observationFace surfaceEnergy.faces surfaceEnergy.remaining raw.grid.neighbors positive
      raw.boundary.contacts contactLater
    sampleData.period.triangles sampleData.period.surfaces sampleData.period.pairs sampleData.period.selected positive
  have capUpper := Hyperelliptic.Meshes.Newton.Complement.CapEnergy.remaining_cap_energy_upper raw.grid.allocated
    raw.surface.shared raw.surface.schedule surfaceEnergy.remaining surfaceEnergy.faces
    (fun position sheet => (surfaceEnergy.whole.get sheet).get position)
    (fun position sheet => (surfaceEnergy.wholePerimeters.get sheet).get position)
    (sampleData.joining.attachments.get first) sampleData.caps.request raw.boundary.remaining remainingLater
      sampleData.surface.physical sampleData.surface.physicalFaces sampleData.joining.attachments raw.grid.neighbors
      sampleData.caps.evaluated
    (raw.surface.schedule_le.trans surfaceLater) sampleData.caps.request.minimum_le sampleData.caps.caps
    ((sampleData.caps.request.certify sampleData.caps.caps).evaluate coefficients)
      (RootContinuation.NewtonRawEnergyBudget.rawEnergyAllowance observations) positive.le physicalPaid positive
      remainingPaid
  have exteriorUpper :=
    Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples.remaining_exterior_energy_upper
    sampleData.period.periods raw.joining.joining sampleData.joining.evaluated sampleData.joining.attachments
    joiningLater positive degree
    coefficients remaining capUpper
  have reduced := Fraction.Order.Arithmetic.sub_le_sub_direct sewnLower exteriorUpper
  have cancel : (sampleData.period.selected.energy coefficients + remaining).im / 4 - (remaining + 2 *
    sampleData.period.periods.exterior coefficients).im / 4 =
      (sampleData.period.selected.energy coefficients - 2 * sampleData.period.periods.exterior coefficients).im / 4 :=
        by
    simp only [Gaussian.Basic.add_im, Gaussian.Basic.sub_im,
      Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
    ring1
  change _ ≤ (sampleData.period.selected.energy coefficients + remaining).im / 4 -
    (remaining + 2 * sampleData.period.periods.exterior coefficients).im / 4 at reduced
  rw [cancel] at reduced
  have period := Hyperelliptic.Meshes.Newton.Complement.RawComparison.Request.Samples.remaining_raw_lower
    sampleData.period.periods raw.period.cut later positive raw.sewing.annular sampleData.period.annular
    (raw.sewing.annular_le.trans sewingLater) sampleData.period.selected sampleData.period.holes coefficients
    positive annularPaid
  have combined := (Fraction.Order.Arithmetic.sub_le_sub_direct reduced (le_refl (a :=
    (RootContinuation.NewtonRawEnergyBudget.rawEnergyAllowance observations +
    RootContinuation.NewtonRawEnergyBudget.rawEnergyAllowance observations) *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))).trans period
  have margin := RootContinuation.NewtonRawEnergyBudget.rawEnergyAllowance_paid observations
  have scalar := congrArg (fun value : Fraction.Rational => value *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) margin
  apply scalar.symm.trans_le
  exact (le_of_eq (by ring1)).trans combined

end RegularRawSamples
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawSamples
