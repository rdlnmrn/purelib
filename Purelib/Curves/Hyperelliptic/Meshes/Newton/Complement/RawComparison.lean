module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.LinearAlgebra.Gaussian.Energy

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Topology.Surface.Sewing.SewnSelectedEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousRawComparison
import Purelib.Riemann.RootContinuation.NewtonHomogeneousRemainingComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

public section

/-! Compare raw corrected periods directly with the cached sewn complement.
The annular and period allowances are paid on their common later sample. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.RawComparison

open Purelib.Curves
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {family : Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation
    target radius}
  {current : Meshes.LiftedPuncturedGrid family.single.grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
    family.single.grid.faces.regulars} {newSheet : Fin 2}
  {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision family.single.grid current}
  {magnitudes : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential basis))}
  {error : Fraction.Rational} {floor : Nat}

namespace Request

open Purelib.Data.Rat.Fraction.Compatibility

variable {allowance : Fraction.Rational}
  {request : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes
    (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance / 4) floor}
  {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {triangles : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) current.mesh)}
  {surfaces : Topology.Surface.Sewing.SewnEnergyCombination.EnergySurfaces current.cutPolygon.patch (fun basis =>
    (triangles.get basis).values)}
  {pairs : Topology.Surface.Sewing.SewnEnergyCombination.EnergyPairs surfaces}

/-- Bound the corrected raw period form below by the cached sewn-complement energy with its exterior offset.

The annular and period allowances are paid on the same late samples, retaining the original hole contributions, selected
complement and coefficient norm. -/
theorem Samples.remaining_raw_lower (samples : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples
  triangles surfaces pairs request)
    {minimum : Nat} (cut : Hyperelliptic.Meshes.Newton.HomogeneousCutRequest.Request.CutRequest request
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance / 4)
      minimum)
    (later : cut.index ≤ stage) (positive : 0 < allowance)
    {annularPrepared :
      Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations excision}
      {annularFloor : Nat}
    (annularRequest : RootContinuation.NewtonHomogeneousAnnularRequest.HomogeneousAnnularRequest.Request (domains :=
      domains) annularPrepared annularFloor)
    (annularSamples : RootContinuation.NewtonHomogeneousAnnularRequest.HomogeneousAnnularRequest.Samples triangles
      surfaces pairs annularRequest)
    (annularLater : annularRequest.index ≤ stage)
    (selected : Topology.Surface.Sewing.SewnSelectedEnergy.SelectedEnergySamples surfaces pairs
      (fun source => !(excision.entries.any (fun entry => Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry
        source))))
    (holes : Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request.HoleSamples triangles excision)
      (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    {annularAllowance : Fraction.Rational} (annularPositive : 0 < annularAllowance)
    (annularPaid : (82 / 4 : Fraction.Rational) * target ≤
      Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus annularAllowance) :
    let values := fun basis => Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
      (triangles.get basis).values
    let aMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared family.single.grid.shrunk.included
      current.edges current.vertices newSheet values false
    let bMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared family.single.grid.shrunk.included
      current.edges current.vertices newSheet values true
    (selected.energy coefficients - 2 * samples.exterior coefficients).im / 4 -
      (annularAllowance + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
        LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients aMatrix bMatrix := by
  intro values aMatrix bMatrix
  have annular :=
    RootContinuation.NewtonHomogeneousRemainingComparison.HomogeneousAnnularRequest.Samples.remaining_sub_energy_lower
    annularSamples annularLater selected holes coefficients annularPositive
    annularPaid (2 * samples.exterior coefficients)
  have period := Hyperelliptic.Meshes.Newton.HomogeneousRawComparison.Request.Samples.raw_lower samples cut later
    positive holes coefficients
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct annular (le_rfl (a := allowance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))).trans period
  exact (le_of_eq (by ring1)).trans paid

end Request
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.RawComparison
