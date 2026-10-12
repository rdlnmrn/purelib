module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CanonicalSurfaceEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-! Transport the complete canonical component estimate to the odd Newton exterior. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalSurfaceEnergy

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

attribute [local congr] FiniteSum.Fin.sumFin_congr

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
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
  {newSheet : Fin 2} {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current}
  {magnitudes : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential basis))}
  {error : Fraction.Rational} {floor stage : Nat}
  {cache : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (Periods.PeriodMatrix.standardDifferential
    basis) stage domains)}
  {triangles : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) current.mesh)}
  {surfaces : Topology.Surface.Sewing.SewnEnergyCombination.EnergySurfaces current.cutPolygon.patch (fun basis =>
    (triangles.get basis).values)}
  {pairs : Topology.Surface.Sewing.SewnEnergyCombination.EnergyPairs surfaces}
  {request : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes
    error floor}

variable {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
  Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus}

/-- The odd Newton exterior consumes the summed bounds of the actual canonical surface components. -/
theorem Samples.odd_component_surface_energy_upper (samples :
  Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples triangles surfaces pairs request)
    {allowance componentAllowance : Fraction.Rational} {joiningFloor : Nat}
    (joining :
      OddCanonicalExteriorRequest
      magnitudes allowance joiningFloor)
    (later : joining.index ≤ stage) (degree : curve.polynomial.natDegree = 2 * genus + 1)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (remaining :
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
      regular domains differential → Gaussian.Basic.Canonical)
    (bounded : ∀ component ∈
      (PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      (lifted := current) regular domains differential).components,
      (remaining component + Path.PairedIncrementArea.area (component.program.indexed.map
        (fun edge => Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh (triangles.get row).values
            edge)))).im / 4 ≤
        componentAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum

        ((PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
        regular domains differential).components.map remaining) +
        2 * samples.exterior coefficients).im / 4 ≤

        (((PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
        (lifted := current) regular domains differential).components.length : Fraction.Rational) *
        componentAllowance + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  exact Hyperelliptic.Meshes.Newton.OddCanonicalExteriorEnergy.Samples.remaining_odd_exterior_energy_upper
    samples joining later degree coefficients _

      (ExteriorProgram.AllSurfacePreparation.built_canonical_energy_upper
      cache coefficients (fun row => triangles.get row) remaining bounded)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalSurfaceEnergy
