module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.Periods.NewtonRawPeriodSamples
public import Purelib.Riemann.RootContinuation.NewtonRawOddExteriorSchedule
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorEnergy
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Topology.NewtonRawSewingSchedule
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.NewtonRawPeriodSchedule
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Vector.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Consume the odd exterior schedule on the retained raw numerical samples. -/
namespace Purelib.Riemann.RootContinuation.NewtonRawOddExteriorEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.Topology.NewtonRawSewingSchedule (SewingSchedule)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {radius : Rational}
  {observations : ProtectedObservations base.bank.toBranchCellBank}
  {gridData : RawEnergyGrid observations preparation radius}
  (prepared : Prepared paired) {sewingFloor :
    Nat}
  (sewingData : SewingSchedule gridData sewingFloor)

namespace Request
open Purelib.Riemann.Periods.NewtonRawPeriodSchedule (RawPeriodSchedule)
open Purelib.Riemann.Periods.NewtonRawPeriodSamples.Request (RawPeriodSamples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRawOddExteriorSchedule (OddExteriorSchedule)

variable {newSheet : Fin 2} {floor minimum stage : Nat}
  (periodData : RawPeriodSchedule prepared sewingData newSheet floor minimum)
  (cache : Numerics gridData.domains
    stage)

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget (rawEnergyAllowance)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)

namespace RawPeriodSamples

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.LinearAlgebra.Gaussian in
/-- Bound remaining energy with the retained odd exterior period contribution.

For odd polynomial degree and a stage after the exterior joining schedule, transports the actual boundary-word estimate
to twice the retained period exterior, adding the raw-energy allowance. -/
theorem odd_remaining_energy_upper
    (samples : RawPeriodSamples prepared sewingData periodData cache)
    {joiningFloor : Nat} (schedule : OddExteriorSchedule gridData sewingData joiningFloor)
    (later : schedule.index ≤ stage) (degree : curve.polynomial.natDegree = 2 * genus + 1)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (remaining : Basic.Canonical) {surfaceAllowance
      :
      Fraction.Rational}
    (surfaceUpper : (remaining + Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (gridData.lifted.exteriorBoundaries.map (fun word => PairedIncrementArea.area (word.map
        (fun edge => ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
          Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation gridData.lifted.mesh (samples.triangles.get row).values
            edge)))))).im / 4 ≤
      surfaceAllowance * coefficientNormSq coefficients) :
    (remaining + 2 * samples.periods.exterior coefficients).im / 4 ≤
      (surfaceAllowance + rawEnergyAllowance observations) * coefficientNormSq coefficients :=
  Meshes.Newton.OddCanonicalExteriorEnergy.Samples.remaining_odd_exterior_energy_upper samples.periods schedule.joining
    ((schedule.joining_le gridData sewingData).trans later) degree coefficients remaining surfaceUpper

end RawPeriodSamples
end Request
end Purelib.Riemann.RootContinuation.NewtonRawOddExteriorEnergy
