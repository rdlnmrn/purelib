module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Topology.Surface.Sewing.SewnSelectedEnergy
public import Purelib.Riemann.Periods.NewtonRawPeriodSchedule
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.RawComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Data.Vector.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Topology.NewtonRawSewingSchedule
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Riemann.Meshes.LiftedPuncturedGrid

public section

/-! Cache the actual triangle, sewn, period and annular samples once for each
shared numerical bank. Homogeneous energy proofs consume these same values. -/
namespace Purelib.Riemann.Periods.NewtonRawPeriodSamples

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.Topology.NewtonRawSewingSchedule (SewingSchedule)
open Purelib.Riemann.Periods.NewtonRawPeriodSchedule (RawPeriodSchedule)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Topology.Surface.Sewing.SewnEnergyCombination (EnergySurfaces EnergyPairs)
open Purelib.Topology.Surface.Sewing.SewnSelectedEnergy (SelectedEnergySamples)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request (HoleSamples)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {radius : Purelib.Data.Rat.Fraction.Rational}
  {observations : ProtectedObservations base.bank.toBranchCellBank}
  {gridData : RawEnergyGrid observations preparation radius}
  (prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) {sewingFloor :
    Nat}
  (sewingData : SewingSchedule gridData sewingFloor)

namespace Request
open Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request (Samples)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (sourceMask)

variable {newSheet : Fin 2} {floor minimum stage : Nat}
  (periodData : RawPeriodSchedule prepared sewingData newSheet floor minimum)
  (cache : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics gridData.domains
    stage)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Surface in
set_option genInjectivity false in
/-- Cached readings for a raw period schedule.

Retains basis-indexed triangle readings and shared energy surfaces and pairs, together with physical, annular,
selected-complement and hole samples built from those exact owners. -/
structure RawPeriodSamples where
  /-- Basis-indexed triangle readings from the retained numerical cache. -/ triangles : Vector.DependentVector (fun
    basis : Fin genus => Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis)
    gridData.lifted.mesh)
  /-- Energy surfaces using those exact triangle values. -/ surfaces : Sewing.SewnEnergyCombination.EnergySurfaces
    gridData.lifted.cutPolygon.patch (fun basis => (triangles.get basis).values)
  /-- Paired energy surfaces over the retained surface family. -/ pairs : Sewing.SewnEnergyCombination.EnergyPairs
    surfaces
  /-- Physical period samples for the actual scheduled request. -/ periods :
    Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples triangles surfaces pairs periodData.request
  /-- Annular samples for the sewing schedule and shared surfaces. -/ annular :
    NewtonHomogeneousAnnularRequest.HomogeneousAnnularRequest.Samples triangles surfaces pairs sewingData.annular
  /-- Samples of sources outside every retained hole mask. -/ selected : Sewing.SewnSelectedEnergy.SelectedEnergySamples
    surfaces pairs
    (fun source => !(gridData.excision.entries.any (fun entry => sourceMask entry source)))
  /-- Hole readings indexed by the original excision. -/ holes :
    Meshes.Newton.HomogeneousBoundaryComparison.Request.HoleSamples triangles gridData.excision

constructive_injectivity RawPeriodSamples

namespace RawPeriodSamples

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Surface in
/-- Build all raw period samples from one numerical cache.

Constructs the triangle bank once, derives shared energy surfaces and pairs, then reuses them for the physical, annular
and selected readings; hole samples retain the original excision. -/
@[expose] def build : RawPeriodSamples prepared sewingData periodData cache :=
  let triangles := Vector.DependentVector.ofFn fun basis : Fin genus =>
    Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.build (cache.get basis) gridData.lifted.mesh
  let surfaces := Sewing.SewnEnergyCombination.EnergySurfaces.build gridData.lifted.cutPolygon.patch (fun basis =>
    (triangles.get basis).values)
  let pairs := Sewing.SewnEnergyCombination.EnergyPairs.build surfaces
  let periods := Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples.build triangles surfaces pairs
    periodData.request
  let annular := NewtonHomogeneousAnnularRequest.HomogeneousAnnularRequest.Samples.build triangles surfaces pairs
    sewingData.annular
  let selected := Sewing.SewnSelectedEnergy.SelectedEnergySamples.build surfaces pairs
    (fun source => !(gridData.excision.entries.any (fun entry => sourceMask entry source)))
  let holes := Meshes.Newton.HomogeneousBoundaryComparison.Request.HoleSamples.build triangles gridData.excision
  ⟨triangles, surfaces, pairs, periods, annular, selected, holes⟩

end RawPeriodSamples
end Request
end Purelib.Riemann.Periods.NewtonRawPeriodSamples
