module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.LiftedPuncturedGrid

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid

public section

/-! One retained Newton geometry for the coefficient-independent raw energy
request. Its domains, annuli and observation partitions share the same grid. -/
namespace Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid (build)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests (FamilyFineAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (outerCount)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
set_option genInjectivity false in
/-- Allocated lifted grid with retained raw-energy geometry.

Keeps the actual fine-area request, lift, face domains, all-hole excision and outer preparations, together with
compatible surface partitions and the grid neighbor bank. -/
structure RawEnergyGrid (observations : ProtectedObservations original)
    (preparation : NewtonPreparation original) (radius : Fraction.Rational) where
  /-- Fine-area allocation at the shared raw-energy target and radius. -/ allocated :
    Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest preparation
    (NewtonRawEnergyBudget.rawEnergyGridTarget observations
      (Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation)) radius
  /-- Lift of the punctured grid belonging to the retained allocation. -/ lifted : LiftedPuncturedGrid
    allocated.family.single.grid.punctured
  /-- Face domains indexed by the retained lift and regular faces. -/ domains :
    Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames allocated.family.single.grid.faces.regulars
  /-- All-hole excision for the allocated grid and its exact lift. -/ excision :
    Meshes.Newton.AllHoles.Excision.AllHoleExcision allocated.family.single.grid lifted
  /-- Outer primitive preparations belonging to that excision. -/ outer :
    (Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations excision)
  /-- Observation partitions over the same allocated grid. -/ partitions : SurfacePartitions observations
    allocated.family.single.grid
  /-- The retained partition bank satisfies its compatibility conditions. -/ compatible :
    Meshes.Newton.Surface.PartitionBankCompatibility.Compatible partitions
  /-- Neighbor bank for the allocated punctured faces. -/ neighbors : PuncturedFaces.NeighborBank
    allocated.family.single.grid.faces

constructive_injectivity RawEnergyGrid

namespace RawEnergyGrid

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.RootContinuation in
/-- Construct a raw-energy grid from protected observations and positive radius.

Allocates the exact shared grid target, then constructs all lifts, domains, excision data, outer preparations and
partitions from that same allocated grid. -/
@[expose] def build (observations : ProtectedObservations original) (preparation : NewtonPreparation original)
    (radius : Fraction.Rational) (positive : 0 < radius) : RawEnergyGrid observations preparation radius :=
  let allocated := Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest.build preparation
    (NewtonRawEnergyBudget.rawEnergyGridTarget observations
      (Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation)) radius
    (NewtonRawEnergyBudget.rawEnergyGridTarget_positive observations
      (Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation)) positive
  let lifted := LiftedPuncturedGrid.build allocated.family.single.grid.punctured
  let domains := Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank.build lifted.frames
    allocated.family.single.grid.faces.regulars
  let excision := Meshes.Newton.AllHoles.Excision.AllHoleExcision.build allocated.family.single.grid lifted
  let outer := Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations.build excision
  let partitions := Meshes.Newton.Surface.PartitionBankCompatibility.build observations allocated.family.single.grid
  let compatible := Meshes.Newton.Surface.PartitionBankCompatibility.build_compatible observations
    allocated.family.single.grid
  let neighbors := PuncturedGridFaces.PuncturedFaces.NeighborBank.build allocated.family.single.grid.faces
    allocated.family.single.grid.shrunk.prepared.frame
  ⟨allocated, lifted, domains, excision, outer, partitions, compatible, neighbors⟩

end RawEnergyGrid
end Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
