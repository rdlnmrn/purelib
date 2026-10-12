module
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedPeriods
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Data.Rat

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests

open Purelib.Data.List

open Purelib.Topology.Surface.Sewing

public section

/-! Read back the cached exterior integral on the canonical physical cochain.
The comparison uses the same triangle readings and retained occurrence order. -/

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Request Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation
  (RequestedOddEnergy)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary (canonical_physical_source)
open Purelib.Riemann.Normalization
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Differential
    genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {target areaTarget : Coordinate} {floor : Nat}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request

/-- The canonical valuation of the complete original exterior boundary equals the sum of its retained source occurrences
in the same order. -/
theorem canonical_integral (request : AllSurfacePreparation.Request prepared target areaTarget floor)
    (values : Fin lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :
    SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh values) lifted.exteriorBoundaries.flatten
      =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.entries.map
        (fun entry => entry.occurrence.placement.location.sourceEdge.increment values)) := by
  have physical (entry : AllSurfacePreparation.Entry regular domains differential request.localTarget
    request.budget.areaTarget floor)
      (member : entry ∈ request.entries) :
      entry.occurrence.placement.indexed ∈ lifted.boundaryLoops.flatten := by
    have exterior : entry.occurrence.placement.indexed ∈ lifted.exteriorBoundaries.flatten :=
      request.indexed_eq ▸ Map.mem_map_of_mem member
    change entry.occurrence.placement.indexed ∈ (lifted.exteriorBoundaries ++ _).flatten
    rw [Data.List.Flatten.flatten_append]
    exact Data.List.Membership.mem_append.mpr (Or.inl exterior)
  have sum : ∀ entries : List (AllSurfacePreparation.Entry regular domains differential request.localTarget
    request.budget.areaTarget floor),
      (∀ entry ∈ entries, entry ∈ request.entries) →
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh values) (entries.map (fun entry =>
        entry.occurrence.placement.indexed)) =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry =>
          entry.occurrence.placement.location.sourceEdge.increment values)) := by
    intro entries retained
    induction entries with
    | nil => rfl
    | cons entry entries ih =>
      have source := CanonicalPhysicalBoundary.canonical_physical_source entry.occurrence.placement.location.sourceEdge
        (entry.occurrence.placement.location.sourceEdge_project.symm ▸ physical entry (retained entry
          List.mem_cons_self)) values
      have value := (congrArg (CanonicalEdgeValues.edgeValuation lifted.mesh values)
      entry.occurrence.placement.location.sourceEdge_project).symm.trans source
      exact congrArg₂ (fun first last : Data.Gaussian.Basic.Canonical => first + last) value
        (ih (fun next member => retained next (List.mem_cons_of_mem _ member)))
  exact (congrArg (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh values))
    request.indexed_eq).symm.trans
    (sum request.entries (fun _ member => member))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation
namespace RequestedOddEnergy

variable {component :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
  regular domains differential}
  {energyTarget : Coordinate} {depthFloor energyFloor : Nat}

/-- The odd exterior bound controls the original canonical boundary word. -/
theorem canonical_period_small
    (result : AllSurfacePreparation.RequestedOddEnergy prepared component target energyTarget floor depthFloor
      energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (readings : TrianglePrimitiveReadings.TriangleReadings result.acquired.shared lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.values) lifted.exteriorBoundaries.flatten) < target :=
  (congrArg Data.Gaussian.Norm.Basic.normSq (result.request.canonical_integral readings.values)).trans_lt
    (result.triangle_period_small branch readings)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy
