module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnConjugateRequest
public import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest

open Purelib.Data.Vector

open Purelib.Riemann.Periods

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

public section

/-! All basis pairs share one sewing geometry and one preparation per basis.
Their common numerical index controls every homogeneous energy combination. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Surface.Sewing.SewingConnected.SewingForest (SinglePolygon)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (ContactBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Surface.Sewing.SewnEnergyCombination (EnergySurfaces EnergyPairs energyBoundary localEnergy
  energy_error_bound)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Riemann.Meshes.GridLiftedMesh.LiftedMesh
    vertices edges faces}
  {forest : Topology.Surface.Sewing.SewingForest mesh.triangulation.faces} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}

set_option genInjectivity false in
/-- One retained sewing geometry with a magnitude and contact preparation for every original basis differential.

All pairwise requests reuse these exact original caches on the same face domains. -/
structure EnergyPreparation (polygon : SewingForest.SinglePolygon forest) (domains : DomainBanks.FaceDomainBank frames
  faces.regulars) where
  /-- The original per-basis face magnitude caches on the retained shared domains. -/ magnitudes :
    Data.Vector.DependentVector (fun basis : Fin genus => MagnitudeBank.FaceMagnitudeBank domains
    (PeriodMatrix.standardDifferential basis))
  /-- The single contact bank of the original sewn polygon assembly. -/ contacts : SewnPrimitiveContacts.ContactBank
    polygon.patch.assembly
  /-- The original per-basis contact preparations using the exact shared contact list. -/ rows :
    Data.Vector.DependentVector (fun basis : Fin genus => ContactBanks.ContactPreparations contacts.entries
    (PeriodMatrix.standardDifferential basis) domains)

constructive_injectivity EnergyPreparation

namespace EnergyPreparation

variable {polygon : Topology.Surface.Sewing.SewingConnected.SewingForest.SinglePolygon forest}

/-- Cache one original polygon contact bank and one retained magnitude/contact preparation per basis differential. -/
@[expose] def build (polygon : SewingForest.SinglePolygon forest) (domains : DomainBanks.FaceDomainBank frames
  faces.regulars) : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation polygon domains :=
  let contacts := ContactBank.build polygon.patch.assembly
  ⟨DependentVector.ofFn (fun basis => FaceMagnitudeBank.build domains (PeriodMatrix.standardDifferential basis)),
    contacts,
    DependentVector.ofFn (fun basis => ContactPreparations.ofAssembly contacts (PeriodMatrix.standardDifferential basis)
      domains)⟩

/-- Reuse the two actual retained basis preparations as one original bilinear preparation. -/
@[expose] def pair (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation polygon
  domains) (first second : Fin genus) : SewnBilinearRequest.BilinearPreparation polygon domains first second :=
  ⟨prepared.magnitudes.get first, prepared.magnitudes.get second, prepared.contacts, prepared.rows.get first,
    prepared.rows.get second⟩

/-- The dependent matrix of original pairwise requests on the retained common preparation. -/
@[expose] def Requests (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation polygon
  domains) (target : SewnPrimitiveFaces.Coordinate) (floor : Nat) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    BilinearPreparation.Request (prepared.pair first second) target floor))

/-- Every actual pairwise request stage is at most the supplied common stage. -/
@[expose] def Requests.IndexBound {prepared :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation polygon domains} {target :
  SewnPrimitiveFaces.Coordinate} {floor : Nat}
    (entries : Requests prepared target
      floor) (index : Nat) : Prop :=
  ∀ first second, ((entries.get first).get second).index ≤ index

set_option genInjectivity false in
/-- The complete original basis-pair request matrix with a common stage paying all pairs and the supplied floor. -/
structure Request (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation polygon
  domains) (target : SewnPrimitiveFaces.Coordinate) (floor : Nat) where
  /-- The retained original matrix of basis-pair requests. -/ entries :
    Requests prepared target floor
  /-- The cached common numerical stage for all original basis pairs. -/ index : Nat
  /-- The common stage retains the supplied original floor. -/ floor_le : floor ≤ index
  /-- The common stage pays every retained original basis-pair request. -/ index_ge : entries.IndexBound index

constructive_injectivity Request

namespace Request

variable {prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation polygon domains}
  {target : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- Build every original positive basis-pair request and cache one maximum stage retaining the supplied floor. -/
@[expose] def build (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation polygon
  domains) (target : SewnPrimitiveFaces.Coordinate) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Request prepared target floor := by
  let entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Requests prepared target
    floor := DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
    BilinearPreparation.Request.build (prepared.pair first second) target positive floor
  let maximum := entries.maximum (fun _ row => row.maximum fun _ request => request.index)
  refine ⟨entries, max floor maximum, Data.Nat.Order.le_max_left _ _, ?_⟩
  intro first second
  exact ((entries.get first).get_le_maximum (fun _ request => request.index) second).trans
    ((entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.index) first).trans
      (Data.Nat.Order.le_max_right _ _))

/-- Every homogeneous energy combination satisfies the retained genus and coefficient-norm error bound at the paid
common stage. -/
theorem accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Request
  prepared target floor) {stage : Nat} (later : request.index ≤ stage)
    {cache : RegularMeshes.Numerics domains stage}
    (triangles : Data.Vector.DependentVector (fun basis : Fin genus => TrianglePrimitiveReadings.TriangleReadings
      (cache.get basis) mesh))
    (surfaces : SewnEnergyCombination.EnergySurfaces polygon.patch (fun basis => (triangles.get basis).values))
    (pairs : SewnEnergyCombination.EnergyPairs surfaces) (coefficients : Fin genus → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (SewnEnergyCombination.energyBoundary surfaces coefficients -
      FiniteSum.Fin.sumFin (SewnEnergyCombination.localEnergy (fun basis => (triangles.get basis).values) coefficients))
        ≤
        (genus : SewnPrimitiveFaces.Coordinate)^2 * (FiniteSum.Fin.sumFin (fun basis =>
          Data.Gaussian.Norm.Basic.normSq (coefficients basis)))^2 * target := by
  apply SewnEnergyCombination.energy_error_bound surfaces pairs coefficients
  intro first second
  exact (BilinearPreparation.Request.conjugate_accurate ((request.entries.get first).get second) ((request.index_ge
    first second).trans later)
    (triangles.get first) (triangles.get second) ((pairs.get first).get second)).le

end Request
end EnergyPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
