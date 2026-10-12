module
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Meshes.RectangularObservationMesh

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PrimitiveSurfaceBudget

open Purelib.Curves

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-! Tighten primitive-reading tolerances without changing a prepared mesh.
The updated requests retain their spatial certificates and numerical floors. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

variable {face : RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
  {domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} {box :
    Rational.Box}
  {preflight : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain} {coarse :
    Meshes.RectangularObservationMesh.ObservationMesh domain.cuts box} {target : Fraction.Rational}

/-- Tighten the original primitive-reading tolerance to a positive cap while retaining its mesh, depth and prior
numerical floor.

The original request owners, mesh identities and spatial depths remain retained; only the reading cap and a certified
common numerical stage are tightened. -/
@[expose] def DomainEnergyRequest.EnergyRequest.limitReadings
    (request : Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight coarse target) (cap :
      Fraction.Rational) (positive : 0 < cap) :
    Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight coarse target :=
  let readingTarget := min request.readingTarget cap
  let readingPositive := Fraction.Order.Basic.lt_min request.reading_positive positive
  let initial := Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.Request.build preflight
    readingTarget readingPositive
  { request with
    readingTarget := readingTarget
    reading_positive := readingPositive
    reading_small := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_left _ _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))).trans request.reading_small
    modelRequest := initial.refineIndex (max request.modelRequest.index initial.index) (Data.Nat.Order.le_max_right _ _)
      }

/-- The tightened reading tolerance fits the supplied cap. -/
theorem DomainEnergyRequest.EnergyRequest.limitReadings_target_le
    (request : Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight coarse target) (cap :
      Fraction.Rational) (positive : 0 < cap) :
    (request.limitReadings cap positive).readingTarget ≤ cap := Fraction.Order.Basic.min_le_right _ _

/-- Tightening the reading tolerance retains the exact original observation mesh. -/
theorem DomainEnergyRequest.EnergyRequest.limitReadings_mesh
    (request : Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight coarse target) (cap :
      Fraction.Rational) (positive : 0 < cap) :
    (request.limitReadings cap positive).mesh = request.mesh := rfl

/-- Tightening the reading tolerance retains the exact original spatial depth. -/
theorem DomainEnergyRequest.EnergyRequest.limitReadings_depth
    (request : Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight coarse target) (cap :
      Fraction.Rational) (positive : 0 < cap) :
    (request.limitReadings cap positive).depth = request.depth := rfl

/-- The tightened request meets the original numerical reading floor.

The original request owners, mesh identities and spatial depths remain retained; only the reading cap and a certified
common numerical stage are tightened. -/
theorem DomainEnergyRequest.EnergyRequest.limitReadings_index_ge
    (request : Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight coarse target) (cap :
      Fraction.Rational) (positive : 0 < cap) :
    request.modelRequest.index ≤ (request.limitReadings cap positive).modelRequest.index := Data.Nat.Order.le_max_left _
      _

variable {face : RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
  {domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} {box :
    Rational.Box}
  {preflight : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain}
  {first last : Meshes.RectangularObservationMesh.ObservationMesh domain.cuts box} {target : Fraction.Rational}

/-- Transport the retained ownership request along a certified mesh equality.

The supplied equality changes the observation-mesh index of the same request.
Its original preflight, target, numerical index and retained preparation data
are transported together. -/
@[expose] def DomainClippedRequest.ClippedBasisRequest.transportMesh
    (request : Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedBasisRequest preflight first target)
      (equal : first = last) :
    Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedBasisRequest preflight last target := equal ▸ request

/-- Transport along an exact observation-mesh equality preserves the original ownership request index. -/
theorem DomainClippedRequest.ClippedBasisRequest.transportMesh_index
    (request : Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedBasisRequest preflight first target)
      (equal : first = last) :
    (request.transportMesh equal).index = request.index := by
  cases equal
  rfl

variable {faces : List (RegularFace bank)} {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank
  frames faces}

variable {sheet : Fin 2} {coarse : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {target :
  Fraction.Rational}

/-- Tighten each original face's reading tolerance to its supplied positive cap and retain a common stage above the old
request.

The original request owners, mesh identities and spatial depths remain retained; only the reading cap and a certified
common numerical stage are tightened. -/
@[expose] def RegularDomainMeshes.RegularMeshes.Request.limitReadings
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse fixed target)
    (caps : Fin faces.length → Fraction.Rational) (positive : ∀ position, 0 < caps position) :
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse fixed target :=
  let entries := Data.Vector.DependentVector.ofFn fun position =>
    (request.entries.get position).limitReadings (caps position) (positive position)
  { request with
    entries := entries
    index := max request.index (entries.maximum (fun _ entry => entry.modelRequest.index))
    index_ge := fun position => (entries.get_le_maximum (fun _ entry => entry.modelRequest.index) position).trans
      (Data.Nat.Order.le_max_right _ _) }

/-- Each tightened face request retains the exact original observation mesh. -/
theorem RegularDomainMeshes.RegularMeshes.Request.limitReadings_mesh
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse fixed target)
    (caps : Fin faces.length → Fraction.Rational) (positive : ∀ position, 0 < caps position) (position : Fin
      faces.length) :
    (request.limitReadings caps positive).meshes.entries.get position = request.meshes.entries.get position := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request.mesh_eq,
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request.mesh_eq]
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request.limitReadings]
  rw [Data.Vector.DependentVector.ofFn_get]
  rfl

/-- Each tightened face request retains the exact original spatial depth. -/
theorem RegularDomainMeshes.RegularMeshes.Request.limitReadings_depth
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse fixed target)
    (caps : Fin faces.length → Fraction.Rational) (positive : ∀ position, 0 < caps position) (position : Fin
      faces.length) :
    ((request.limitReadings caps positive).entries.get position).depth = (request.entries.get position).depth := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request.limitReadings]
  rw [Data.Vector.DependentVector.ofFn_get]
  rfl

/-- Each tightened face reading tolerance fits its supplied positive cap. -/
theorem RegularDomainMeshes.RegularMeshes.Request.limitReadings_target_le
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse fixed target)
    (caps : Fin faces.length → Fraction.Rational) (positive : ∀ position, 0 < caps position) (position : Fin
      faces.length) :
    ((request.limitReadings caps positive).entries.get position).readingTarget ≤ caps position := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request.limitReadings]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact (request.entries.get position).limitReadings_target_le _ _

variable {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}

/-- Tighten the original reading tolerances on both sheets, preserving their shared spatial depths and increasing only
the common numerical stage.

The original request owners, mesh identities and spatial depths remain retained; only the reading cap and a certified
common numerical stage are tightened. -/
@[expose] def TwoSheetBilinearRequest.TwoSheetRequest.limitReadings
    (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target)
    (caps : Fin 2 → Fin faces.length → Fraction.Rational) (positive : ∀ sheet position, 0 < caps sheet position) :
    Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target :=
  let entries := Data.Vector.DependentVector.ofFn fun sheet : Fin 2 =>
    (request.entries.get sheet).limitReadings (caps sheet) (positive sheet)
  { request with
    entries := entries
    depth_eq := fun sheet position => by
      dsimp only [entries]
      rw [Data.Vector.DependentVector.ofFn_get,
        Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request.limitReadings_depth]
      exact request.depth_eq sheet position
    index := max request.index (entries.maximum (fun _ entry => entry.index))
    index_ge := fun sheet => (entries.get_le_maximum (fun _ entry => entry.index) sheet).trans
      (Data.Nat.Order.le_max_right _ _) }

/-- Each tightened sheet and face retains its exact original observation mesh. -/
theorem TwoSheetBilinearRequest.TwoSheetRequest.limitReadings_mesh
    (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target)
    (caps : Fin 2 → Fin faces.length → Fraction.Rational) (positive : ∀ sheet position, 0 < caps sheet position)
    (sheet : Fin 2) (position : Fin faces.length) :
    ((request.limitReadings caps positive).entries.get sheet).meshes.entries.get position =
      (request.entries.get sheet).meshes.entries.get position := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.limitReadings]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact (request.entries.get sheet).limitReadings_mesh _ _ position

/-- Each tightened sheet and face reading tolerance fits its supplied positive cap. -/
theorem TwoSheetBilinearRequest.TwoSheetRequest.limitReadings_target_le
    (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target)
    (caps : Fin 2 → Fin faces.length → Fraction.Rational) (positive : ∀ sheet position, 0 < caps sheet position)
    (sheet : Fin 2) (position : Fin faces.length) :
    (((request.limitReadings caps positive).entries.get sheet).entries.get position).readingTarget ≤ caps sheet position
      := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.limitReadings]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact (request.entries.get sheet).limitReadings_target_le _ _ position

variable {energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target}
  {ownershipTarget : Fraction.Rational}

/-- Reuse every ownership preparation: tightening primitive accuracy leaves
its actual observation meshes unchanged.

The original request owners, mesh identities and spatial depths remain retained; only the reading cap and a certified
common numerical stage are tightened. -/
@[expose] def RegularClippedRequest.ClippedRequest.limitReadings
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest energy ownershipTarget)
    (caps : Fin 2 → Fin faces.length → Fraction.Rational) (positive : ∀ sheet position, 0 < caps sheet position) :
    Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest (energy.limitReadings caps positive)
      ownershipTarget :=
  let entries := Data.Vector.DependentVector.ofFn fun sheet : Fin 2 => Data.Vector.DependentVector.ofFn fun position :
    Fin faces.length =>
    ((request.entries.get sheet).get position).transportMesh (energy.limitReadings_mesh caps positive sheet
      position).symm
  { positive := request.positive
    perFace := request.perFace
    perFace_eq := request.perFace_eq
    entries := entries
    index := max (energy.limitReadings caps positive).index request.index
    energy_le := Data.Nat.Order.le_max_left _ _
    index_ge := fun sheet position => by
      dsimp only [entries]
      rw [Data.Vector.DependentVector.ofFn_get, Data.Vector.DependentVector.ofFn_get,
        Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedBasisRequest.transportMesh_index]
      exact (request.index_ge sheet position).trans (Data.Nat.Order.le_max_right _ _) }

variable {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}

/-- Tighten the energy readings and transport the original ownership preparations along the retained exact mesh
identities.

The original request owners, mesh identities and spatial depths remain retained; only the reading cap and a certified
common numerical stage are tightened. -/
@[expose] def RegularLocalBoundaryRequest.LocalBoundaryRequest.limitReadings
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest coarse fixed target)
    (caps : Fin 2 → Fin faces.length → Fraction.Rational) (positive : ∀ sheet position, 0 < caps sheet position) :
    Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest coarse fixed target :=
  { request with
    energy := request.energy.limitReadings caps positive
    ownership := request.ownership.limitReadings caps positive }

/-- The tightened local-boundary request retains every original sheet and face observation mesh. -/
theorem RegularLocalBoundaryRequest.LocalBoundaryRequest.limitReadings_mesh
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest coarse fixed target)
    (caps : Fin 2 → Fin faces.length → Fraction.Rational) (positive : ∀ sheet position, 0 < caps sheet position)
    (sheet : Fin 2) (position : Fin faces.length) :
    (((request.limitReadings caps positive).energy.entries.get sheet).meshes.entries.get position) =
      (request.energy.entries.get sheet).meshes.entries.get position :=
  request.energy.limitReadings_mesh caps positive sheet position

/-- Every tightened local-boundary reading tolerance fits its supplied positive cap. -/
theorem RegularLocalBoundaryRequest.LocalBoundaryRequest.limitReadings_target_le
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest coarse fixed target)
    (caps : Fin 2 → Fin faces.length → Fraction.Rational) (positive : ∀ sheet position, 0 < caps sheet position)
    (sheet : Fin 2) (position : Fin faces.length) :
    ((((request.limitReadings caps positive).energy.entries.get sheet).entries.get position).readingTarget) ≤ caps sheet
      position :=
  request.energy.limitReadings_target_le caps positive sheet position

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
