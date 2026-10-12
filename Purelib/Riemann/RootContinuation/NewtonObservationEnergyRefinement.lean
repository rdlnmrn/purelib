module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy

@[expose] public section

/-!
# Positive observation energy at a later common numerical index

Retain the spatial meshes, coefficient-independent requests, and preflights.
Only numerical readings and their certified budgets are acquired at the later
index. This is still observation boundary energy: identification with the raw
period form is a separate geometric obligation.
-/
namespace Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonObservationPartitions.ProtectedObservations (GridPartitions)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy (LocalMeshes)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics Samples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Request PositiveEnergy Preflights)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {partitions : GridPartitions observations grid} {sheet : Fin 2}

namespace Request

variable {coarse : LocalMeshes partitions domains sheet} {fixed : Preflights domains sheet} {totalTarget :
  Rational}

/-- Raise the common numerical index while retaining every original per-piece request and spatial mesh. -/
def raiseIndex (request : Request
  coarse fixed totalTarget) (stage : Nat) (later : request.index ≤ stage) :
    Request coarse fixed totalTarget :=
  { request with index := stage, index_ge := fun piece => (request.index_ge piece).trans later }

/-- The raised request uses exactly the supplied common index. -/
theorem raiseIndex_index (request :
  Request coarse fixed totalTarget) (stage : Nat) (later : request.index ≤ stage) :
    (request.raiseIndex stage later).index = stage := rfl

/-- Raising the numerical index preserves the original per-piece request entries. -/
theorem raiseIndex_entries (request :
  Request coarse fixed totalTarget) (stage : Nat) (later : request.index ≤ stage) :
    (request.raiseIndex stage later).entries = request.entries := rfl

/-- Raising the numerical index preserves the exact retained spatial meshes. -/
theorem raiseIndex_meshes (request :
  Request coarse fixed totalTarget) (stage : Nat) (later : request.index ≤ stage) :
    (request.raiseIndex stage later).meshes = request.meshes := rfl

end Request

namespace PositiveEnergy

/-- Acquire positive observation readings from the supplied later numerical cache.

The existing coefficient-independent requests, preflights and meshes are reused, and the new samples and certified
budget consume this exact shared cache. -/
def withNumerics (prepared :
  PositiveEnergy partitions domains sheet) {stage : Nat}
    (numerics : Numerics domains stage) (later : prepared.request.index ≤ stage) :
    PositiveEnergy partitions domains sheet :=
  let request := prepared.request.raiseIndex stage later
  let samples := Samples.ofNumerics request.meshes numerics
  ⟨prepared.coarse, prepared.fixed, request, numerics, samples, request.budget (le_refl _) samples, rfl⟩

/-- The synchronized positive-energy request uses the supplied cache's index. -/
theorem withNumerics_index
  (prepared : PositiveEnergy partitions domains sheet) {stage : Nat}
    (numerics : Numerics domains stage) (later : prepared.request.index ≤ stage) :
    (prepared.withNumerics numerics later).request.index = stage := rfl

/-- Numerical synchronization preserves the original observation meshes. -/
theorem withNumerics_meshes
  (prepared : PositiveEnergy partitions domains sheet) {stage : Nat}
    (numerics : Numerics domains stage) (later : prepared.request.index ≤ stage) :
    (prepared.withNumerics numerics later).request.meshes = prepared.request.meshes := rfl

/-- Numerical synchronization retains exactly the supplied cache. -/
theorem withNumerics_cache
  (prepared : PositiveEnergy partitions domains sheet) {stage : Nat}
    (numerics : Numerics domains stage) (later : prepared.request.index ≤ stage) :
    (prepared.withNumerics numerics later).numerics = numerics := rfl

open Purelib.Topology in
open Purelib.LinearAlgebra in
/-- The synchronized observation energy retains the original homogeneous positive lower bound.

The lower constant is unchanged for every coefficient vector and either face, including the zero vector. -/
theorem withNumerics_lower
  (prepared : PositiveEnergy partitions domains sheet) {stage : Nat}
    (numerics : Numerics domains stage) (later : prepared.request.index ≤ stage)
    (coefficients : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      BranchedCover.Double.Attachment.Face) :
    (observations.energy.lower / 8) * coefficientNormSq coefficients ≤
      ((prepared.withNumerics numerics later).budget.bound coefficients).boundaryEnergy :=
  (prepared.withNumerics numerics later).lower coefficients face

end PositiveEnergy
end Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
