module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonGlobalRetainedBandRequests
import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Cache every actual retained interface and hole-side request under finite maxima. -/

namespace Purelib.Riemann.RootContinuation.NewtonRetainedBandBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions observations grid}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {error : Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.RetainedBandBank

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.RootContinuation.NewtonGlobalRetainedBandRequests.SynchronizedSurfaceRequests (BandBoundaryRequest)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (centeredSideSum)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {lifted : LiftedPuncturedGrid grid.punctured}
  {requests : SynchronizedSurfaceRequests coarse fixed error} {traces : PerimeterTraces requests}
  {position : Fin grid.faces.regulars.length} {side : GridSide}

/-- Neighbor index selected between the original hole and regular-face lists. -/
@[expose] def NeighborIndex (isHole : Bool) := Fin (if isHole then grid.faces.holes.length else
  grid.faces.regulars.length)

open Purelib.Curves.Hyperelliptic in
/-- Boundary condition for a retained face and selected neighbor kind.

Hole neighbors require a matching side and retained source face; regular neighbors additionally require the matching
target face to be removed. -/
@[expose] def Condition (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (side : GridSide)
    (position : Fin grid.faces.regulars.length) : (isHole : Bool) → NeighborIndex (grid := grid) isHole → Prop
  | true, next => side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.faces.holes[next.val]'next.isLt).cell.box ∧ fineMask excision position = false
  | false, next => side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.faces.regulars[next.val]'next.isLt).cell.box ∧ fineMask excision position = false ∧ fineMask excision next =
        true

variable (excision : AllHoleExcision grid lifted) (traces :
  PerimeterTraces requests)

set_option genInjectivity false in
/-- Cached conditional band request and its numerical index.

For the indexed neighbor relation, retains a request whenever the boundary condition holds and an exact identity for its
cached index. -/
structure Entry (side : GridSide) (position : Fin grid.faces.regulars.length)
    (isHole : Bool) (next : NeighborIndex (grid := grid) isHole) where
  /-- Cached numerical index of the retained request or bank. -/ index : Nat
  /-- Band request available for each proof of the indexed boundary condition. -/ request : Condition excision side
    position isHole next → BandBoundaryRequest excision traces position side
  /-- Every available request has exactly the cached index. -/ index_eq : ∀ present, (request present).index = index

constructive_injectivity Entry

/-- Decide a neighbor condition and cache its band request.

A present interface or hole relation retains its actual constructed request and index; an absent relation stores index
zero and eliminates any purported witness. -/
@[expose] def Entry.build (side : GridSide) (position : Fin grid.faces.regulars.length)
    (isHole : Bool) (next : NeighborIndex (grid := grid) isHole) : Entry excision traces side position isHole next := by
  have decision : Decidable (Condition excision side position isHole next) := by
    cases isHole <;> unfold Condition <;> infer_instance
  letI := decision
  by_cases present : Condition excision side position isHole next
  · let request : BandBoundaryRequest excision traces position side := by
      cases isHole with
      | false =>
        exact BandBoundaryRequest.ofInterface excision traces position next side present.1 present.2.1 present.2.2
      | true => exact BandBoundaryRequest.ofHole excision traces position next side present.1 present.2
    exact ⟨request.index, fun _ => request, fun _ => rfl⟩
  · exact ⟨0, fun h => (present h).elim, fun h => (present h).elim⟩

open Purelib.Data in
/-- Dependent bank of band entries for every source face and neighbor.

The neighbor index remains tied to the selected hole-or-regular mode and original grid. -/
@[expose] def Entries (side : GridSide) (isHole : Bool) :=
  Vector.DependentVector (fun position : Fin grid.faces.regulars.length =>
    Vector.DependentVector (fun next : NeighborIndex (grid := grid) isHole => Entry excision traces side position isHole
      next))

/-- All entries in the retained dependent bank lie below one index. -/
@[expose] def Entries.IndexBound {side : GridSide} {isHole : Bool}
    (entries : Entries excision traces side isHole) (index : Nat) : Prop :=
  ∀ position next, ((entries.get position).get next).index ≤ index

set_option genInjectivity false in
/-- Retained band-entry bank with a common numerical index.

Keeps the entire finite bank for the selected side and neighbor mode together with pointwise bounds on its cached
indices. -/
structure Request (side : GridSide) (isHole : Bool) where
  /-- Actual dependent bank indexed by source face and neighbor. -/ entries : Entries excision traces side isHole
  /-- Cached numerical index of the retained request or bank. -/ index : Nat
  /-- Every cached entry index lies below the bank index. -/ entries_le : entries.IndexBound excision traces index

constructive_injectivity Request

namespace Request

open Purelib.Data in
/-- Build the complete retained band bank and its maximum index.

Constructs the dependent face/neighbor entries once and proves every entry index lies below the nested maximum. -/
@[expose] def build (side : GridSide) (isHole : Bool) : Request excision traces side isHole := by
  let entries : Entries excision traces side isHole := Vector.DependentVector.ofFn fun position =>
    Vector.DependentVector.ofFn fun next => Entry.build excision traces side position isHole next
  refine ⟨entries, entries.maximum (fun _ row => row.maximum fun _ entry => entry.index), ?_⟩
  intro position next
  exact ((entries.get position).get_le_maximum (fun _ entry => entry.index) next).trans
    (entries.get_le_maximum (fun _ row => row.maximum fun _ entry => entry.index) position)

variable {excision traces} {side : GridSide} {isHole : Bool}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
/-- Read a paid centered-side bound from the retained bank.

For a certified neighbor condition and a sufficiently late stage, uses the cached request and exact index identity
without rebuilding its band witness. -/
theorem centered_bound (request : Request excision traces side isHole) (later : request.index ≤ stage)
    (samples : PerimeterSamples requests traces cache coefficients)
    (position : Fin grid.faces.regulars.length) (next : NeighborIndex (grid := grid) isHole)
    (present : Condition excision side position isHole next) :
    Data.Gaussian.Norm.Basic.normSq (centeredSideSum samples side position) ≤
      4 * ((genus : Fraction.Rational)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients^2 *
        (((request.entries.get position).get next).request present).allowance) := by
  let entry := (request.entries.get position).get next
  exact (entry.request present).centered_bound
    ((entry.index_eq present).le.trans ((request.entries_le position next).trans later)) samples

end Request
end SynchronizedSurfaceRequests.RetainedBandBank
end Purelib.Riemann.RootContinuation.NewtonRetainedBandBank
