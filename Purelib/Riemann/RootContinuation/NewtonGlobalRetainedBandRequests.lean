module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BandBoundary
public import Purelib.Riemann.RootContinuation.NewtonOmittedHoleGeometry
public import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Integration.Path.JoinedTrace
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Riemann.RootContinuation.NewtonSelectedSideGeometry
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.RootIsolation.State.Raw
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! Both-sheet requests for the retained Newton complement boundary. -/

namespace Purelib.Riemann.RootContinuation.NewtonGlobalRetainedBandRequests

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
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters FaceAssemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)
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

namespace SynchronizedSurfaceRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision AnnularEntry)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces (SideRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (BasisReadings)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry (SideBoundary)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (centeredSideSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies (PreparedBandFamily)

variable {lifted : LiftedPuncturedGrid grid.punctured}
  {requests : SynchronizedSurfaceRequests coarse fixed error} {traces : PerimeterTraces requests}
  {position : Fin grid.faces.regulars.length} {side : GridSide}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Riemann.RootContinuation in
/-- Sheet-indexed side requests at the retained annular band tolerance.

Each request uses the actual perimeter side geometry and the side budget determined by the band and trace length. -/
@[expose] def BandReferences (traces : PerimeterTraces requests) (entry : Meshes.Newton.AllHoles.Excision.AnnularEntry
  grid lifted)
    (position : Fin grid.faces.regulars.length) (side : GridSide) :=
  Vector.DependentVector (fun sheet : Fin 2 =>
    Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces.SideRequest (((traces.get sheet).get
      position).sideGeometry side)
      (PreparedNewtonAreaRate.PreparedBandFamily.sideBudget (grid.bands.entries.get entry.hole.index)
        (((traces.get sheet).get position).sideTrace side).rest.length).tolerance)

open Purelib.Curves.Hyperelliptic in
/-- Every retained band reference index is below the supplied index. -/
@[expose] def BandReferences.IndexBound {entry : Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted}
    (references : BandReferences traces entry position side) (index : Nat) : Prop :=
  ∀ sheet, (references.get sheet).index ≤ index

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Certified band boundary with retained sheet requests.

Keeps the actual excision entry and membership witness, the regular-side boundary relation, and a common index for its
two side requests. -/
structure BandBoundaryRequest (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (traces : PerimeterTraces requests) (position : Fin grid.faces.regulars.length) (side : GridSide) where
  /-- Actual annular entry retained from the excision. -/ entry : Meshes.Newton.AllHoles.Excision.AnnularEntry grid
    lifted
  /-- The retained entry belongs to the original excision list. -/ member : entry ∈ excision.entries
  /-- The indexed regular side lies on that band's boundary. -/ boundary :
    Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary (grid.faces.regulars[position.val]'position.isLt).cell.box
    (grid.bands.box entry.hole.index) side
  /-- Two sheet-specific side requests for the retained band. -/ references : BandReferences traces entry position side
  /-- Common numerical index for the retained references. -/ index : Nat
  /-- Each sheet reference index lies below the common index. -/ index_ge : references.IndexBound index

constructive_injectivity BandBoundaryRequest

namespace BandBoundaryRequest
variable {excision : AllHoleExcision grid lifted}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Riemann.RootContinuation in
/-- Build band references from an explicit certified side boundary.

Constructs both sheet requests using the exact band side budget and retains their maximum index with its bounds. -/
@[expose] def ofBoundary (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  PerimeterTraces requests)
    (position : Fin grid.faces.regulars.length) (side : GridSide)
    (entry : Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted) (member : entry ∈ excision.entries)
    (boundary : Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary
      (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.bands.box entry.hole.index) side) : BandBoundaryRequest excision traces position side :=
  let references : BandReferences traces entry position side := Vector.DependentVector.ofFn fun sheet =>
    let face := (traces.get sheet).get position
    let budget := PreparedNewtonAreaRate.PreparedBandFamily.sideBudget (grid.bands.entries.get entry.hole.index)
      (face.sideTrace side).rest.length
    Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces.SideRequest.build (face.sideGeometry side)
      budget.tolerance budget.tolerance_positive
  ⟨entry, member, boundary, references, references.maximum (fun _ reference => reference.index),
    fun sheet => references.get_le_maximum (fun _ reference => reference.index) sheet⟩

section
open Purelib.Curves.Hyperelliptic
/-- Acquire a band boundary at a retained-to-removed regular interface.

Finds the original excision band from the opposite matching side and transports its boundary witness back to the
retained face. -/
@[expose] def ofInterface (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  PerimeterTraces requests)
    (position next : Fin grid.faces.regulars.length) (side : GridSide)
    (matching : side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.faces.regulars[next.val]'next.isLt).cell.box)
    (retained : fineMask excision position = false) (removed : fineMask excision next = true) :
    BandBoundaryRequest excision traces position side := by
  let found := excision.interfaceBand next position side.opposite matching.reverse removed retained
  have boundary := found.property.2.matched matching.reverse
  apply ofBoundary excision traces position side found.val found.property.1
  cases side <;> exact boundary

/-- Acquire a band boundary adjacent to an original hole.

Retains the excision entry selected for that hole and its omitted-hole boundary certificate. -/
@[expose] def ofHole (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces : PerimeterTraces
  requests)
    (position : Fin grid.faces.regulars.length) (hole : Fin grid.faces.holes.length) (side : GridSide)
    (matching : side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.faces.holes[hole.val]'hole.isLt).cell.box)
    (retained : fineMask excision position = false) : BandBoundaryRequest excision traces position side :=
  let found := excision.entryForHole hole
  ofBoundary excision traces position side found.val found.property.1
    (excision.omittedHole_boundary position hole side matching retained)

end

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Area allowance of the request's retained annular band.

Multiplies the original prepared differential area coefficient by the square of the selected output radius. -/
@[expose] def allowance (request : BandBoundaryRequest excision traces position side) : Fraction.Rational :=
  PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient (curve := curve) (current := (BranchCellWinding.state
    original request.entry.hole.index).raw)
    (preparation.profiles.get request.entry.hole.index).differentials *
    (grid.bands.entries.get request.entry.hole.index).selection.sample.output.radius^2

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
/-- Bound the retained side's sum of centered sheet areas.

After the common request index, applies the band energy estimate to each actual side sample and combines the two
squared-norm bounds with factor four. -/
theorem centered_bound (request : BandBoundaryRequest excision traces position side)
    (later : request.index ≤ stage) (samples : PerimeterSamples requests traces cache coefficients) :
    Data.Gaussian.Norm.Basic.normSq (centeredSideSum samples side position) ≤
      4 * ((genus : Fraction.Rational)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients^2 *
        request.allowance) := by
  have bounded : ∀ sheet : Fin 2,
      Data.Gaussian.Norm.Basic.normSq ((((samples.get sheet).get position).sideSample side).centeredArea) ≤
        (genus : Fraction.Rational)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients^2 *
          request.allowance := by
    intro sheet
    exact ((traces.get sheet).get position).boundary_energy_bound side
      (grid.bands.entries.get request.entry.hole.index) request.boundary (request.references.get sheet)
      ((request.index_ge sheet).trans later)
      (Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings.build (((traces.get sheet).get
        position).sideTrace side) cache)
      (((samples.get sheet).get position).sideSample side)
  have bound := Norm.Sum.Indexed.normSq_sumFin_le _ _ bounded
  have readback : (FiniteSum.Fin.sumFin fun sheet : Fin 2 =>
      (((samples.get sheet).get position).sideSample side).centeredArea) = centeredSideSum samples side position := by
    cases side <;> rfl
  rw [readback] at bound
  exact bound.trans_eq (by ring1)

end BandBoundaryRequest
end SynchronizedSurfaceRequests
end Purelib.Riemann.RootContinuation.NewtonGlobalRetainedBandRequests
