module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Tactic.Ring

public section

/-! Exact global decomposition of the complete two-sheet surface boundary.
Cached face samples retain every owner join. Only the finite neighbor
classification separates paired regular sides from physical boundaries. -/
namespace Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters FaceAssemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
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

variable (requests : SynchronizedSurfaceRequests coarse fixed error)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface in
open Purelib.Data in
/-- The retained face-perimeter traces indexed by both original sheets and every regular face. -/
@[expose] def PerimeterTraces := Vector.DependentVector (fun sheet : Fin 2 =>
  Vector.DependentVector (fun position : Fin grid.faces.regulars.length => PerimeterTraces.FacePerimeterTraces
    (requests.entries.get sheet) position))

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces in
open Purelib.Data in
/-- Build every face-perimeter trace from its exact synchronized sheet request. -/
@[expose] def PerimeterTraces.build : PerimeterTraces requests :=
  Vector.DependentVector.ofFn fun sheet => Vector.DependentVector.ofFn fun position =>
    FacePerimeterTraces.build (requests.entries.get sheet) position

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters in
open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian.Energy in
/-- Centered samples of those retained perimeters at one cache and coefficient vector. -/
@[expose] def PerimeterSamples (traces : PerimeterTraces requests) (cache : Numerics domains stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :=
  Vector.DependentVector (fun sheet : Fin 2 => Vector.DependentVector (fun position : Fin grid.faces.regulars.length =>
    FacePerimeterTraces.Centered ((traces.get sheet).get position) cache coefficients))

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces in
open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian.Energy in
/-- Materialize centered perimeter samples from the retained traces, cache and coefficients. -/
@[expose] def PerimeterSamples.build (traces : PerimeterTraces requests) (cache : Numerics domains stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : PerimeterSamples requests traces cache
      coefficients :=
  Vector.DependentVector.ofFn fun sheet => Vector.DependentVector.ofFn fun position =>
    Centered.build ((traces.get sheet).get position) cache coefficients

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest in
open Purelib.Data in
/-- The exact boundary assemblies for both synchronized sheet requests at the same sample. -/
@[expose] def SheetAssemblies := Vector.DependentVector (fun sheet : Fin 2 =>
    Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest.Assemblies
  (requests.entries.get sheet) cache coefficients)
section
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
open Purelib.Data
/-- The retained perimeters of the two original sheet assemblies. -/
@[expose] def SheetPerimeters (assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)) :=
  Vector.DependentVector (fun sheet : Fin 2 => FaceAssembly.Perimeters (assemblies.get sheet))
/-- Face assemblies indexed by their retained perimeters on both sheets. -/
@[expose] def SheetFaces {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    (perimeters : SheetPerimeters requests assemblies) :=
  Vector.DependentVector (fun sheet : Fin 2 => FaceAssembly.FaceAssemblies (perimeters.get sheet))

end

namespace PerimeterSamples

variable {requests} {traces : PerimeterTraces requests}
  (samples : PerimeterSamples requests traces cache coefficients)

section
open Purelib.Algebra
/-- Sum one retained side reading over both sheets of the same regular face. -/
@[expose] def sideSum (side : GridSide) (position : Fin grid.faces.regulars.length) : Gaussian :=
  FiniteSum.Fin.sumFin fun sheet : Fin 2 => match side with
    | .bottom => ((samples.get sheet).get position).bottom.originalArea
    | .right => ((samples.get sheet).get position).right.originalArea
    | .top => ((samples.get sheet).get position).top.originalArea
    | .left => ((samples.get sheet).get position).left.originalArea

/-- The complete oriented sum of the retained face perimeters on both sheets. -/
@[expose] def exterior : Gaussian := FiniteSum.Fin.sumFin fun position =>
  samples.sideSum .bottom position + samples.sideSum .right position -
    samples.sideSum .top position - samples.sideSum .left position

end

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters in
/-- The cached face exteriors equal the complete sum of the original centered perimeter readings.

Exact side readbacks and each sample's endpoint decomposition retain every original owner join. -/
theorem exterior_readback {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters) :
    FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet : Fin 2 => ((faces.get sheet).get
      position).exterior)) = samples.exterior := by
  have scalar (position : Fin grid.faces.regulars.length) (sheet : Fin 2) :
      ((faces.get sheet).get position).exterior =
        ((samples.get sheet).get position).bottom.originalArea + ((samples.get sheet).get position).right.originalArea -
          ((samples.get sheet).get position).top.originalArea - ((samples.get sheet).get position).left.originalArea :=
            by
    let reading := (samples.get sheet).get position
    let trace := (traces.get sheet).get position
    calc
      _ = trace.bottom.area (FacePerimeterTraces.ownerValues cache coefficients position) +
          trace.right.area (FacePerimeterTraces.ownerValues cache coefficients position) -
          trace.top.area (FacePerimeterTraces.ownerValues cache coefficients position) -
          trace.left.area (FacePerimeterTraces.ownerValues cache coefficients position) :=
        trace.exterior_eq ((faces.get sheet).get position)
      _ = _ := by
        rw [reading.bottom_area, reading.right_area, reading.top_area, reading.left_area,
          ← reading.bottom.decomposition, ← reading.right.decomposition,
          ← reading.top.decomposition, ← reading.left.decomposition]
  unfold exterior
  apply FiniteSum.Fin.sumFin_congr
  intro position
  rw [FiniteSum.Fin.sumFin_congr (scalar position)]
  simp only [-eq_self, -iff_self, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub, sideSum]
  rfl

section
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces
/-- The oriented perimeter contribution of sides classified as regular neighbors. -/
@[expose] def regular (neighbors : PuncturedFaces.NeighborBank grid.faces) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => SideNeighbor.regularValue ((neighbors.entries.get p).right) (samples.sideSum .right p))
    -
    FiniteSum.Fin.sumFin (fun p => SideNeighbor.regularValue ((neighbors.entries.get p).left) (samples.sideSum .left p))
      -
    (FiniteSum.Fin.sumFin (fun p => SideNeighbor.regularValue ((neighbors.entries.get p).top) (samples.sideSum .top p))
      -
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.regularValue ((neighbors.entries.get p).bottom) (samples.sideSum
        .bottom p)))

/-- The oriented perimeter contribution of sides classified as physical boundaries. -/
@[expose] def physical (neighbors : PuncturedFaces.NeighborBank grid.faces) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).right) (samples.sideSum .right
    p)) -
    FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).left) (samples.sideSum .left
      p)) -
    (FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).top) (samples.sideSum .top p))
      -
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).bottom) (samples.sideSum
        .bottom p)))

end

open Purelib.Algebra in
/-- The signed sum of actual matching right-left and top-bottom perimeter discrepancies. -/
@[expose] def paired : Gaussian :=
  FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun last =>
    if GridSide.Matches .right (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box then samples.sideSum .right first - samples.sideSum .left last
        else 0)) -
  FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun last =>
    if GridSide.Matches .top (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box then samples.sideSum .top first - samples.sideSum .bottom last
        else 0))

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces in
/-- The complete exterior separates into regular-neighbor and physical-boundary contributions.

The retained neighbor classification splits every original side value exactly, preserving its orientation and both sheet
occurrences. -/
theorem exterior_split (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    samples.exterior = samples.regular neighbors + samples.physical neighbors := by
  have split (side : GridSide) : FiniteSum.Fin.sumFin (samples.sideSum side) =
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.regularValue (FaceNeighbors.at (neighbors.entries.get p) side)
        (samples.sideSum side p)) +
        FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (FaceNeighbors.at (neighbors.entries.get p) side)
          (samples.sideSum side p)) := by
    rw [FiniteSum.Fin.sumFin_congr (fun p => SideNeighbor.value_split (FaceNeighbors.at (neighbors.entries.get p) side)
      (samples.sideSum side p)), FiniteSum.Fin.sumFin_add]
  unfold exterior
  simp only [-eq_self, -iff_self, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub]
  rw [split .bottom, split .right, split .top, split .left]
  dsimp only [regular, physical, FaceNeighbors.at]
  ring1

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces in
/-- The explicit matching-side pair sum equals the retained regular-neighbor contribution. -/
theorem paired_eq_regular (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    samples.paired = samples.regular neighbors := by
  unfold paired
  rw [NeighborBank.pair_sum neighbors .right (samples.sideSum .right) (samples.sideSum .left),
    NeighborBank.pair_sum neighbors .top (samples.sideSum .top) (samples.sideSum .bottom)]
  rfl

/-- The complete two-sheet exterior is the paired regular-side sum plus physical boundaries. -/
theorem exterior_eq_paired_add_physical (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    samples.exterior = samples.paired + samples.physical neighbors := by
  rw [samples.paired_eq_regular neighbors]
  exact samples.exterior_split neighbors

end PerimeterSamples
end SynchronizedSurfaceRequests
end Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
