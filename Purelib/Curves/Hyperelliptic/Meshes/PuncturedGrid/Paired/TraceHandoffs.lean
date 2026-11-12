module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Continue fixed face sheets using the actual cached prefix endpoint owner.
A subsequent boundary block reuses both domains and the inherited owner. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceHandoffs

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
      Meshes.PuncturedGridFaces.RegularFace
    bank}
  {firstModels : Face.InverseModels.BranchCellBank.FaceModels frames firstFace}
    {lastModels : Face.InverseModels.BranchCellBank.FaceModels frames lastFace}
  {start : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {leftEntry : Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
    Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain :
    Face.Periods.PeriodDomain lastModels rightEntry.sheet}
  {count : Nat}

variable {piece : Paths.RectangularPairedSegments.PairedSegmentPiece leftDomain.geometry rightDomain.geometry}

namespace Entry

/-- Continue the given face occurrence along a retained contained path. -/
def follow {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Face.InverseModels.BranchCellBank.FaceModels frames face}
    (entry : Face.Entries.FaceModels.Entry models start owner) {ambient :
      Rational.Box} {finish : Gaussian.Basic.Canonical}
    {path : Geometry.ClearPath curve.polynomial ambient start finish}
    (traced : Paths.PreparedPathTrace.TracedPath path owner) (inside : Geometry.ClearPath.InBox face.cell.box
      path) :
    Face.Entries.FaceModels.Entry models finish traced.finishOwner :=
  ⟨entry.sheet, entry.reached.append ⟨traced.trace.get,
    (Paths.PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original traced).trans
      (Paths.ClearBoxPathWinding.ClearPath.rawWinding_eq_potential face.clearance
        (Branches.BranchIsolation.degreePositive curve) path inside)⟩⟩

/-- Continuing the original face entry along the retained contained path preserves its exact sheet. -/
@[simp] theorem follow_sheet {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Face.InverseModels.BranchCellBank.FaceModels frames face}
    (entry : Face.Entries.FaceModels.Entry models start owner) {ambient :
      Rational.Box} {finish : Gaussian.Basic.Canonical}
    {path : Geometry.ClearPath curve.polynomial ambient start finish}
    (traced : Paths.PreparedPathTrace.TracedPath path owner) (inside : Geometry.ClearPath.InBox face.cell.box
      path) :
    (Entry.follow entry traced inside).sheet = entry.sheet :=
      rfl

end Entry

namespace PairedTracePreparation

variable {trace : Integration.RectangularPairedPointBanks.Trace piece count}

/-- Read the actual cached prefix endpoint owner at the retained trace vertex. -/
def ownerAt (preparation : TracePreparation.PairedTracePreparation trace)
    (vertex : Fin (count + 1)) : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval (trace.points
      vertex)) :=
  (preparation.prepared.get vertex).traced.finishOwner

/-- Continue the original left face entry to the cached prefix endpoint owner. -/
def leftEntryAt (preparation : TracePreparation.PairedTracePreparation trace)
    (vertex : Fin (count + 1)) : Face.Entries.FaceModels.Entry firstModels
      (trace.points vertex)
      (PairedTracePreparation.ownerAt preparation vertex) :=
  Entry.follow leftEntry
    (preparation.prepared.get vertex).traced (preparation.leftInside vertex)

/-- Continue the original right face entry to the same cached prefix endpoint owner. -/
def rightEntryAt (preparation : TracePreparation.PairedTracePreparation trace)
    (vertex : Fin (count + 1)) : Face.Entries.FaceModels.Entry lastModels
      (trace.points vertex)
      (PairedTracePreparation.ownerAt preparation vertex) :=
  Entry.follow rightEntry
    (preparation.prepared.get vertex).traced (preparation.rightInside vertex)

/-- Start the next common trace from an actual retained prefix endpoint.
The original face domains typecheck unchanged because both sheets are inherited. -/
def continueAt (preparation : TracePreparation.PairedTracePreparation trace)
    (vertex : Fin (count + 1))
    {nextPiece : Paths.RectangularPairedSegments.PairedSegmentPiece leftDomain.geometry rightDomain.geometry}
    {nextCount : Nat} (next : Integration.RectangularPairedPointBanks.Trace nextPiece nextCount)
    (joined : next.points 0 = trace.points vertex) :
    TracePreparation.PairedTracePreparation next
      (start := trace.points vertex)
      (owner := PairedTracePreparation.ownerAt preparation
        vertex)
      (leftEntry := PairedTracePreparation.leftEntryAt
        preparation vertex)
      (rightEntry := PairedTracePreparation.rightEntryAt
        preparation vertex) :=
  TracePreparation.PairedTracePreparation.build
    (start := trace.points vertex)
    (owner := PairedTracePreparation.ownerAt preparation vertex)
    (leftEntry := PairedTracePreparation.leftEntryAt preparation
      vertex)
    (rightEntry := PairedTracePreparation.rightEntryAt
      preparation vertex)
    next joined

end PairedTracePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceHandoffs
