module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks
public import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Acquire common prefix preparations once from the retained trace geometry.
Both differential contact banks consume these same preparations and owners. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
      Meshes.PuncturedGridFaces.RegularFace
    bank}
  {firstModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames firstFace}
    {lastModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames lastFace}
  {start : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}
  {count : Nat}

variable {piece : Paths.RectangularPairedSegments.PairedSegmentPiece leftDomain.geometry rightDomain.geometry}

set_option genInjectivity false in
/-- Common-origin path preparation for the original rectangular paired trace.

Retain both domain owners and certify every prepared path lies in both original face boxes. -/
structure PairedTracePreparation (trace : Integration.RectangularPairedPointBanks.Trace piece count) where
  /-- The first original trace point is the retained common path origin. -/ origin_eq : trace.points 0 = start
  /-- The original common-origin routes to all retained trace vertices. -/ routes : Data.Vector.DependentVector (fun
    vertex =>
    Paths.ClearBoxPaths.Route curve.polynomial firstFace.cell.box start (trace.points vertex))
  /-- The exact original path preparations using the retained root owner. -/ prepared : Data.Vector.DependentVector (fun
    vertex => Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (routes.get vertex).path owner)
  /-- Every original prepared path stays inside the first retained face box. -/ leftInside : ∀ vertex, (routes.get
    vertex).path.InBox firstFace.cell.box
  /-- Every original prepared path stays inside the second retained face box. -/ rightInside : ∀ vertex, (routes.get
    vertex).path.InBox lastFace.cell.box

constructive_injectivity PairedTracePreparation

namespace PairedTracePreparation

/-- The retained axis-aligned route lies in any box containing both original endpoints. -/
public theorem route_inBox {polynomial : Geometry.ClearPath.GaussianPolynomial} {box other :
  Rational.Box}
    (clearance : Clearance.Box.Region.RegionClearance polynomial box)
    (start finish : Gaussian.Basic.Canonical) (first : box.Contains start) (last : box.Contains finish)
    (otherFirst : other.Contains start) (otherLast : other.Contains finish) :
    (Paths.ClearBoxPaths.Route.build clearance start finish first last).path.InBox other := by
  unfold Paths.ClearBoxPaths.Route.build
  split
  · rename_i equal
    subst finish
    exact otherFirst
  · dsimp only
    split
    · exact ⟨otherFirst, otherLast⟩
    · split
      · exact ⟨otherFirst, otherLast⟩
      · exact ⟨otherFirst, ⟨otherLast.1, otherLast.2.1, otherFirst.2.2⟩, otherLast⟩

/-- Prepare the actual trace paths once from the retained common root and both face-containment certificates. -/
def build (trace : Integration.RectangularPairedPointBanks.Trace piece count) (origin_eq : trace.points 0 = start) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation.PairedTracePreparation trace := by
  have leftPoint : ∀ vertex, firstFace.cell.box.Contains (trace.points vertex) := fun vertex =>
    (leftDomain.patch.cell_refines piece.leftColumn piece.leftRow).contains (trace.left_contains vertex)
  have rightPoint : ∀ vertex, lastFace.cell.box.Contains (trace.points vertex) := fun vertex =>
    (rightDomain.patch.cell_refines piece.rightColumn piece.rightRow).contains (trace.right_contains vertex)
  have leftStart : firstFace.cell.box.Contains start := origin_eq ▸ leftPoint 0
  have rightStart : lastFace.cell.box.Contains start := origin_eq ▸ rightPoint 0
  let routes := Data.Vector.DependentVector.ofFn fun vertex =>
    Paths.ClearBoxPaths.Route.build firstFace.clearance start (trace.points vertex) leftStart (leftPoint vertex)
  refine ⟨origin_eq, routes, Data.Vector.DependentVector.ofFn (fun vertex =>
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.build (routes.get vertex).path
      (routes.get vertex).within owner), ?_, ?_⟩
  · intro vertex
    exact Geometry.ClearPath.InBox.ofWithin (routes.get vertex).path (routes.get vertex).within leftStart
  · intro vertex
    dsimp only [routes]
    rw [Data.Vector.DependentVector.ofFn_get]
    exact Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation.PairedTracePreparation.route_inBox
      firstFace.clearance start (trace.points vertex)
      leftStart (leftPoint vertex) rightStart (rightPoint vertex)

/-- Prepare the selected differential's original contact caches from the retained shared paths and two domain owners. -/
def contacts {trace : Integration.RectangularPairedPointBanks.Trace piece count}
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation.PairedTracePreparation trace)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
    Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain rightDomain
      (fun vertex => trace.points vertex) differential parentSheet :=
  Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank.build leftEntry rightEntry leftDomain
    rightDomain
    (fun vertex => trace.points vertex) preparation.origin_eq (fun _ => firstFace.cell.box)
    (fun vertex => (preparation.routes.get vertex).path) preparation.prepared
    preparation.leftInside preparation.rightInside differential parentSheet
    (Data.Vector.DependentVector.ofFn fun vertex =>
      Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache.build (preparation.prepared.get vertex)
      differential parentSheet)

end PairedTracePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation
