module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Meshes.RectangularFaceModels
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Riemann.Meshes.GridLiftedFaceLocations
public import Purelib.Data.Fin
import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedFaces

open Purelib.Riemann.Meshes.RectangularFaceModels

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.TransportedFaceInverseModels

open Purelib.Riemann.Paths

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

@[expose] public section

/-!
# Local inverse-root models attached to actual lifted grid faces

The two sheet queries share one cached geometric budget and one retained
root frame. Their source occurrences are exactly those at the first corner
of the existing lifted quadrilaterals. Queries locate one dyadic child,
transport the selected occurrence, and retain the resulting polynomial data;
they do not enumerate the exponentially larger complete refinement mesh.
-/

namespace Purelib

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularLayout RectangularPatch)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)

namespace RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

/-- Looking up an original vertex and sheet retains the owner name from that same root frame. -/
theorem ownerName_index {polynomial :
  ClearPath.GaussianPolynomial} {ambient : Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient}
    (vertices : LiftedVertices.VertexBank grid) (frames : RootFrames grid) (point :
      Data.Gaussian.Basic.Canonical) (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point)
    (sheet : Fin 2) : OwnerTraceReadings.ownerName (vertices.owner frames (vertices.index point member sheet)) =
      OwnerTraceReadings.ownerName ((frames.frameAt point member).owners sheet) := by
  unfold VertexBank.owner
  rw [VertexBank.sheet_index]
  have names : ∀ first last (left : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid first) (right :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex grid last),
      first = last → OwnerTraceReadings.ownerName ((frames.frameAt first left).owners sheet) =
        OwnerTraceReadings.ownerName ((frames.frameAt last right).owners sheet) := by
    intro first last left right equal
    cases equal
    rfl
  exact names _ _ _ _ (vertices.coordinate_index point member sheet)

end RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}

set_option genInjectivity false in
/-- The executable geometry and frame are shared across both sheets and all point/accuracy requests on this face. -/
structure FaceModels (frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid) (face :
    PuncturedGridFaces.RegularFace bank) where
  /-- The cached polynomial and clearance bounds of the original regular face. -/ bounds :
    RegularFaceInverseModels.Bounds face.clearance
  /-- The retained finite dyadic mesh for these exact face bounds. -/ mesh : RegularFaceInverseModels.Mesh bounds
  /-- The cached original two-sheet root frame at the face anchor. -/ frame : RootOwnerFrames.OwnerFrame
    (curve.polynomial.eval face.cell.box.anchor)
  /-- The cached frame is exactly the original grid frame at this face anchor. -/ frame_eq : frame = frames.frameAt
    face.cell.box.anchor (Cell.anchor_mem face.cell face.member)

constructive_injectivity FaceModels

namespace FaceModels

variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
  RegularFace bank}

/-- Cache the original face bounds, dyadic mesh and grid root frame once for both sheet queries. -/
def build (frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid) (face : PuncturedGridFaces.RegularFace bank) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face :=
  let bounds := RegularFaceInverseModels.Bounds.build face.clearance
  ⟨bounds, Mesh.build bounds, frames.frameAt face.cell.box.anchor (Cell.anchor_mem face.cell face.member), rfl⟩

/-- Synchronize with a later common mesh depth without rebuilding the polynomial majorants or the face's root frame. -/
def atDepth (models : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames
  face) (depth : Nat) (later : models.mesh.depth ≤ depth) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face :=
  ⟨models.bounds, models.mesh.atDepth depth later, models.frame, models.frame_eq⟩

/-- The retained face-model sheet owner has the same name as the original lifted quadrilateral's first vertex owner. -/
theorem source_name {vertices : LiftedVertices.VertexBank bank.grid} {edges : RootEdgeBank frames}
    (models : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face) {sheet
      : Fin 2} (lifted : BranchCellBank.LiftedFace vertices edges face sheet) :
    OwnerTraceReadings.ownerName (models.frame.owners sheet) = OwnerTraceReadings.ownerName (vertices.owner frames
      lifted.quad.first) := by
  rw [lifted.first_eq, RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank.ownerName_index, models.frame_eq]

set_option genInjectivity false in
/-- A retained point location and transported inverse-root cell on the original requested sheet.

The covering box belongs to the cached mesh, and the cell retains its original source frame owner. -/
structure Query (models : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames
  face) (sheet : Fin 2) (point : Data.Gaussian.Basic.Canonical) where
  /-- The retained mesh box containing the requested original point. -/ located : models.mesh.Located point
  /-- The transported inverse-root cell from the exact original source sheet to the retained query box. -/ cell :
    TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet) located.box

constructive_injectivity Query

/-- Total model acquisition on the requested sheet, from face data alone. The result keeps both the covering witness and
the actual owner thread. -/
def query (models : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face)
  (sheet : Fin 2) (point : Data.Gaussian.Basic.Canonical)
    (inside : face.cell.box.Contains point) :
      Query models sheet point :=
  let located := models.mesh.locate point inside
  ⟨located, TransportedCell.acquire (models.mesh.cellGeometry located.member) (models.frame.owners sheet)⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels in
/-- A query already contains the geometric evidence needed at its requested point; callers need only supply the positive
accuracy target. -/
theorem query_residual_lt {models :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
  {point : Data.Gaussian.Basic.Canonical}
    (query : Query models sheet
      point) {target : Fraction.Rational}
    (request : TransportedCell.Request query.cell target) :
    Data.Gaussian.Norm.Basic.normSq
      (1 - curve.polynomial.eval point * (request.model.value.eval point) ^ 2) < target :=
  request.residual_lt point query.located.contains

set_option genInjectivity false in
/-- Both actual lifted sheets share the materialized axes and face budget. Each retains its own operational source, cell
traces and computed gauge. -/
structure RectangularModels (models :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face) where
  /-- The retained number of dyadic intervals per rectangular axis. -/ steps : Nat
  /-- The rectangular step count is exactly the original face mesh's dyadic count. -/ steps_eq : steps =
    Geometry.Rectangle.Partition.RectangularUniformGeometry.dyadicSteps models.mesh.depth
  /-- The shared original rectangular geometry for both lifted sheets. -/ geometry : RectangularInverseModels.Geometry
    steps steps
  /-- The retained face-model layout on this exact shared rectangular geometry. -/ layout :
    RectangularFaceModels.RectangularLayout models.bounds geometry
  /-- The first retained rectangle has the original face anchor. -/ anchor_eq : (geometry.box 0 0).anchor =
    face.cell.box.anchor
  /-- The cached rectangular model patch on the original zero sheet. -/ zero : RectangularFaceModels.RectangularPatch
    models.bounds (models.frame.owners 0) geometry
  /-- The cached rectangular model patch on the original one sheet. -/ one : RectangularFaceModels.RectangularPatch
    models.bounds (models.frame.owners 1) geometry

constructive_injectivity RectangularModels

/-- Construct the complete compatible interior model banks from the face, with no caller-provided rectangle, owner,
polynomial or sign certificates. -/
def rectangular (models : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames
  face) : RectangularModels
  models :=
  let steps := Geometry.Rectangle.Partition.RectangularUniformGeometry.dyadicSteps models.mesh.depth
  let geometry := Geometry.Rectangle.Partition.RectangularUniformGeometry.uniform face.cell.box face.cell.box_proper
      steps
  let layout := RectangularLayout.ofMesh models.mesh face.cell.box_proper
  ⟨steps, rfl, geometry, layout, Geometry.Rectangle.Partition.RectangularUniformGeometry.uniform_anchor _ _ _,
    RectangularPatch.acquire layout (models.frame.owners 0),
    RectangularPatch.acquire layout (models.frame.owners 1)⟩

/-- Read the cached rectangular patch for the requested original sheet. -/
def RectangularModels.patch {models :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} (rectangles :
  RectangularModels models) :
    (sheet : Fin 2) → RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet)
      rectangles.geometry :=
  Data.Fin.casesByRecursion rectangles.zero (Data.Fin.casesByRecursion rectangles.one (fun empty => Fin.elim0 empty))

end FaceModels

end Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.LiftedPuncturedGrid

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

set_option genInjectivity false in
/-- Lookup and cache both actual quadrilateral occurrences once. This connects the analytic queries to the existing
triangulation indices. -/
structure ModelFace (lifted : Meshes.LiftedPuncturedGrid base) (position : Fin base.faces.regulars.length) where
  /-- The cached local inverse-root geometry and frame for this original regular-face position. -/ models :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels lifted.frames
    base.faces.regulars[position.val]
  /-- The cached original lifted quadrilateral at this face position on sheet zero. -/ zero : lifted.mesh.LocatedFace
    position 0
  /-- The cached original lifted quadrilateral at this face position on sheet one. -/ one : lifted.mesh.LocatedFace
    position 1

constructive_injectivity ModelFace

namespace ModelFace

variable {lifted : LiftedPuncturedGrid base} {position : Fin base.faces.regulars.length}

/-- Cache the original face models and both exact lifted quadrilateral occurrences at the retained position. -/
def build (lifted : Meshes.LiftedPuncturedGrid base) (position : Fin base.faces.regulars.length) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.LiftedPuncturedGrid.ModelFace lifted position :=
  ⟨BranchCellBank.FaceModels.build lifted.frames base.faces.regulars[position.val],
    lifted.mesh.locateFace position 0, lifted.mesh.locateFace position 1⟩

/-- Read the cached lifted face occurrence on the requested original sheet. -/
def location (face : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.LiftedPuncturedGrid.ModelFace lifted
  position) : (sheet : Fin 2) → lifted.mesh.LocatedFace position sheet :=
  Data.Fin.casesByRecursion face.zero (Data.Fin.casesByRecursion face.one (fun empty => Fin.elim0 empty))

/-- The retained face-model sheet owner has the same name as the original lifted quadrilateral's first vertex owner. -/
theorem source_name (face : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.LiftedPuncturedGrid.ModelFace
  lifted position) (sheet : Fin 2) :
    OwnerTraceReadings.ownerName (face.models.frame.owners sheet) =
      OwnerTraceReadings.ownerName (lifted.vertices.owner lifted.frames (face.location sheet).lifted.quad.first) :=
  face.models.source_name (face.location sheet).lifted

end ModelFace

end Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.LiftedPuncturedGrid

end Purelib

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels
namespace RectangularModels

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels.RectangularModels
