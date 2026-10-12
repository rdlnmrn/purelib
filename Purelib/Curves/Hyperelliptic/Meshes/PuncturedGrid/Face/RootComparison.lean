module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Owner.Transport

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
public import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.AlignedInverseRootSeed
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib

open Purelib.Data.Int

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Polynomial.Geometry.ClearPath

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Winding

open Purelib.Riemann.Branches

open Purelib.Riemann.Meshes.GridLiftedFaces

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.OwnerLoopMonodromy

open Purelib.Riemann.Paths.OwnerTracePath

open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.ClearBoxRootTransport

open Purelib.Riemann.Topology

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Owner

@[expose] public section

/-!
# Face models on the actual global root occurrence

The branch bank supplies the source reference internally. A cell's acquired
owner agrees with every alternative contained trace from the same face owner,
including a boundary path presented in the larger grid ambient. At the origin
of a rectangular bank, the aligned seed therefore names the actual supplied
global source occurrence, even for independently generated cell traces.

This identifies operational sheets. Comparison of primitive increments along
the entire exterior, and the resulting A/B period sums, is still separate.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels (RectangularModels)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank}
  {models : FaceModels frames face}
    {sheet : Fin 2} {inner : Purelib.Geometry.Rational.Box}

/-- The alternative route supplies only its actual trace and containment. The branch reference and equality of winding
are constructed, not premises. -/
def RootComparison.compareCellTrace (cell : TransportedFaceInverseModels.TransportedCell models.bounds
  (models.frame.owners sheet)
  inner)
    {ambient : Rational.Box} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient face.cell.box.anchor
      inner.anchor}
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners sheet)) (inside : ClearPath.InBox face.cell.box
      path)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval inner.anchor)) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName cell.traced.finishOwner)
      (OwnerTraceReadings.ownerName traced.finishOwner) :=
  TracedPath.equivalentOfInBox face.clearance (BranchIsolation.degreePositive curve)
    (BranchCellBank.referenceAt bank _ (Cell.anchor_mem face.cell face.member)).toLoop cell.route.within cell.traced
      traced
    (Polynomial.Geometry.ClearPath.InBox.ofWithin cell.route.path cell.route.within face.cell.box.contains_anchor)
      inside frame

/-- Alignment refines the acquired occurrence, rather than selecting a fresh square root. This bridge consumes the
seed's existing containment. -/
def RootComparison.seedEquivalent (cell : TransportedFaceInverseModels.TransportedCell models.bounds
  (models.frame.owners sheet) inner)
  :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName cell.aligned.seed.owner)
      (OwnerTraceReadings.ownerName cell.traced.finishOwner) :=
  (PreparedPrimitiveSheets.rootEquivalent_of_initial_refines cell.traced.finishOwner.parameterNonzero
    cell.traced.finishOwner.track cell.aligned.seed.owner.track cell.aligned.refines).symm

/-- Transporting the original root owner along equality of its radicand preserves its exact retained name. -/
public theorem RootComparison.ownerName_castParameter {source target : Data.Gaussian.Basic.Canonical} (equal : source =
  target)
    (owner : SquareRootContinuationChain.Owner source) :
    OwnerTraceReadings.ownerName (Transport.castOwnerParameter equal owner) = OwnerTraceReadings.ownerName owner := by
  cases equal
  rfl

/-- Any contained acquisition ending at the source corner returns to the actual supplied owner. Even generated
nontrivial closed routes are allowed. -/
def RootComparison.sourceEquivalent (cell : TransportedFaceInverseModels.TransportedCell models.bounds
  (models.frame.owners sheet)
  inner)
    (anchor : inner.anchor = face.cell.box.anchor) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName cell.traced.finishOwner)
      (OwnerTraceReadings.ownerName (models.frame.owners sheet)) := by
  let returned := Transport.castOwnerParameter (congrArg curve.polynomial.eval anchor)
    cell.traced.finishOwner
  let loop : OwnerTracePath.OwnerPath curve.polynomial face.cell.box.anchor (models.frame.owners sheet)
    face.cell.box.anchor returned :=
    cell.traced.trace.get.castEndpoints rfl anchor HEq.rfl
      (Transport.castOwnerParameter_heq _ _).symm
  have winding : Polygon.Basic.chainRaw curve.polynomial face.cell.box.anchor loop.vertices = 8 * (0 : Int) := by
    change Polygon.Basic.chainRaw curve.polynomial face.cell.box.anchor
      (cell.traced.trace.get.castEndpoints rfl anchor HEq.rfl
        (Transport.castOwnerParameter_heq _ _).symm).vertices = _
    rw [OwnerPath.castEndpoints_vertices, TracedPath.winding_original cell.traced,
      Route.winding face.clearance (BranchIsolation.degreePositive curve) cell.route face.cell.box.contains_anchor,
      anchor, Arithmetic.sub_eq_zero_of_eq rfl]
    rfl
  have equivalent := OwnerPath.rootEquivalent_of_even_with_reference
    (BranchCellBank.referenceAt bank _ (Cell.anchor_mem face.cell face.member)).toLoop loop 0 winding
  change Gaussian.Equivalence.NamedEquivalent
    (OwnerTraceReadings.ownerName (Transport.castOwnerParameter _ _)) _ at equivalent
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RootComparison.ownerName_castParameter] at equivalent
  exact equivalent

namespace InverseModels.BranchCellBank.FaceModels.RectangularModels

/-- The rectangular gauge's origin seed belongs to the actual first-corner sheet of the global face frame, with no
separate root-agreement certificate. -/
def
  originSeedEquivalent
  (rectangles : FaceModels.RectangularModels models) (sheet : Fin 2) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (((rectangles.patch sheet).transported.cell 0
      0).aligned.seed.owner))
      (OwnerTraceReadings.ownerName (models.frame.owners sheet)) :=
  let cell := (rectangles.patch sheet).transported.cell 0 0
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RootComparison.seedEquivalent cell).trans
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RootComparison.sourceEquivalent cell rectangles.anchor_eq)

/-- The same occurrence is the first vertex of the existing lifted face, not merely an independently numbered sheet of
the analytic model bank. -/
def
  originLiftedEquivalent
  (rectangles : FaceModels.RectangularModels models)
    {vertices : LiftedVertices.VertexBank bank.grid} {edges : RootEdgeBank frames}
    (lifted : BranchCellBank.LiftedFace vertices edges face sheet) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (((rectangles.patch sheet).transported.cell 0
      0).aligned.seed.owner))
      (OwnerTraceReadings.ownerName (vertices.owner frames lifted.quad.first)) := by
  rw [← models.source_name lifted]
  exact rectangles.originSeedEquivalent sheet

end InverseModels.BranchCellBank.FaceModels.RectangularModels

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
