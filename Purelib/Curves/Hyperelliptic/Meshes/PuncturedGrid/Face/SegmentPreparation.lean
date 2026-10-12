module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels

open Purelib.Riemann.Topology

@[expose] public section

/-! Prepare a comparison segment from a specified retained face sheet, even
when its first point is a fine trace vertex. The forward route selects the
actual incoming owner once; later differential requests reuse that owner and
the covered segment. No original-grid-vertex classification is required. -/
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank}
  {ambient : Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}

namespace SegmentPreparation

set_option genInjectivity false in
/-- A cached incoming owner on one specified face sheet. -/
structure ForwardOwner (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2) (point :
  Data.Gaussian.Basic.Canonical) where
  /-- The retained incoming root owner at the actual segment start. -/ owner : SquareRootContinuationChain.Owner
    (curve.polynomial.eval point)
  /-- The cached face-sheet trace reaches this exact incoming owner. -/ reached : PreparedFaceTracePrefixes.Reached
    face.cell.box (models.frame.owners sheet) owner

constructive_injectivity ForwardOwner

end SegmentPreparation

namespace SegmentPreparation.ForwardOwner

/-- The retained forward trace certifies the chosen sheet at any contained point. Downstream segment requests reuse its
owner without tracing again. -/
def build (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2)
    (point : Data.Gaussian.Basic.Canonical) (inside : face.cell.box.Contains point) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SegmentPreparation.ForwardOwner models sheet point :=
  let route := Route.build face.clearance face.cell.box.anchor point
    face.cell.box.contains_anchor inside
  let forward := TracedPath.build route.path route.within (models.frame.owners sheet)
  ⟨forward.finishOwner, forward.trace.get, (TracedPath.winding_original forward).trans
    (Route.winding face.clearance
      (BranchIsolation.degreePositive curve) route face.cell.box.contains_anchor)⟩

end SegmentPreparation.ForwardOwner

set_option genInjectivity false in
/-- The original owner and covered piece are shared by all differentials. -/
structure SegmentPreparation (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2)
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish) where
  /-- The retained incoming root owner at the actual segment start. -/ owner : SquareRootContinuationChain.Owner
    (curve.polynomial.eval start)
  /-- The cached face-sheet trace reaches this exact incoming owner. -/ reached : PreparedFaceTracePrefixes.Reached
    face.cell.box (models.frame.owners sheet) owner
  /-- The cached covered segment prepared from the retained incoming owner. -/ piece :
    PreparedPathDecomposition.CoveredSegment segment owner
  /-- The prepared segment remains within the original regular-face box. -/ inside : (ClearPath.cons segment (.nil
    finish)).InBox face.cell.box

constructive_injectivity SegmentPreparation

namespace SegmentPreparation

variable {models : FaceModels frames
  face} {sheet : Fin 2}
  {segment : ClearSegment curve.polynomial ambient start finish}

/-- Reuse a cached incoming owner for all comparison segments starting at this point, and prepare each segment only once
for both differential consumers. -/
def ofOwner (incoming : ForwardOwner models sheet
  start)
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (firstInside : face.cell.box.Contains start) (lastInside : face.cell.box.Contains finish) :
    SegmentPreparation models sheet segment :=
  ⟨incoming.owner, incoming.reached, CoveredSegment.build segment within incoming.owner,
    firstInside, lastInside⟩

/-- The supplied shared domain and parent cache remain literal fields of the comparison. Only its split geometry is
constructed here. -/
def entered (prepared : SegmentPreparation models
  sheet segment)
    (domain : Periods.PeriodDomain models sheet) (differential : Differentials.Basic.Differential genus)
    (parents : PreparedClearPathModels.ParentCache prepared.piece.path differential sheet) :=
  EnteredPath.ofEntry ⟨sheet, prepared.reached⟩ domain prepared.piece.path prepared.inside
    differential sheet parents

/-- A single horizontal segment, including a stationary owner junction. -/
def horizontalSegment (_models : BranchCellBank.FaceModels frames face) (start finish : Data.Gaussian.Basic.Canonical)
    (first : face.cell.box.Contains start) (last : face.cell.box.Contains finish)
    (height : start.im = finish.im) : ClearPath.ClearSegment curve.polynomial face.cell.box start finish :=
  let edge := ClearSegment.horizontal start.re finish.re start.im first.1 first.2.1 last.1 last.2.1
    (ClearBoxPaths.horizontal face.clearance start.im first.2.2)
  edge.castFinish (Data.Gaussian.Basic.ext rfl height)

/-- The constructed horizontal comparison segment lies in its retained ambient face box. -/
theorem horizontalSegment_within (models : BranchCellBank.FaceModels frames face) (start finish :
  Data.Gaussian.Basic.Canonical)
    (first : face.cell.box.Contains start) (last : face.cell.box.Contains finish)
    (height : start.im = finish.im) :
      (horizontalSegment
      models start finish first last height).WithinAmbient := by
  unfold horizontalSegment
  apply ClearSegment.castFinish_withinAmbient
  exact first.2.2

/-- A single vertical segment, with either orientation and no positive-length premise, so coincident readings are still
compared. -/
def verticalSegment (_models : BranchCellBank.FaceModels frames face) (start finish : Data.Gaussian.Basic.Canonical)
    (first : face.cell.box.Contains start) (last : face.cell.box.Contains finish)
    (horizontal : start.re = finish.re) : ClearPath.ClearSegment curve.polynomial face.cell.box start finish :=
  let edge := ClearSegment.vertical start.re start.im finish.im first.2.2.1 first.2.2.2 last.2.2.1 last.2.2.2
    (ClearBoxPaths.vertical face.clearance start.re ⟨first.1, first.2.1⟩)
  edge.castFinish (Data.Gaussian.Basic.ext horizontal rfl)

/-- The constructed vertical comparison segment lies in its retained ambient face box. -/
theorem verticalSegment_within (models : BranchCellBank.FaceModels frames face) (start finish :
  Data.Gaussian.Basic.Canonical)
    (first : face.cell.box.Contains start) (last : face.cell.box.Contains finish)
    (horizontal : start.re = finish.re) :
      (verticalSegment
      models start finish first last horizontal).WithinAmbient := by
  unfold verticalSegment
  apply ClearSegment.castFinish_withinAmbient
  exact ⟨first.1, first.2.1⟩

end SegmentPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
