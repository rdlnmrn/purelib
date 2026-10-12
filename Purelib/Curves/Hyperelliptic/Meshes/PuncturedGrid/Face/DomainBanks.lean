module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries
import Init.Core
import Init.Data.Fin.Basic
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods

open Purelib.Riemann.Meshes

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Topology.Polygon

@[expose] public section

/-!
# Shared local analytic domains indexed by retained grid faces

Each finite face position has one memoized model cache and one memoized
domain per sheet. Repeated path occurrences read that cache by their retained
position; untouched faces and sheets do not run analytic acquisition.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

set_option genInjectivity false in
/-- A retained regular-face model cache with lazily acquired domains for its two sheets.

Each sheet domain depends on the same cached models and is evaluated only when requested. -/
structure FaceDomains (frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid) (face :
    PuncturedGridFaces.RegularFace bank) where
  /-- The cached analytic models on this exact retained regular face. -/ models : BranchCellBank.FaceModels frames face
  /-- The lazy local domain on sheet zero of the retained model cache. -/ zero : Thunk (Periods.PeriodDomain models 0)
  /-- The lazy local domain on sheet one of the retained model cache. -/ one : Thunk (Periods.PeriodDomain models 1)

constructive_injectivity FaceDomains

namespace FaceDomains

/-- Cache the face models and delay each sheet's domain acquisition independently. -/
def build (frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid) (face : PuncturedGridFaces.RegularFace bank) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face :=
  let models := FaceModels.build frames face
  ⟨models, ⟨fun _ => PeriodDomain.build models 0⟩, ⟨fun _ => PeriodDomain.build models 1⟩⟩

/-- Read the requested sheet's cached local analytic domain. -/
def domain {face : PuncturedGridFaces.RegularFace bank} (cached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face) :
    (sheet : Fin 2) → Periods.PeriodDomain cached.models sheet
  | ⟨0, _⟩ => cached.zero.get
  | ⟨1, _⟩ => cached.one.get
  | ⟨_ + 2, impossible⟩ => (by omega : False).elim

/-- Reading sheet zero returns its retained lazy domain. -/
theorem domain_zero {face : PuncturedGridFaces.RegularFace bank} (cached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face) :
    cached.domain 0 = cached.zero.get := rfl

/-- Reading sheet one returns its retained lazy domain. -/
theorem domain_one {face : PuncturedGridFaces.RegularFace bank} (cached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face) :
    cached.domain 1 = cached.one.get := rfl

/-- Transport the face-domain cache along equality of its actual face owner. -/
def castFace {first last : PuncturedGridFaces.RegularFace bank} (equal : first = last) (cached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames first) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames last := by
  cases equal
  exact cached

end FaceDomains

set_option genInjectivity false in
/-- A lazy analytic-domain cache indexed by the exact ordered list of retained regular faces. -/
inductive FaceDomainBank (frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid) : List
    (PuncturedGridFaces.RegularFace bank) → Type
  /-- The empty cache for an empty regular-face list. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames []
  /-- Extend the cache with a lazy domain bank for its exact first face. -/ | cons {face :
    PuncturedGridFaces.RegularFace bank} {faces : List (PuncturedGridFaces.RegularFace bank)}
      (first : Thunk (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face)) (remaining :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces) :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames (face :: faces)

constructive_injectivity FaceDomainBank

namespace FaceDomainBank

/-- Prepare a lazy domain entry for each exact face in the retained list without acquiring untouched domains. -/
def build (frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid) : (faces : List (PuncturedGridFaces.RegularFace
    bank)) →
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces
  | [] => .nil
  | face :: faces => .cons ⟨fun _ => Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains.build frames
    face⟩ (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank.build frames faces)

/-- Read the cached domains at the supplied bounded regular-face position. -/
def get : {faces : List (PuncturedGridFaces.RegularFace bank)} → (cached :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces) →
    (position : Fin faces.length) → Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames
      faces[position.val]
  | _, .nil, position => Fin.elim0 position
  | _, .cons first _, ⟨0, _⟩ => first.get
  | _, .cons _ remaining, ⟨index + 1, bound⟩ => remaining.get ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- The exact face equality permits generated caches; no fresh membership search, model construction, or root transport
occurs on a cache hit. -/
def atRoute {vertices : LiftedVertices.VertexBank bank.grid} {edges : RootEdgeBank frames}
    {faces : PuncturedGridFaces.PuncturedFaces bank} {mesh : GridLiftedMesh.LiftedMesh vertices edges faces}
    (cached : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) {edge :
      Stokes.OrientedEdge vertices.count}
    (route : MeshPathWalks.EdgeRoute mesh edge) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains
      frames route.face :=
  (cached.get route.position).castFace route.face_eq

end FaceDomainBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
