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
public import Purelib.Riemann.Meshes.PuncturedFaceLookup
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
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace RegularLocation)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches
    higher}
  {frames : RootFrames bank.grid}

set_option genInjectivity false in
/-- A retained regular-face model cache with lazily acquired domains for its two sheets.

Each sheet domain depends on the same cached models and is evaluated only when requested. -/
structure FaceDomains (frames : RootFrames bank.grid) (face :
    RegularFace bank) where
  /-- The cached analytic models on this exact retained regular face. -/ models : FaceModels frames face
  /-- The lazy local domain on sheet zero of the retained model cache. -/ zero : Thunk (PeriodDomain models 0)
  /-- The lazy local domain on sheet one of the retained model cache. -/ one : Thunk (PeriodDomain models 1)

constructive_injectivity FaceDomains

namespace FaceDomains

/-- Cache the face models and delay each sheet's domain acquisition independently. -/
def build (frames : RootFrames bank.grid) (face : RegularFace bank) :
  FaceDomains frames face :=
  let models := FaceModels.build frames face
  ⟨models, ⟨fun _ => PeriodDomain.build models 0⟩, ⟨fun _ => PeriodDomain.build models 1⟩⟩

/-- Read the requested sheet's cached local analytic domain. -/
def domain {face : RegularFace bank} (cached :
  FaceDomains frames face) :
    (sheet : Fin 2) → PeriodDomain cached.models sheet
  | ⟨0, _⟩ => cached.zero.get
  | ⟨1, _⟩ => cached.one.get
  | ⟨_ + 2, impossible⟩ => (by omega : False).elim

/-- Reading sheet zero returns its retained lazy domain. -/
theorem domain_zero {face : RegularFace bank} (cached :
  FaceDomains frames face) :
    cached.domain 0 = cached.zero.get := rfl

/-- Reading sheet one returns its retained lazy domain. -/
theorem domain_one {face : RegularFace bank} (cached :
  FaceDomains frames face) :
    cached.domain 1 = cached.one.get := rfl

/-- Transport the face-domain cache along equality of its actual face owner. -/
def castFace {first last : RegularFace bank} (equal : first = last) (cached :
  FaceDomains frames first) :
    FaceDomains frames last := by
  cases equal
  exact cached

end FaceDomains

set_option genInjectivity false in
/-- A lazy analytic-domain cache indexed by the exact ordered list of retained regular faces. -/
inductive FaceDomainBank (frames : RootFrames bank.grid) : List
    (RegularFace bank) → Type
  /-- The empty cache for an empty regular-face list. -/ | nil :
    FaceDomainBank frames []
  /-- Extend the cache with a lazy domain bank for its exact first face. -/ | cons {face :
    RegularFace bank} {faces : List (RegularFace bank)}
      (first : Thunk (FaceDomains frames face)) (remaining :
        FaceDomainBank frames faces) :
      FaceDomainBank frames (face :: faces)

constructive_injectivity FaceDomainBank

namespace FaceDomainBank

/-- Prepare a lazy domain entry for each exact face in the retained list without acquiring untouched domains. -/
def build (frames : RootFrames bank.grid) : (faces : List (RegularFace
    bank)) →
  FaceDomainBank frames faces
  | [] => .nil
  | face :: faces => .cons ⟨fun _ => FaceDomains.build frames
    face⟩ (FaceDomainBank.build frames faces)

/-- Read the cached domains at the supplied bounded regular-face position. -/
def get : {faces : List (RegularFace bank)} → (cached :
  FaceDomainBank frames faces) →
    (position : Fin faces.length) → FaceDomains frames
      faces[position.val]
  | _, .nil, position => Fin.elim0 position
  | _, .cons first _, ⟨0, _⟩ => first.get
  | _, .cons _ remaining, ⟨index + 1, bound⟩ => remaining.get ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Read the same complete face-domain cache at an original retained regular-cell location.

The location's actual index selects the shared bank entry. Its retained
whole-face equality transports that cache without another membership
search, face-model construction or domain acquisition.
-/
def atLocation {faces : List (RegularFace bank)}
    (cached : FaceDomainBank frames faces) {cell : Cell curve.polynomial (Branches.Cuts.Ambient curve)}
    (location : RegularLocation faces cell) : FaceDomains frames location.face :=
  (cached.get location.index).castFace location.indexed

/-- The location readback is the complete original indexed cache with its same whole-face transport. -/
theorem atLocation_eq {faces : List (RegularFace bank)}
    (cached : FaceDomainBank frames faces) {cell : Cell curve.polynomial (Branches.Cuts.Ambient curve)}
    (location : RegularLocation faces cell) :
    cached.atLocation location = (cached.get location.index).castFace location.indexed := rfl

/-- The exact face equality permits generated caches; no fresh membership search, model construction, or root transport
occurs on a cache hit. -/
def atRoute {vertices : LiftedVertices.VertexBank bank.grid} {edges : RootEdgeBank frames}
    {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}
    (cached : FaceDomainBank frames faces.regulars) {edge :
      Stokes.OrientedEdge vertices.count}
    (route : MeshPathWalks.EdgeRoute mesh edge) : FaceDomains
      frames route.face :=
  (cached.get route.position).castFace route.face_eq

end FaceDomainBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
