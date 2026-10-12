module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
public import Purelib.Riemann.Readings.RectangularPointReadings
import Init.Core
import Init.Data.Fin.Basic
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.LinearAlgebra.Grid

open Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularPrimitiveGluing

open Purelib.Riemann.Integration.RectangularPrimitiveModels

open Purelib.Riemann.Meshes

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularPointReadings

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Topology.Polygon

@[expose] public section

/-!
# Shared numerical primitives for retained face domains

One requested index and differential determine a memoized primitive, anchor,
offset and four-corner bank on each used face and sheet. Untouched faces and
sheets do not construct polynomials. The fixed corner values are independent
of the fine mesh; comparing its other readings still pays ownership errors.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains FaceDomainBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners (point inside)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

set_option genInjectivity false in
/-- Cached numerical primitives and four-corner readings for one actual retained face-sheet domain.

The differential and stage select the primitive bank, while anchors, offsets and corner owners are computed once and
shared by all fine-mesh comparisons. -/
structure DomainPrimitives {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face}
  {sheet : Fin 2}
    (domain : Periods.PeriodDomain models sheet) (differential : Differentials.Basic.Differential genus) (index : Nat)
      where
  /-- The cached oriented primitive polynomials for the retained domain, differential and stage. -/ primitives :
    RectangularPrimitiveModels.Primitives (Transitions.oriented (domain.patch.sheets.refine index).transitions
    (domain.patch.sheets.refine index).gauge) (PreparedPrimitiveSamples.differentialNumerator differential)
  /-- The cached primitive anchors on these exact retained polynomials. -/ anchors :
    RectangularPrimitiveGluing.PrimitiveAnchors primitives
  /-- The cached gluing offsets on the actual anchor edges. -/ offsets : LinearAlgebra.Grid.Offsets anchors.edges
  /-- The cached four-corner readings with their retained owners. -/ corners : RectangularPointReadings.PointReadings
    anchors offsets (FaceCorners.point face.cell.box)

constructive_injectivity DomainPrimitives

namespace DomainPrimitives

/-- Cache the retained domain's primitive polynomials, anchors, offsets and four original corner-owner readings. -/
def build {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    (domain : Periods.PeriodDomain models sheet) (differential : Differentials.Basic.Differential genus) (index : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain differential index :=
  let sheets := domain.patch.sheets.refine index
  let primitives := Primitives.build (Transitions.oriented sheets.transitions sheets.gauge)
    (PreparedPrimitiveSamples.differentialNumerator differential)
  let anchors := PrimitiveAnchors.build primitives
  let offsets := anchors.offsets
  let owners := Data.Vector.Basic.vectorOfFn fun corner =>
    let located := PeriodDomain.locate domain
      (FaceCorners.point face.cell.box corner)
      (FaceCorners.inside face.cell.box corner)
    (⟨located.column, located.row, FaceCorners.point face.cell.box corner, located.inside⟩ :
      RectangularOwnedTriangulation.OwnedVertex domain.geometry)
  let corners := PointReadings.build anchors offsets (FaceCorners.point face.cell.box) owners
    (fun corner => by rw [Data.Vector.Basic.vectorOfFn_apply])
  ⟨primitives, anchors, offsets, corners⟩

/-- Transport the numerical cache along equality of its exact domain owner. -/
def castDomain {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face} {sheet :
  Fin 2}
    {first last : Periods.PeriodDomain models sheet} {differential : Differentials.Basic.Differential genus} {index :
      Nat}
    (equal : first = last) (cached : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives first
      differential index) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives last
      differential index := by
  cases equal
  exact cached

/-- Transporting the retained domain preserves all cached corner values. -/
theorem castDomain_corners {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face}
  {sheet : Fin 2}
    {first last : Periods.PeriodDomain models sheet} {differential : Differentials.Basic.Differential genus} {index :
      Nat}
    (equal : first = last) (cached : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives first
      differential index) :
    (cached.castDomain equal).corners.values = cached.corners.values := by
  cases equal
  rfl

end DomainPrimitives

set_option genInjectivity false in
/-- Lazy numerical primitive caches for both sheets of the same retained face-domain bank. -/
structure FacePrimitives {face : PuncturedGridFaces.RegularFace bank} (domains : DomainBanks.FaceDomains frames face)
  (differential : Differentials.Basic.Differential genus) (index : Nat) where
  /-- The lazy numerical cache for the exact retained sheet-zero domain. -/ zero : Thunk
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives (domains.domain 0) differential
    index)
  /-- The lazy numerical cache for the exact retained sheet-one domain. -/ one : Thunk
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives (domains.domain 1) differential
    index)

constructive_injectivity FacePrimitives

namespace FacePrimitives

/-- Delay numerical primitive construction separately for both sheets of the retained face. -/
def build {face : PuncturedGridFaces.RegularFace bank} (domains : DomainBanks.FaceDomains frames face) (differential :
  Differentials.Basic.Differential genus) (index : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives domains differential index :=
  ⟨⟨fun _ => Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.build (domains.domain 0)
    differential index⟩,
    ⟨fun _ => Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.build (domains.domain 1)
      differential index⟩⟩

/-- Read the requested sheet's cached primitives, offsets and corner values. -/
def atSheet {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face} {differential :
  Differentials.Basic.Differential genus} {index : Nat}
    (cached : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives domains differential index) :
      (sheet : Fin 2) → Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives (domains.domain
      sheet) differential index
  | ⟨0, _⟩ => cached.zero.get
  | ⟨1, _⟩ => cached.one.get
  | ⟨_ + 2, impossible⟩ => (by omega : False).elim

/-- Reading sheet zero returns its retained lazy numerical cache. -/
theorem atSheet_zero {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
  {differential : Differentials.Basic.Differential genus} {index : Nat}
    (cached : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives domains differential index) :
      cached.atSheet 0 = cached.zero.get := rfl

/-- Reading sheet one returns its retained lazy numerical cache. -/
theorem atSheet_one {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
  {differential : Differentials.Basic.Differential genus} {index : Nat}
    (cached : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives domains differential index) :
      cached.atSheet 1 = cached.one.get := rfl

/-- Transport the numerical cache along equality of its actual retained regular face. -/
def castFace {first last : PuncturedGridFaces.RegularFace bank} (equal : first = last) {domains :
  DomainBanks.FaceDomains frames first}
    {differential : Differentials.Basic.Differential genus} {index : Nat} (cached :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives domains differential index) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives (domains.castFace equal) differential
      index := by
  cases equal
  exact cached

/-- Transport the numerical cache along equality of its actual face-domain bank. -/
def castDomains {face : PuncturedGridFaces.RegularFace bank} {first last : DomainBanks.FaceDomains frames face} (equal :
  first = last)
    {differential : Differentials.Basic.Differential genus} {index : Nat} (cached :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives first differential index) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives last differential index := by
  cases equal
  exact cached

/-- Transporting the face-domain bank preserves each sheet's exact cached corner values. -/
theorem castDomains_corners {face : PuncturedGridFaces.RegularFace bank} {first last : DomainBanks.FaceDomains frames
  face} (equal : first = last)
    {differential : Differentials.Basic.Differential genus} {index : Nat} (cached :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives first differential index) (sheet : Fin
      2) :
    ((cached.castDomains equal).atSheet sheet).corners.values = (cached.atSheet sheet).corners.values := by
  cases equal
  rfl

end FacePrimitives

/-- A recursive product over the retained domain bank, not a second face enumeration or an independently acquired
collection of domains. -/
def FacePrimitiveBank (differential : Differentials.Basic.Differential genus) (index : Nat) :
    {faces : List (PuncturedGridFaces.RegularFace bank)} → DomainBanks.FaceDomainBank frames faces → Type
  | _, .nil => PUnit
  | _, .cons first remaining => Thunk (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives
    first.get differential index) ×
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index remaining

namespace FacePrimitiveBank

/-- Prepare lazy numerical entries on the exact existing domain-bank spine. -/
def build (differential : Differentials.Basic.Differential genus) (index : Nat) :
    {faces : List (PuncturedGridFaces.RegularFace bank)} → (domains : DomainBanks.FaceDomainBank frames faces) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains
  | _, .nil => ⟨⟩
  | _, .cons first remaining => ⟨⟨fun _ =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives.build first.get differential index⟩,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build differential index
    remaining⟩

/-- Read the retained numerical cache at its original bounded face position. -/
def get {differential : Differentials.Basic.Differential genus} {index : Nat} :
    {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains : DomainBanks.FaceDomainBank frames faces} → (cached
      : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) →
      (position : Fin faces.length) → Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives
        (domains.get position) differential index
  | _, .nil, _, position => Fin.elim0 position
  | _, .cons _ _, cached, ⟨0, _⟩ => cached.1.get
  | _, .cons _ _, cached, ⟨position + 1, bound⟩ =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.get cached.2 ⟨position,
    Nat.lt_of_succ_lt_succ bound⟩

/-- Read the exact retained face's numerical cache from the supplied path route without acquiring a new domain. -/
def atRoute {vertices : LiftedVertices.VertexBank bank.grid} {edges : RootEdgeBank frames}
    {faces : PuncturedGridFaces.PuncturedFaces bank} {mesh : GridLiftedMesh.LiftedMesh vertices edges faces} {domains :
      DomainBanks.FaceDomainBank frames faces.regulars}
    {differential : Differentials.Basic.Differential genus} {index : Nat} (cached :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains)
    {edge : Stokes.OrientedEdge vertices.count} (route : MeshPathWalks.EdgeRoute mesh edge) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives (domains.atRoute route) differential
      index :=
  (cached.get route.position).castFace route.face_eq

/-- One increment of the fixed four-value bank, retaining orientation and the actual selected sheet. This consumes no
path mesh or integration data. -/
def edgeIncrement {vertices : LiftedVertices.VertexBank bank.grid} {edges : RootEdgeBank frames}
    {faces : PuncturedGridFaces.PuncturedFaces bank} {mesh : GridLiftedMesh.LiftedMesh vertices edges faces} {domains :
      DomainBanks.FaceDomainBank frames faces.regulars}
    {differential : Differentials.Basic.Differential genus} {index : Nat} (cached :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains)
    {edge : Stokes.OrientedEdge vertices.count} (route : MeshPathWalks.EdgeRoute mesh edge) : Gaussian :=
  let values := ((cached.atRoute route).atSheet route.sheet).corners.values
  values route.corners.finish - values route.corners.start

end FacePrimitiveBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
