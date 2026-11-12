module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh

open Purelib.Riemann.Meshes

open Purelib.Riemann.Readings

@[expose] public section

/-! Transport retained point readings through the same face, domain and
sheet equalities as the shared primitive bank. Values are never evaluated. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives FacePrimitives
  FacePrimitiveBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {differential :
    Differential genus} {index count : Nat}
  {points : Fin count → Gaussian}

/-- Transport the original point readings along an equality of period domains, retaining their exact value vector. -/
public def domainReadings {face : RegularFace bank} {models : FaceModels frames face}
  {sheet : Fin 2}
    {first last : PeriodDomain models sheet} (equal : first = last)
    (cached : DomainPrimitives first differential index)
    (original : PointReadings cached.anchors cached.offsets points) :
    {readings : PointReadings (cached.castDomain equal).anchors (cached.castDomain
      equal).offsets points //
      readings.values = original.values} := by
  cases equal
  exact ⟨original, rfl⟩

/-- Transport the original point readings along an equality of regular faces, retaining their exact value vector. -/
public def faceReadings {first last : RegularFace bank} (equal : first = last)
    {domains : FaceDomains frames first} (cached : FacePrimitives domains differential index)
      (sheet : Fin 2)
    (original : PointReadings (cached.atSheet sheet).anchors (cached.atSheet sheet).offsets
      points) :
    {readings : PointReadings ((cached.castFace equal).atSheet sheet).anchors
      ((cached.castFace equal).atSheet sheet).offsets points // readings.values = original.values} := by
  cases equal
  exact ⟨original, rfl⟩

/-- Transport the original point readings along an equality of the face-domain families, retaining their exact value
vector. -/
public def domainsReadings {face : RegularFace bank} {first last : FaceDomains frames
  face}
    (equal : first = last) (cached : FacePrimitives first differential index) (sheet : Fin 2)
    (original : PointReadings (cached.atSheet sheet).anchors (cached.atSheet sheet).offsets
      points) :
    {readings : PointReadings ((cached.castDomains equal).atSheet sheet).anchors
      ((cached.castDomains equal).atSheet sheet).offsets points // readings.values = original.values} := by
  cases equal
  exact ⟨original, rfl⟩

/-- Transport the original point readings along an equality of sheets, retaining their exact value vector. -/
public def sheetReadings {face : RegularFace bank} {domains : FaceDomains frames face}
    (cached : FacePrimitives domains differential index) {first last : Fin 2} (equal : first = last)
    (original : PointReadings (cached.atSheet first).anchors (cached.atSheet first).offsets
      points) :
    {readings : PointReadings (cached.atSheet last).anchors (cached.atSheet last).offsets
      points //
      readings.values = original.values} := by
  cases equal
  exact ⟨original, rfl⟩

/-- Transport the original shared-bank readings along equalities of face position and sheet, retaining their exact value
vector. -/
public def indexedReadings {faces : List (RegularFace bank)} {domains : FaceDomainBank
  frames faces}
    (shared : FacePrimitiveBank differential index domains) {first last : Fin faces.length}
    {firstSheet lastSheet : Fin 2} (positionEq : first = last) (sheetEq : firstSheet = lastSheet)
    (original : PointReadings ((shared.get first).atSheet firstSheet).anchors
      ((shared.get first).atSheet firstSheet).offsets points) :
    {readings : PointReadings ((shared.get last).atSheet lastSheet).anchors
      ((shared.get last).atSheet lastSheet).offsets points // readings.values = original.values} := by
  cases positionEq
  cases sheetEq
  exact ⟨original, rfl⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace (sideOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {differential :
    Differential genus} {index count : Nat}
  {points : Fin count → Gaussian}
variable {vertices : RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    GridLiftedMesh.LiftedMesh vertices edges faces} {ambient :
    Geometry.Rational.Box}
  {start finish : Gaussian} {segment : ClearSegment
    curve.polynomial ambient start finish}
  {owner : Owner (curve.polynomial.eval start)}
  {placement : LiftedMesh.SegmentFace mesh segment} {piece :
    CoveredSegment segment owner}
  {parentSheet : Fin 2} {domains : FaceDomainBank
    frames faces.regulars}

/-- Reuse the actual position/sheet readings. The certificate is equality of the retained value vectors, not equality of
independently sampled values. -/
def sharedReadings (compared : SegmentComparison placement piece differential parentSheet)
    (shared : FacePrimitiveBank differential index domains)
    (aligned : compared.domains = domains.atRoute placement.location)
    (original : PointReadings
      (((shared.get
        (SegmentFace.sideOccurrence
        placement).val.position).atSheet
        (SegmentFace.sideOccurrence
        placement).val.sheet).anchors)
      (((shared.get
        (SegmentFace.sideOccurrence
        placement).val.position).atSheet
        (SegmentFace.sideOccurrence
        placement).val.sheet).offsets) points) :
    {readings : PointReadings (compared.sharedData shared aligned).anchors
      (compared.sharedData shared aligned).offsets points // readings.values = original.values} := by
  have positionEq :
    (SegmentFace.sideOccurrence
    placement).val.position = placement.location.position := by
    unfold SegmentFace.sideOccurrence
    cases placement.location <;> rfl
  have sheetEq :
    (SegmentFace.sideOccurrence
    placement).val.sheet = placement.location.sheet := by
    unfold SegmentFace.sideOccurrence
    cases placement.location <;> rfl
  let indexed := SharedPointReadings.indexedReadings shared positionEq
    sheetEq original
  let routed := SharedPointReadings.faceReadings
    placement.location.face_eq (shared.get placement.location.position)
    placement.location.sheet indexed.val
  let alignedReadings := SharedPointReadings.domainsReadings
    aligned.symm (shared.atRoute placement.location)
    placement.location.sheet routed.val
  let entered := SharedPointReadings.sheetReadings ((shared.atRoute
    placement.location).castDomains aligned.symm)
    compared.sheet_eq.symm alignedReadings.val
  let result := SharedPointReadings.domainReadings
    compared.domain_eq.symm
    (((shared.atRoute placement.location).castDomains aligned.symm).atSheet compared.entered.entry.sheet) entered.val
  exact ⟨result.val, result.property.trans
    (entered.property.trans (alignedReadings.property.trans (routed.property.trans indexed.property)))⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
