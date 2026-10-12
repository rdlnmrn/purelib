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
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index count : Nat}
  {points : Fin count → Purelib.Data.Gaussian.Basic.Canonical}

/-- Transport the original point readings along an equality of period domains, retaining their exact value vector. -/
public def domainReadings {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face}
  {sheet : Fin 2}
    {first last : Periods.PeriodDomain models sheet} (equal : first = last)
    (cached : PrimitiveData.DomainPrimitives first differential index)
    (original : RectangularPointReadings.PointReadings cached.anchors cached.offsets points) :
    {readings : RectangularPointReadings.PointReadings (cached.castDomain equal).anchors (cached.castDomain
      equal).offsets points //
      readings.values = original.values} := by
  cases equal
  exact ⟨original, rfl⟩

/-- Transport the original point readings along an equality of regular faces, retaining their exact value vector. -/
public def faceReadings {first last : PuncturedGridFaces.RegularFace bank} (equal : first = last)
    {domains : DomainBanks.FaceDomains frames first} (cached : PrimitiveData.FacePrimitives domains differential index)
      (sheet : Fin 2)
    (original : RectangularPointReadings.PointReadings (cached.atSheet sheet).anchors (cached.atSheet sheet).offsets
      points) :
    {readings : RectangularPointReadings.PointReadings ((cached.castFace equal).atSheet sheet).anchors
      ((cached.castFace equal).atSheet sheet).offsets points // readings.values = original.values} := by
  cases equal
  exact ⟨original, rfl⟩

/-- Transport the original point readings along an equality of the face-domain families, retaining their exact value
vector. -/
public def domainsReadings {face : PuncturedGridFaces.RegularFace bank} {first last : DomainBanks.FaceDomains frames
  face}
    (equal : first = last) (cached : PrimitiveData.FacePrimitives first differential index) (sheet : Fin 2)
    (original : RectangularPointReadings.PointReadings (cached.atSheet sheet).anchors (cached.atSheet sheet).offsets
      points) :
    {readings : RectangularPointReadings.PointReadings ((cached.castDomains equal).atSheet sheet).anchors
      ((cached.castDomains equal).atSheet sheet).offsets points // readings.values = original.values} := by
  cases equal
  exact ⟨original, rfl⟩

/-- Transport the original point readings along an equality of sheets, retaining their exact value vector. -/
public def sheetReadings {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
    (cached : PrimitiveData.FacePrimitives domains differential index) {first last : Fin 2} (equal : first = last)
    (original : RectangularPointReadings.PointReadings (cached.atSheet first).anchors (cached.atSheet first).offsets
      points) :
    {readings : RectangularPointReadings.PointReadings (cached.atSheet last).anchors (cached.atSheet last).offsets
      points //
      readings.values = original.values} := by
  cases equal
  exact ⟨original, rfl⟩

/-- Transport the original shared-bank readings along equalities of face position and sheet, retaining their exact value
vector. -/
public def indexedReadings {faces : List (PuncturedGridFaces.RegularFace bank)} {domains : DomainBanks.FaceDomainBank
  frames faces}
    (shared : PrimitiveData.FacePrimitiveBank differential index domains) {first last : Fin faces.length}
    {firstSheet lastSheet : Fin 2} (positionEq : first = last) (sheetEq : firstSheet = lastSheet)
    (original : RectangularPointReadings.PointReadings ((shared.get first).atSheet firstSheet).anchors
      ((shared.get first).atSheet firstSheet).offsets points) :
    {readings : RectangularPointReadings.PointReadings ((shared.get last).atSheet lastSheet).anchors
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
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index count : Nat}
  {points : Fin count → Purelib.Data.Gaussian.Basic.Canonical}
variable {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
  Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces} {ambient :
    Purelib.Geometry.Rational.Box}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment
    curve.polynomial ambient start finish}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {placement : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {piece :
    Purelib.Riemann.Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {parentSheet : Fin 2} {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank
    frames faces.regulars}

/-- Reuse the actual position/sheet readings. The certificate is equality of the retained value vectors, not equality of
independently sampled values. -/
def sharedReadings (compared : LiftedMesh.SegmentComparison placement piece differential parentSheet)
    (shared : PrimitiveData.FacePrimitiveBank differential index domains)
    (aligned : compared.domains = domains.atRoute placement.location)
    (original : RectangularPointReadings.PointReadings
      (((shared.get
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace.sideOccurrence
        placement).val.position).atSheet
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace.sideOccurrence
        placement).val.sheet).anchors)
      (((shared.get
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace.sideOccurrence
        placement).val.position).atSheet
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace.sideOccurrence
        placement).val.sheet).offsets) points) :
    {readings : RectangularPointReadings.PointReadings (compared.sharedData shared aligned).anchors
      (compared.sharedData shared aligned).offsets points // readings.values = original.values} := by
  have positionEq :
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace.sideOccurrence
    placement).val.position = placement.location.position := by
    unfold Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace.sideOccurrence
    cases placement.location <;> rfl
  have sheetEq :
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace.sideOccurrence
    placement).val.sheet = placement.location.sheet := by
    unfold Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace.sideOccurrence
    cases placement.location <;> rfl
  let indexed := Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings.indexedReadings shared positionEq
    sheetEq original
  let routed := Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings.faceReadings
    placement.location.face_eq (shared.get placement.location.position)
    placement.location.sheet indexed.val
  let alignedReadings := Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings.domainsReadings
    aligned.symm (shared.atRoute placement.location)
    placement.location.sheet routed.val
  let entered := Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings.sheetReadings ((shared.atRoute
    placement.location).castDomains aligned.symm)
    compared.sheet_eq.symm alignedReadings.val
  let result := Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings.domainReadings
    compared.domain_eq.symm
    (((shared.atRoute placement.location).castDomains aligned.symm).atSheet compared.entered.entry.sheet) entered.val
  exact ⟨result.val, result.property.trans
    (entered.property.trans (alignedReadings.property.trans (routed.property.trans indexed.property)))⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
