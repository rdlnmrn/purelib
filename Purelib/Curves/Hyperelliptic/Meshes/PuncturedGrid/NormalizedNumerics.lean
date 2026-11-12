module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedPrimitives
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
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
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! One shared normalized bank preserves the actual routed period increments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)

open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid}

variable {numerator : Polynomial} {pairs : Nat}

namespace Face.PrimitiveData.FacePrimitives
variable {face : RegularFace bank} {domains : DomainBanks.FaceDomains frames
  face} {differential : Differentials.Basic.Differential genus} {stage : Nat}

/-- Normalize both original sheet primitive caches while retaining their exact domain owners. -/
def normalize
    (cached : FacePrimitives domains differential stage numerator pairs) :
      FacePrimitives domains differential stage numerator pairs :=
  ⟨⟨fun _ => cached.zero.get.normalize⟩, ⟨fun _ => cached.one.get.normalize⟩⟩

/-- Selecting a sheet commutes exactly with normalization of the original face primitive cache. -/
theorem normalize_atSheet
    (cached : FacePrimitives domains differential stage numerator pairs) (sheet :
      Fin 2) :
    cached.normalize.atSheet sheet = (cached.atSheet sheet).normalize := by
  rcases sheet with ⟨sheet, bound⟩
  have cases : sheet = 0 ∨ sheet = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

end Face.PrimitiveData.FacePrimitives

namespace Face.PrimitiveData.FacePrimitiveBank
variable {differential : Differentials.Basic.Differential genus} {stage : Nat}

/-- Normalize the original primitive caches recursively across the retained face-domain bank. -/
def normalize :
    {faces : List (RegularFace bank)} → {domains : DomainBanks.FaceDomainBank
      frames faces} →
    FacePrimitiveBank differential stage domains numerator pairs →
      FacePrimitiveBank differential stage domains numerator pairs
  | _, .nil, _ => ⟨⟩
  | _, .cons _ _, cached => ⟨⟨fun _ => cached.1.get.normalize⟩, normalize cached.2⟩

/-- Indexed lookup commutes exactly with normalization of the retained original primitive bank. -/
theorem normalize_get :
    {faces : List (RegularFace bank)} → {domains : DomainBanks.FaceDomainBank
      frames faces} →
    (cached : FacePrimitiveBank differential stage domains numerator pairs) →
      (position : Fin faces.length) →
    cached.normalize.get position = (cached.get position).normalize
  | _, .nil, _, position => Fin.elim0 position
  | _, .cons _ _, _, ⟨0, _⟩ => rfl
  | _, .cons _ _, cached, ⟨position + 1, bound⟩ =>
      normalize_get cached.2 ⟨position, Nat.lt_of_succ_lt_succ bound⟩

/-- Normalization preserves the exact original routed edge increment. -/
theorem
  normalize_edgeIncrement
    {vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges : SquareRoot.Grid.RootEdgeBank
      frames}
    {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces} {domains :
      DomainBanks.FaceDomainBank frames faces.regulars}
    (cached : FacePrimitiveBank differential stage domains numerator pairs)
    {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count} (route :
      MeshPathWalks.EdgeRoute mesh edge) :
    cached.normalize.edgeIncrement route = cached.edgeIncrement route := by
  rw [cached.normalize.edgeIncrement_eq, cached.edgeIncrement_eq, cached.normalize_get,
    FacePrimitives.normalize_atSheet]
  exact ((cached.get route.position).atSheet route.sheet).normalize_increment _ _

end Face.PrimitiveData.FacePrimitiveBank

variable {faces : List (RegularFace bank)} {domains : Face.DomainBanks.FaceDomainBank
  frames faces} {stage : Nat}

/-- Normalize every original standard-differential primitive bank at the retained shared stage. -/
def RegularDomainMeshes.RegularMeshes.Numerics.normalize
    (cached : RegularDomainMeshes.RegularMeshes.Numerics domains stage) :
      RegularDomainMeshes.RegularMeshes.Numerics domains stage :=
  Vector.DependentVector.ofFn (fun row => (cached.get row).normalize)

/-- Domain lookup commutes exactly with normalization of the original shared numerical bank. -/
theorem
  RegularDomainMeshes.RegularMeshes.Numerics.normalize_atDomain
    (cached : RegularDomainMeshes.RegularMeshes.Numerics domains stage) (position :
      Fin faces.length) (sheet : Fin 2) (row : Fin genus) :
    cached.normalize.atDomain position sheet row = (cached.atDomain position sheet row).normalize := by
  unfold RegularDomainMeshes.RegularMeshes.Numerics.atDomain
    RegularDomainMeshes.RegularMeshes.Numerics.normalize
  rw [Vector.DependentVector.ofFn_get,
    Face.PrimitiveData.FacePrimitiveBank.normalize_get,
    Face.PrimitiveData.FacePrimitives.normalize_atSheet]

/-- Normalization preserves each exact original corner increment on the retained face and sheet. -/
theorem
  RegularDomainMeshes.RegularMeshes.Numerics.normalize_corner_increment
    (cached : RegularDomainMeshes.RegularMeshes.Numerics domains stage)
    (position : Fin faces.length) (sheet : Fin 2) (row : Fin genus) (first last : Fin 4) :
    (cached.normalize.atDomain position sheet row).corners.values last -
      (cached.normalize.atDomain position sheet row).corners.values first =
    (cached.atDomain position sheet row).corners.values last - (cached.atDomain position sheet row).corners.values first
      := by
  rw [cached.normalize_atDomain]
  exact (cached.atDomain position sheet row).normalize_increment first last

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments

open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)

open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid}
  {vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges : SquareRoot.Grid.RootEdgeBank
    frames}
  {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}
    {ambient : Rational.Box}
  {domains : Face.DomainBanks.FaceDomainBank frames faces.regulars} {differential :
    Differentials.Basic.Differential genus} {stage : Nat}

/-- Normalization preserves the complete ordered original corner-increment list along the retained segment assignment.
-/
theorem cornerIncrements_normalize (cached : Face.PrimitiveData.FacePrimitiveBank
  differential stage domains) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces),
      AssignedSegments.cornerIncrements cached.normalize assigned
        = AssignedSegments.cornerIncrements cached assigned
  | _, _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, _, .cons placement remaining => by
      rw [AssignedSegments.cornerIncrements,
        AssignedSegments.cornerIncrements,
        cached.normalize_edgeIncrement,
        AssignedSegments.cornerIncrements_normalize
          cached remaining]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments
