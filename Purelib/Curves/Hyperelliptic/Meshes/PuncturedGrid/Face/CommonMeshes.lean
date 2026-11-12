module
import Purelib.Data.Nat.Order
import Purelib.Polynomial.Dense.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Data.List.Permutation
import Init.Core
import Init.Data.Fin.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary

/-!
# Shared face meshes and scalar budgets for one retained point bank

Every face and sheet retains one mesh and one set of scalar majorants. The
maximum scalar index is computed before the shared numerical primitive bank.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels
open Purelib.Riemann.Comparison
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
open Purelib.Riemann.Integration.RectangularSharedPrimitives
open Purelib.Riemann.Meshes
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.RectangularExteriorBoundary
open Purelib.Riemann.Readings.RectangularPrimitiveBoundary

public section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains FaceDomainBank)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry (Located)
open Purelib.Topology.Mesh.CoordinateTriangulation (VertexLookup)
open Purelib.Riemann.Integration.PreparedParentSplitting.Geometry (allCells_mem)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives FacePrimitives
  FacePrimitiveBank)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {source :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {points : List
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian} {target :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

variable {numerator : CoefficientPolynomial}

set_option genInjectivity false in
/-- One original face-sheet domain's scalar accuracy budget and shared mesh containing the retained point bank.

All geometric meshes and majorants are fixed before selecting the common numerical primitive stage. -/
structure DomainMeshBudget {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face}
  {sheet : Fin 2}
    (domain : Periods.PeriodDomain models sheet) (source : Differentials.Basic.Differential genus) (points : List
      InverseRootPolynomial.Gaussian) (target : InverseRootPolynomial.Coordinate)
    (numerator : CoefficientPolynomial := differentialNumerator source) where
  /-- The retained local fragment-comparison bounds on the original domain and differential. -/ bounds :
    FragmentReadings.FragmentBounds domain.patch source
  /-- The retained global primitive-overlap bounds on the actual original face clearance. -/ globalBounds :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance numerator
  /-- The scalar grid-primitive accuracy request on the original domain steps. -/ accuracy :
    RectangularPrimitiveAccuracy.GridPrimitiveAccuracy globalBounds domain.steps target
  /-- The cached common mesh containing the retained points and all original domain cells. -/ mesh :
    RectangularInverseModels.CommonMesh domain.geometry (Geometry.allCells domain.geometry) points

constructive_injectivity DomainMeshBudget

namespace DomainMeshBudget

/-- Cache the original local and global bounds, paid scalar accuracy request and common geometric mesh before numerical
evaluation. -/
@[expose] def build {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face} {sheet
  : Fin 2}
    (domain : Periods.PeriodDomain models sheet) (source : Differentials.Basic.Differential genus) (points : List
      InverseRootPolynomial.Gaussian)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) : CommonMeshes.DomainMeshBudget domain source
      points target :=
  let globalBounds := PrimitiveOverlapBounds.build face.clearance (PreparedPrimitiveSamples.differentialNumerator
    source)
  ⟨FragmentBounds.build domain.patch source, globalBounds, GridPrimitiveAccuracy.build globalBounds domain.steps target
    positive,
    CommonMesh.build domain.geometry (Geometry.allCells domain.geometry) points⟩

/-- Transport the retained budget or readings along equality of their actual original domain owner. -/
@[expose] def castDomain {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face}
  {sheet : Fin 2}
    {first last : Periods.PeriodDomain models sheet} (equal : first = last)
    (budget : CommonMeshes.DomainMeshBudget first source points target
        (numerator := numerator)) : CommonMeshes.DomainMeshBudget last source
      points target (numerator := numerator) := by
  cases equal
  exact budget

/-- Select new genuine numerator bounds and accuracy on the SAME given geometric mesh.

Only the new scalar bound/request is prepared. The complete supplied mesh
and original local orientation bounds survive unchanged; they are not
relabelled as bounds for the new numerator.
-/
@[expose] def onNumerator {face : PuncturedGridFaces.RegularFace bank}
    {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    {domain : Periods.PeriodDomain models sheet} {oldTarget : InverseRootPolynomial.Coordinate}
    {oldNumerator : CoefficientPolynomial}
    (kept : DomainMeshBudget domain source points oldTarget (numerator := oldNumerator))
    (numerator : CoefficientPolynomial) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    DomainMeshBudget domain source points target (numerator := numerator) :=
  let globalBounds := PrimitiveOverlapBounds.build face.clearance numerator
  let accuracy := GridPrimitiveAccuracy.build globalBounds domain.steps target positive
  ⟨kept.bounds, globalBounds, accuracy, kept.mesh⟩

/-- The whole old mesh is retained; no point location, geometry or surface is reconstructed. -/
theorem onNumerator_mesh {face : PuncturedGridFaces.RegularFace bank}
    {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    {domain : Periods.PeriodDomain models sheet} {oldTarget : InverseRootPolynomial.Coordinate}
    {oldNumerator : CoefficientPolynomial}
    (kept : DomainMeshBudget domain source points oldTarget (numerator := oldNumerator))
    (numerator : CoefficientPolynomial) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    (kept.onNumerator numerator target positive).mesh = kept.mesh := rfl

/-- The new global bound is the actual full-numerator constructor on the unchanged face clearance. -/
theorem onNumerator_globalBounds {face : PuncturedGridFaces.RegularFace bank}
    {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    {domain : Periods.PeriodDomain models sheet} {oldTarget : InverseRootPolynomial.Coordinate}
    {oldNumerator : CoefficientPolynomial}
    (kept : DomainMeshBudget domain source points oldTarget (numerator := oldNumerator))
    (numerator : CoefficientPolynomial) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    (kept.onNumerator numerator target positive).globalBounds =
      PrimitiveOverlapBounds.build face.clearance numerator := rfl

/-- Look up every supplied located point once on the SAME retained common mesh.

Each literal slot retains its actual point-bank membership and containing
cell. The original bounded lookup gives a genuine index and coordinate
readback; repeated or stationary slots remain separate occurrences.
-/
def lookupPoints {face : PuncturedGridFaces.RegularFace bank}
    {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    {domain : Periods.PeriodDomain models sheet} {pointCount : Nat}
    (budget : DomainMeshBudget domain source points target (numerator := numerator))
    (query : Fin pointCount → Gaussian)
    (locations : DependentVector fun slot : Fin pointCount => Located domain.geometry (query slot))
    (included : ∀ slot, query slot ∈ points) :
    DependentVector fun slot : Fin pointCount => VertexLookup budget.mesh.surface.mesh.vertices (query slot) :=
  DependentVector.ofFn fun slot => budget.mesh.lookup (query slot) (included slot)
    (locations.get slot).column (locations.get slot).row
    (allCells_mem domain.geometry (locations.get slot).column (locations.get slot).row)
    (locations.get slot).inside

/-- The complete original lookup vector retains its exact ordered bounded-lookup factory. -/
theorem lookupPoints_factory {face : PuncturedGridFaces.RegularFace bank}
    {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    {domain : Periods.PeriodDomain models sheet} {pointCount : Nat}
    (budget : DomainMeshBudget domain source points target (numerator := numerator))
    (query : Fin pointCount → Gaussian)
    (locations : DependentVector fun slot : Fin pointCount => Located domain.geometry (query slot))
    (included : ∀ slot, query slot ∈ points) :
    budget.lookupPoints query locations included =
      DependentVector.ofFn fun slot => budget.mesh.lookup (query slot) (included slot)
        (locations.get slot).column (locations.get slot).row
        (allCells_mem domain.geometry (locations.get slot).column (locations.get slot).row)
        (locations.get slot).inside := by
  unfold lookupPoints
  rfl

end DomainMeshBudget

set_option genInjectivity false in
/-- The actual scalar mesh budgets on both original sheets of one retained face.

The two budgets retain their separate domain owners and original sheet indices. -/
structure FaceMeshBudget {face : PuncturedGridFaces.RegularFace bank} (domains : DomainBanks.FaceDomains frames face)
    (source : Differentials.Basic.Differential genus) (points : List InverseRootPolynomial.Gaussian) (target :
      InverseRootPolynomial.Coordinate)
    (numerator : CoefficientPolynomial := differentialNumerator source) where
  /-- The retained budget or shared numerical mesh readings on original sheet zero. -/ zero :
    CommonMeshes.DomainMeshBudget (domains.domain 0) source points target (numerator := numerator)
  /-- The retained budget or shared numerical mesh readings on original sheet one. -/ one :
    CommonMeshes.DomainMeshBudget (domains.domain 1) source points target (numerator := numerator)

constructive_injectivity FaceMeshBudget

namespace FaceMeshBudget

/-- Cache the original domain mesh budget independently on each of the two retained face sheets. -/
@[expose] def build {face : PuncturedGridFaces.RegularFace bank} (domains : DomainBanks.FaceDomains frames face) (source
  : Differentials.Basic.Differential genus)
    (points : List InverseRootPolynomial.Gaussian) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
      CommonMeshes.FaceMeshBudget domains source points target :=
  ⟨DomainMeshBudget.build (domains.domain 0) source points target positive,
    CommonMeshes.DomainMeshBudget.build (domains.domain 1) source points target positive⟩

/-- Read the maximum sufficient stage of both original sheet requests. -/
@[expose] def index {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face} (budget
  : CommonMeshes.FaceMeshBudget domains source points target (numerator := numerator)) : Nat :=
  max budget.zero.accuracy.index budget.one.accuracy.index

/-- Read the retained budget or readings on the supplied actual sheet. -/
@[expose] def atSheet {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
  (budget : CommonMeshes.FaceMeshBudget domains source points target (numerator := numerator)) :
    (sheet : Fin 2) → CommonMeshes.DomainMeshBudget (domains.domain sheet) source points target (numerator := numerator)
  | ⟨0, _⟩ => budget.zero
  | ⟨1, _⟩ => budget.one
  | ⟨_ + 2, impossible⟩ => (by omega : False).elim

/-- Each actual sheet's retained accuracy stage is below the common face stage.

The maximum is computed from the two original accuracy requests. The displayed sheet selects the corresponding retained
lower bound. -/
theorem atSheet_le {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
    (budget : CommonMeshes.FaceMeshBudget domains source points target
        (numerator := numerator)) (sheet : Fin 2) : (budget.atSheet
      sheet).accuracy.index ≤ budget.index := by
  rcases sheet with ⟨sheet, bound⟩
  have cases : sheet = 0 ∨ sheet = 1 := by omega
  rcases cases with rfl | rfl
  · exact Data.Nat.Order.le_max_left _ _
  · exact Data.Nat.Order.le_max_right _ _

/-- Transport the retained budget or readings along equality of the actual original face owner. -/
@[expose] def castFace {first last : PuncturedGridFaces.RegularFace bank} (equal : first = last) {domains :
  DomainBanks.FaceDomains frames first}
    (budget : CommonMeshes.FaceMeshBudget domains source points target
        (numerator := numerator)) : CommonMeshes.FaceMeshBudget (domains.castFace
      equal) source points target (numerator := numerator) := by
  cases equal
  exact budget

/-- Transport the complete paired-sheet budget along equality of its actual retained face-domain cache.

Equality elimination preserves both whole original sheet budgets. It does
not build a new domain, accuracy request, bound cache or common mesh.
-/
@[expose] def castDomains {face : PuncturedGridFaces.RegularFace bank}
    {first last : DomainBanks.FaceDomains frames face} (equal : first = last)
    (budget : CommonMeshes.FaceMeshBudget first source points target (numerator := numerator)) :
    CommonMeshes.FaceMeshBudget last source points target (numerator := numerator) := by
  cases equal
  exact budget

/-- Prepare the two genuine numerator requests on the SAME original paired geometric meshes. -/
@[expose] def onNumerator {face : PuncturedGridFaces.RegularFace bank}
    {domains : DomainBanks.FaceDomains frames face} {oldTarget : InverseRootPolynomial.Coordinate}
    {oldNumerator : CoefficientPolynomial}
    (kept : FaceMeshBudget domains source points oldTarget (numerator := oldNumerator))
    (numerator : CoefficientPolynomial) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    FaceMeshBudget domains source points target (numerator := numerator) :=
  ⟨kept.zero.onNumerator numerator target positive, kept.one.onNumerator numerator target positive⟩

end FaceMeshBudget

/-- The dependent budget bank on every actual original face-domain owner.

The dependent bank follows the original face-domain list, retaining both sheet budgets for each face and no replacement
domain owners. -/
@[expose] def FaceMeshBudgets (source : Differentials.Basic.Differential genus) (points : List
  InverseRootPolynomial.Gaussian) (target : InverseRootPolynomial.Coordinate)
    {faces : List (PuncturedGridFaces.RegularFace bank)} (domains : DomainBanks.FaceDomainBank frames faces)
    (numerator : CoefficientPolynomial := differentialNumerator source) : Type :=
  match domains with
  | .nil => PUnit
  | .cons first rest => CommonMeshes.FaceMeshBudget first.get source points target
        (numerator := numerator) × CommonMeshes.FaceMeshBudgets
    source points target (numerator := numerator) rest

namespace FaceMeshBudgets

/-- Cache the paired-sheet budget on every actual original face in retained order. -/
@[expose] def build (source : Differentials.Basic.Differential genus) (points : List InverseRootPolynomial.Gaussian)
  (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    {faces : List (PuncturedGridFaces.RegularFace bank)} → (domains : DomainBanks.FaceDomainBank frames faces) →
      CommonMeshes.FaceMeshBudgets source points target domains
  | _, .nil => ⟨⟩
  | _, .cons first rest => ⟨FaceMeshBudget.build first.get source points target positive,
    CommonMeshes.FaceMeshBudgets.build source points target positive rest⟩

open CommonMeshes.FaceMeshBudgets in
/-- Read the maximum sufficient scalar stage across all actual retained face budgets. -/
@[expose] def index : {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains : DomainBanks.FaceDomainBank
  frames faces} →
    CommonMeshes.FaceMeshBudgets source points target (numerator := numerator) domains → Nat
  | _, .nil, _ => 0
  | _, .cons _ _, budgets => max budgets.1.index (index budgets.2)

/-- Select the retained budget using its original bounded face position. -/
@[expose] def get : {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains : DomainBanks.FaceDomainBank frames
  faces} →
    CommonMeshes.FaceMeshBudgets source points target (numerator := numerator) domains → (position : Fin faces.length) →
      CommonMeshes.FaceMeshBudget (domains.get position) source points target (numerator := numerator)
  | _, .nil, _, position => Fin.elim0 position
  | _, .cons _ _, budgets, ⟨0, _⟩ => budgets.1
  | _, .cons _ _, budgets, ⟨position + 1, bound⟩ => CommonMeshes.FaceMeshBudgets.get budgets.2 ⟨position,
    Nat.lt_of_succ_lt_succ bound⟩

open CommonMeshes.FaceMeshBudgets in
/-- Each retained face budget's stage is below the complete bank's common stage.

Structural recursion follows the same retained face position. At each cons, the displayed maximum bounds both the head
request and the unchanged tail bank. -/
theorem get_le {faces : List (PuncturedGridFaces.RegularFace bank)} {domains : DomainBanks.FaceDomainBank frames faces}
    (budgets : CommonMeshes.FaceMeshBudgets source points target
        (numerator := numerator) domains) (position : Fin faces.length) :
    (CommonMeshes.FaceMeshBudgets.get budgets position).index ≤ index budgets := by
  induction domains with
  | nil => exact Fin.elim0 position
  | cons first rest ih =>
      rcases position with ⟨position, bound⟩
      cases position with
      | zero => exact Data.Nat.Order.le_max_left _ _
      | succ position =>
        exact (ih budgets.2 ⟨position, Nat.lt_of_succ_lt_succ bound⟩).trans (Data.Nat.Order.le_max_right _ _)

/-- Prepare full-numerator requests in original face order while retaining every old geometric mesh. -/
@[expose] def onNumerator {oldTarget : InverseRootPolynomial.Coordinate} {oldNumerator : CoefficientPolynomial}
    (numerator : CoefficientPolynomial) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains : DomainBanks.FaceDomainBank frames faces} →
    FaceMeshBudgets source points oldTarget (numerator := oldNumerator) domains →
      FaceMeshBudgets source points target (numerator := numerator) domains
  | _, .nil, _kept => PUnit.unit
  | _, .cons _first remaining, kept =>
      ⟨kept.1.onNumerator numerator target positive,
        onNumerator numerator target positive (domains := remaining) kept.2⟩

end FaceMeshBudgets

set_option genInjectivity false in
/-- Shared primitive readings on the retained original domain mesh at a sufficient numerical stage.

The stage certificate and cached vertex readings refer to the same retained budget and primitive data. -/
structure DomainMeshReadings {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames
  face} {sheet : Fin 2}
    {domain : Periods.PeriodDomain models sheet} {index : Nat} (budget : CommonMeshes.DomainMeshBudget domain source
      points target (numerator := numerator))
    (numerics : PrimitiveData.DomainPrimitives domain source index (numerator := numerator)) where
  /-- The supplied actual numerical stage meets the original scalar accuracy request. -/ later : budget.accuracy.index ≤
    index
  /-- The cached mesh vertex readings using the exact retained primitive anchors and offsets. -/ readings :
    RectangularSharedPrimitives.SharedPrimitiveValues numerics.anchors numerics.offsets budget.mesh.surface

constructive_injectivity DomainMeshReadings

namespace DomainMeshReadings

/-- Cache the actual shared vertex readings from the supplied original primitive anchors and offsets. -/
@[expose] def build {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face} {sheet
  : Fin 2}
    {domain : Periods.PeriodDomain models sheet} {index : Nat} (budget : CommonMeshes.DomainMeshBudget domain source
      points target (numerator := numerator))
    (numerics : PrimitiveData.DomainPrimitives domain source index
        (numerator := numerator)) (later : budget.accuracy.index ≤ index) :
      CommonMeshes.DomainMeshReadings budget numerics :=
  ⟨later, SharedPrimitiveValues.build numerics.anchors numerics.offsets budget.mesh.surface⟩

/-- Transport the retained budget or readings along equality of their actual original domain owner. -/
@[expose] def castDomain {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face}
  {sheet : Fin 2}
    {first last : Periods.PeriodDomain models sheet} (equal : first = last) {index : Nat}
    {budget : CommonMeshes.DomainMeshBudget first source points target
        (numerator := numerator)} {numerics : PrimitiveData.DomainPrimitives first
      source index (numerator := numerator)}
    (readings : CommonMeshes.DomainMeshReadings budget numerics) : CommonMeshes.DomainMeshReadings (budget.castDomain
      equal) (numerics.castDomain equal) := by
  cases equal
  exact readings

/-- Whole cached-data and budget equality preserves each original scalar point reading. -/
theorem atPoint_congr {face : PuncturedGridFaces.RegularFace bank}
    {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    {domain : Periods.PeriodDomain models sheet} {index : Nat}
    {firstData lastData : DomainPrimitives domain source index (numerator := numerator)}
    {firstBudget lastBudget : DomainMeshBudget domain source points target (numerator := numerator)}
    (dataEq : firstData = lastData) (budgetEq : firstBudget = lastBudget)
    {first : DomainMeshReadings firstBudget firstData} {last : DomainMeshReadings lastBudget lastData}
    (equal : HEq first last) (value : Gaussian) :
    SharedPrimitiveValues.atPoint first.readings value = SharedPrimitiveValues.atPoint last.readings value := by
  cases dataEq
  cases budgetEq
  cases equal
  rfl

end DomainMeshReadings

set_option genInjectivity false in
/-- The retained shared-mesh readings on both actual sheets of the original face.

Each sheet keeps its original budget and numerical primitive owner. -/
structure FaceMeshReadings {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
  {index : Nat}
    (budget : CommonMeshes.FaceMeshBudget domains source points target
        (numerator := numerator)) (numerics : PrimitiveData.FacePrimitives domains
      source index (numerator := numerator)) where
  /-- The retained budget or shared numerical mesh readings on original sheet zero. -/ zero :
    CommonMeshes.DomainMeshReadings budget.zero numerics.zero.get
  /-- The retained budget or shared numerical mesh readings on original sheet one. -/ one :
    CommonMeshes.DomainMeshReadings budget.one numerics.one.get

constructive_injectivity FaceMeshReadings

namespace FaceMeshReadings

/-- Cache both actual sheet readings from the supplied original paired primitive data. -/
@[expose] def build {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face} {index
  : Nat}
    (budget : CommonMeshes.FaceMeshBudget domains source points target
        (numerator := numerator)) (numerics : PrimitiveData.FacePrimitives domains
      source index (numerator := numerator))
    (later : budget.index ≤ index) : CommonMeshes.FaceMeshReadings budget numerics :=
  ⟨DomainMeshReadings.build budget.zero numerics.zero.get ((Data.Nat.Order.le_max_left _ _).trans later),
    CommonMeshes.DomainMeshReadings.build budget.one numerics.one.get ((Data.Nat.Order.le_max_right _ _).trans later)⟩

/-- Read the retained budget or readings on the supplied actual sheet. -/
@[expose] def atSheet {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
  {index : Nat}
    {budget : CommonMeshes.FaceMeshBudget domains source points target
        (numerator := numerator)} {numerics : PrimitiveData.FacePrimitives domains
      source index (numerator := numerator)}
    (readings : CommonMeshes.FaceMeshReadings budget numerics) :
    (sheet : Fin 2) → CommonMeshes.DomainMeshReadings (budget.atSheet sheet) (numerics.atSheet sheet)
  | ⟨0, _⟩ => readings.zero
  | ⟨1, _⟩ => readings.one
  | ⟨_ + 2, impossible⟩ => (by omega : False).elim

/-- Transport the retained budget or readings along equality of the actual original face owner. -/
@[expose] def castFace {first last : PuncturedGridFaces.RegularFace bank} (equal : first = last) {domains :
  DomainBanks.FaceDomains frames first} {index : Nat}
    {budget : CommonMeshes.FaceMeshBudget domains source points target
        (numerator := numerator)} {numerics : PrimitiveData.FacePrimitives domains
      source index (numerator := numerator)}
    (readings : CommonMeshes.FaceMeshReadings budget numerics) : CommonMeshes.FaceMeshReadings (budget.castFace equal)
      (numerics.castFace equal) := by
  cases equal
  exact readings

end FaceMeshReadings

/-- The lazy retained shared-mesh reading bank on the exact original domain, budget and primitive spines.

Each face carries its own lazy paired reading construction on the original domain bank. The common stage bounds every
retained accuracy request. -/
@[expose] def FaceSharedMeshes {index : Nat}
    {numerator : CoefficientPolynomial} :
    {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains :
  DomainBanks.FaceDomainBank frames faces} →
    CommonMeshes.FaceMeshBudgets source points target (numerator := numerator) domains →
    PrimitiveData.FacePrimitiveBank source index
        (numerator := numerator) domains →
      Type
  | _, .nil, _, _ => PUnit
  | _, .cons _ _, budgets, numerics => Thunk (CommonMeshes.FaceMeshReadings budgets.1 numerics.1.get) ×
    CommonMeshes.FaceSharedMeshes (numerator := numerator) budgets.2 numerics.2

namespace FaceSharedMeshes

/-- Retain one lazy paired reading construction per original face using the supplied shared numerical bank. -/
@[expose] def build {index : Nat} : {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains :
  DomainBanks.FaceDomainBank frames faces} →
    (budgets : CommonMeshes.FaceMeshBudgets source points target
        (numerator := numerator) domains) → (numerics : PrimitiveData.FacePrimitiveBank
      source index (numerator := numerator) domains) →
    CommonMeshes.FaceMeshBudgets.index budgets ≤ index →
      CommonMeshes.FaceSharedMeshes (numerator := numerator) budgets numerics
  | _, .nil, _, _, _ => ⟨⟩
  | _, .cons _ _, budgets, numerics, later =>
      ⟨⟨fun _ => CommonMeshes.FaceMeshReadings.build budgets.1 numerics.1.get ((Data.Nat.Order.le_max_left _ _).trans
        later)⟩,
        CommonMeshes.FaceSharedMeshes.build budgets.2 numerics.2 ((Data.Nat.Order.le_max_right _ _).trans later)⟩

/-- Read the cached paired mesh readings at the original bounded face position. -/
@[expose] def get {index : Nat} : {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains :
  DomainBanks.FaceDomainBank frames faces} →
    {budgets : CommonMeshes.FaceMeshBudgets source points target
        (numerator := numerator) domains} → {numerics : PrimitiveData.FacePrimitiveBank
      source index (numerator := numerator) domains} →
    CommonMeshes.FaceSharedMeshes (numerator := numerator) budgets numerics → (position : Fin faces.length) →
      CommonMeshes.FaceMeshReadings (CommonMeshes.FaceMeshBudgets.get budgets position) (FacePrimitiveBank.get numerics
        position)
  | _, .nil, _, _, _, position => Fin.elim0 position
  | _, .cons _ _, _, _, shared, ⟨0, _⟩ => shared.1.get
  | _, .cons _ _, _, _, shared, ⟨position + 1, bound⟩ => CommonMeshes.FaceSharedMeshes.get shared.2 ⟨position,
    Nat.lt_of_succ_lt_succ bound⟩

variable {index : Nat} {faces : List (RegularFace bank)} {domains : FaceDomainBank frames faces}
    (budgets : FaceMeshBudgets source points target (numerator := numerator) domains)
    (numerics : FacePrimitiveBank source index (numerator := numerator) domains)
    (later : budgets.index ≤ index)

/-- The complete given numerical inputs and their actual shared-mesh execution.

The original bank, whole root frames, domains, point list, numerator,
stage, budgets and primitive cache remain DATA. The output retains its
one original build factory; no input is recovered by rerunning a producer.
-/
@[expose] def Acquisition : Type _ :=
  {value : BranchCellBank curve branches higher × RootIsolation.SquareRoot.Grid.RootFrames bank.grid ×
      List (RegularFace bank) × FaceDomainBank frames faces × Differential genus × List Gaussian × Coordinate ×
      CoefficientPolynomial × Nat //
    value = (bank, frames, faces, domains, source, points, target, numerator, index)} ×
  {value : FaceMeshBudgets source points target (numerator := numerator) domains // value = budgets} ×
  {value : FacePrimitiveBank source index (numerator := numerator) domains // value = numerics} ×
  {value : FaceSharedMeshes budgets numerics // value = FaceSharedMeshes.build budgets numerics later}

/-- Execute the original shared-mesh worker once and retain all original inputs with its whole output factory. -/
def acquire : Acquisition budgets numerics later :=
  let shared : {value : FaceSharedMeshes budgets numerics //
      value = FaceSharedMeshes.build budgets numerics later} :=
    ⟨FaceSharedMeshes.build budgets numerics later, rfl⟩
  ⟨⟨(bank, frames, faces, domains, source, points, target, numerator, index), rfl⟩,
    ⟨budgets, rfl⟩, ⟨numerics, rfl⟩, shared⟩

namespace Acquisition

variable {budgets numerics later}
variable (kept : Acquisition budgets numerics later)

/-- Read the actual geometric/numerical inputs without recovering them from type indices. -/
@[expose] def inputs := kept.1.val

/-- The entire retained input product is the literal supplied bank, frames, domains and numerical parameters. -/
theorem inputs_eq : kept.inputs = (bank, frames, faces, domains, source, points, target, numerator, index) :=
  kept.1.property

/-- Read the SAME actual input budget product. -/
@[expose] def meshBudgets : FaceMeshBudgets source points target (numerator := numerator) domains := kept.2.1.val

/-- The whole retained budget product is the original supplied cache. -/
theorem meshBudgets_eq : kept.meshBudgets = budgets := kept.2.1.property

/-- Read the SAME actual input primitive bank, including its independent anchors and offsets. -/
@[expose] def primitiveBank : FacePrimitiveBank source index (numerator := numerator) domains := kept.2.2.1.val

/-- The retained whole primitive cache is the original supplied bank. -/
theorem primitiveBank_eq : kept.primitiveBank = numerics := kept.2.2.1.property

/-- Read the actual once-built shared observations on those original input caches. -/
@[expose] def shared : FaceSharedMeshes budgets numerics := kept.2.2.2.val

/-- The complete observation cache retains its single original numerical factory. -/
theorem shared_eq : kept.shared = FaceSharedMeshes.build budgets numerics later := kept.2.2.2.property

/-- A literal whole point-list factory includes every vertex of its actual supplied grid bank.

The finite list equality is coupled to the original numerical inputs.
It gives membership only; no vertex or root Owner identity is inferred
from equal coordinates or numerical readings.
-/
theorem vertices_mem (vertices : RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid)
    (pointPrefix rest : List Gaussian)
    (factory : points = pointPrefix ++ (List.ofFn vertices.coordinate ++ rest)) (vertex : Fin vertices.count) :
    vertices.coordinate vertex ∈ points := by
  rewrite [factory]
  exact List.mem_append_right _ (List.mem_append_left _ (Data.List.Permutation.ofFn_mem _ vertex))

end Acquisition

end FaceSharedMeshes
end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
