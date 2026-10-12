module
import Purelib.Data.Nat.Order
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
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains FaceDomainBank)
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

set_option genInjectivity false in
/-- One original face-sheet domain's scalar accuracy budget and shared mesh containing the retained point bank.

All geometric meshes and majorants are fixed before selecting the common numerical primitive stage. -/
structure DomainMeshBudget {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face}
  {sheet : Fin 2}
    (domain : Periods.PeriodDomain models sheet) (source : Differentials.Basic.Differential genus) (points : List
      InverseRootPolynomial.Gaussian) (target : InverseRootPolynomial.Coordinate) where
  /-- The retained local fragment-comparison bounds on the original domain and differential. -/ bounds :
    FragmentReadings.FragmentBounds domain.patch source
  /-- The retained global primitive-overlap bounds on the actual original face clearance. -/ globalBounds :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance (PreparedPrimitiveSamples.differentialNumerator
    source)
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
    (budget : CommonMeshes.DomainMeshBudget first source points target) : CommonMeshes.DomainMeshBudget last source
      points target := by
  cases equal
  exact budget

end DomainMeshBudget

set_option genInjectivity false in
/-- The actual scalar mesh budgets on both original sheets of one retained face.

The two budgets retain their separate domain owners and original sheet indices. -/
structure FaceMeshBudget {face : PuncturedGridFaces.RegularFace bank} (domains : DomainBanks.FaceDomains frames face)
    (source : Differentials.Basic.Differential genus) (points : List InverseRootPolynomial.Gaussian) (target :
      InverseRootPolynomial.Coordinate) where
  /-- The retained budget or shared numerical mesh readings on original sheet zero. -/ zero :
    CommonMeshes.DomainMeshBudget (domains.domain 0) source points target
  /-- The retained budget or shared numerical mesh readings on original sheet one. -/ one :
    CommonMeshes.DomainMeshBudget (domains.domain 1) source points target

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
  : CommonMeshes.FaceMeshBudget domains source points target) : Nat :=
  max budget.zero.accuracy.index budget.one.accuracy.index

/-- Read the retained budget or readings on the supplied actual sheet. -/
@[expose] def atSheet {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
  (budget : CommonMeshes.FaceMeshBudget domains source points target) :
    (sheet : Fin 2) → CommonMeshes.DomainMeshBudget (domains.domain sheet) source points target
  | ⟨0, _⟩ => budget.zero
  | ⟨1, _⟩ => budget.one
  | ⟨_ + 2, impossible⟩ => (by omega : False).elim

/-- Each actual sheet's retained accuracy stage is below the common face stage.

The maximum is computed from the two original accuracy requests. The displayed sheet selects the corresponding retained
lower bound. -/
theorem atSheet_le {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
    (budget : CommonMeshes.FaceMeshBudget domains source points target) (sheet : Fin 2) : (budget.atSheet
      sheet).accuracy.index ≤ budget.index := by
  rcases sheet with ⟨sheet, bound⟩
  have cases : sheet = 0 ∨ sheet = 1 := by omega
  rcases cases with rfl | rfl
  · exact Data.Nat.Order.le_max_left _ _
  · exact Data.Nat.Order.le_max_right _ _

/-- Transport the retained budget or readings along equality of the actual original face owner. -/
@[expose] def castFace {first last : PuncturedGridFaces.RegularFace bank} (equal : first = last) {domains :
  DomainBanks.FaceDomains frames first}
    (budget : CommonMeshes.FaceMeshBudget domains source points target) : CommonMeshes.FaceMeshBudget (domains.castFace
      equal) source points target := by
  cases equal
  exact budget

end FaceMeshBudget

/-- The dependent budget bank on every actual original face-domain owner.

The dependent bank follows the original face-domain list, retaining both sheet budgets for each face and no replacement
domain owners. -/
@[expose] def FaceMeshBudgets (source : Differentials.Basic.Differential genus) (points : List
  InverseRootPolynomial.Gaussian) (target : InverseRootPolynomial.Coordinate) :
    {faces : List (PuncturedGridFaces.RegularFace bank)} → DomainBanks.FaceDomainBank frames faces → Type
  | _, .nil => PUnit
  | _, .cons first rest => CommonMeshes.FaceMeshBudget first.get source points target × CommonMeshes.FaceMeshBudgets
    source points target rest

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
    CommonMeshes.FaceMeshBudgets source points target domains → Nat
  | _, .nil, _ => 0
  | _, .cons _ _, budgets => max budgets.1.index (index budgets.2)

/-- Select the retained budget using its original bounded face position. -/
@[expose] def get : {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains : DomainBanks.FaceDomainBank frames
  faces} →
    CommonMeshes.FaceMeshBudgets source points target domains → (position : Fin faces.length) →
      CommonMeshes.FaceMeshBudget (domains.get position) source points target
  | _, .nil, _, position => Fin.elim0 position
  | _, .cons _ _, budgets, ⟨0, _⟩ => budgets.1
  | _, .cons _ _, budgets, ⟨position + 1, bound⟩ => CommonMeshes.FaceMeshBudgets.get budgets.2 ⟨position,
    Nat.lt_of_succ_lt_succ bound⟩

open CommonMeshes.FaceMeshBudgets in
/-- Each retained face budget's stage is below the complete bank's common stage.

Structural recursion follows the same retained face position. At each cons, the displayed maximum bounds both the head
request and the unchanged tail bank. -/
theorem get_le {faces : List (PuncturedGridFaces.RegularFace bank)} {domains : DomainBanks.FaceDomainBank frames faces}
    (budgets : CommonMeshes.FaceMeshBudgets source points target domains) (position : Fin faces.length) :
    (CommonMeshes.FaceMeshBudgets.get budgets position).index ≤ index budgets := by
  induction domains with
  | nil => exact Fin.elim0 position
  | cons first rest ih =>
      rcases position with ⟨position, bound⟩
      cases position with
      | zero => exact Data.Nat.Order.le_max_left _ _
      | succ position =>
        exact (ih budgets.2 ⟨position, Nat.lt_of_succ_lt_succ bound⟩).trans (Data.Nat.Order.le_max_right _ _)

end FaceMeshBudgets

set_option genInjectivity false in
/-- Shared primitive readings on the retained original domain mesh at a sufficient numerical stage.

The stage certificate and cached vertex readings refer to the same retained budget and primitive data. -/
structure DomainMeshReadings {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames
  face} {sheet : Fin 2}
    {domain : Periods.PeriodDomain models sheet} {index : Nat} (budget : CommonMeshes.DomainMeshBudget domain source
      points target)
    (numerics : PrimitiveData.DomainPrimitives domain source index) where
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
      points target)
    (numerics : PrimitiveData.DomainPrimitives domain source index) (later : budget.accuracy.index ≤ index) :
      CommonMeshes.DomainMeshReadings budget numerics :=
  ⟨later, SharedPrimitiveValues.build numerics.anchors numerics.offsets budget.mesh.surface⟩

/-- Transport the retained budget or readings along equality of their actual original domain owner. -/
@[expose] def castDomain {face : PuncturedGridFaces.RegularFace bank} {models : BranchCellBank.FaceModels frames face}
  {sheet : Fin 2}
    {first last : Periods.PeriodDomain models sheet} (equal : first = last) {index : Nat}
    {budget : CommonMeshes.DomainMeshBudget first source points target} {numerics : PrimitiveData.DomainPrimitives first
      source index}
    (readings : CommonMeshes.DomainMeshReadings budget numerics) : CommonMeshes.DomainMeshReadings (budget.castDomain
      equal) (numerics.castDomain equal) := by
  cases equal
  exact readings

end DomainMeshReadings

set_option genInjectivity false in
/-- The retained shared-mesh readings on both actual sheets of the original face.

Each sheet keeps its original budget and numerical primitive owner. -/
structure FaceMeshReadings {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
  {index : Nat}
    (budget : CommonMeshes.FaceMeshBudget domains source points target) (numerics : PrimitiveData.FacePrimitives domains
      source index) where
  /-- The retained budget or shared numerical mesh readings on original sheet zero. -/ zero :
    CommonMeshes.DomainMeshReadings budget.zero numerics.zero.get
  /-- The retained budget or shared numerical mesh readings on original sheet one. -/ one :
    CommonMeshes.DomainMeshReadings budget.one numerics.one.get

constructive_injectivity FaceMeshReadings

namespace FaceMeshReadings

/-- Cache both actual sheet readings from the supplied original paired primitive data. -/
@[expose] def build {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face} {index
  : Nat}
    (budget : CommonMeshes.FaceMeshBudget domains source points target) (numerics : PrimitiveData.FacePrimitives domains
      source index)
    (later : budget.index ≤ index) : CommonMeshes.FaceMeshReadings budget numerics :=
  ⟨DomainMeshReadings.build budget.zero numerics.zero.get ((Data.Nat.Order.le_max_left _ _).trans later),
    CommonMeshes.DomainMeshReadings.build budget.one numerics.one.get ((Data.Nat.Order.le_max_right _ _).trans later)⟩

/-- Read the retained budget or readings on the supplied actual sheet. -/
@[expose] def atSheet {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
  {index : Nat}
    {budget : CommonMeshes.FaceMeshBudget domains source points target} {numerics : PrimitiveData.FacePrimitives domains
      source index}
    (readings : CommonMeshes.FaceMeshReadings budget numerics) :
    (sheet : Fin 2) → CommonMeshes.DomainMeshReadings (budget.atSheet sheet) (numerics.atSheet sheet)
  | ⟨0, _⟩ => readings.zero
  | ⟨1, _⟩ => readings.one
  | ⟨_ + 2, impossible⟩ => (by omega : False).elim

/-- Transport the retained budget or readings along equality of the actual original face owner. -/
@[expose] def castFace {first last : PuncturedGridFaces.RegularFace bank} (equal : first = last) {domains :
  DomainBanks.FaceDomains frames first} {index : Nat}
    {budget : CommonMeshes.FaceMeshBudget domains source points target} {numerics : PrimitiveData.FacePrimitives domains
      source index}
    (readings : CommonMeshes.FaceMeshReadings budget numerics) : CommonMeshes.FaceMeshReadings (budget.castFace equal)
      (numerics.castFace equal) := by
  cases equal
  exact readings

end FaceMeshReadings

/-- The lazy retained shared-mesh reading bank on the exact original domain, budget and primitive spines.

Each face carries its own lazy paired reading construction on the original domain bank. The common stage bounds every
retained accuracy request. -/
@[expose] def FaceSharedMeshes {index : Nat} : {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains :
  DomainBanks.FaceDomainBank frames faces} →
    CommonMeshes.FaceMeshBudgets source points target domains → PrimitiveData.FacePrimitiveBank source index domains →
      Type
  | _, .nil, _, _ => PUnit
  | _, .cons _ _, budgets, numerics => Thunk (CommonMeshes.FaceMeshReadings budgets.1 numerics.1.get) ×
    CommonMeshes.FaceSharedMeshes budgets.2 numerics.2

namespace FaceSharedMeshes

/-- Retain one lazy paired reading construction per original face using the supplied shared numerical bank. -/
@[expose] def build {index : Nat} : {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains :
  DomainBanks.FaceDomainBank frames faces} →
    (budgets : CommonMeshes.FaceMeshBudgets source points target domains) → (numerics : PrimitiveData.FacePrimitiveBank
      source index domains) →
    CommonMeshes.FaceMeshBudgets.index budgets ≤ index → CommonMeshes.FaceSharedMeshes budgets numerics
  | _, .nil, _, _, _ => ⟨⟩
  | _, .cons _ _, budgets, numerics, later =>
      ⟨⟨fun _ => CommonMeshes.FaceMeshReadings.build budgets.1 numerics.1.get ((Data.Nat.Order.le_max_left _ _).trans
        later)⟩,
        CommonMeshes.FaceSharedMeshes.build budgets.2 numerics.2 ((Data.Nat.Order.le_max_right _ _).trans later)⟩

/-- Read the cached paired mesh readings at the original bounded face position. -/
@[expose] def get {index : Nat} : {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains :
  DomainBanks.FaceDomainBank frames faces} →
    {budgets : CommonMeshes.FaceMeshBudgets source points target domains} → {numerics : PrimitiveData.FacePrimitiveBank
      source index domains} →
    CommonMeshes.FaceSharedMeshes budgets numerics → (position : Fin faces.length) →
      CommonMeshes.FaceMeshReadings (CommonMeshes.FaceMeshBudgets.get budgets position) (FacePrimitiveBank.get numerics
        position)
  | _, .nil, _, _, _, position => Fin.elim0 position
  | _, .cons _ _, _, _, shared, ⟨0, _⟩ => shared.1.get
  | _, .cons _ _, _, _, shared, ⟨position + 1, bound⟩ => CommonMeshes.FaceSharedMeshes.get shared.2 ⟨position,
    Nat.lt_of_succ_lt_succ bound⟩

end FaceSharedMeshes
end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
