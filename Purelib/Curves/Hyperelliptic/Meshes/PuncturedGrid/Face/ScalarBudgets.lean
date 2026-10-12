module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.QuotientFreeOmega

/-!
# Face accuracy budgets before original period polynomials

The retained domain sizes bound all analytic splits. A scalar budget pays a
common total-fragment bound on every face and sheet; its finite maximum is a
sufficient floor for both original request polynomials and shared primitives.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets

open Purelib.Data.Nat
open Purelib.Approximation
open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib.RootIsolation

public section

namespace GridPrimitiveAccuracy

open Purelib.Riemann.Normalization.InverseRootPolynomial

/-- Transport the original grid-accuracy certificate along an equality of target tolerances. -/
@[expose] def castTarget {polynomial numerator : Normalization.InverseRootPolynomial.Polynomial} {ambient :
  Normalization.InverseRootPolynomial.Box} {clearance : Comparison.PrimitiveEdgeComparison.RegionClearance polynomial
  ambient}
    {bounds : Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance numerator} {columns : Nat} {first last
      : Normalization.InverseRootPolynomial.Coordinate}
    (equal : first = last) (accuracy : Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns
      first) : Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns last := by
  cases equal
  exact accuracy

/-- Transporting the target preserves the original grid-accuracy stage exactly. -/
theorem castTarget_index {polynomial numerator : Normalization.InverseRootPolynomial.Polynomial} {ambient :
  Normalization.InverseRootPolynomial.Box} {clearance : Comparison.PrimitiveEdgeComparison.RegionClearance polynomial
  ambient}
    {bounds : Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance numerator} {columns : Nat} {first last
      : Normalization.InverseRootPolynomial.Coordinate}
    (equal : first = last) (accuracy : Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns
      first) :
    (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.GridPrimitiveAccuracy.castTarget equal accuracy).index =
      accuracy.index := by
  cases equal
  rfl

end GridPrimitiveAccuracy

namespace BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {source : Hyperelliptic.Differentials.Basic.Differential
    genus} {fragments : Nat} {target : Normalization.InverseRootPolynomial.Coordinate}

namespace FaceDomainBank

/-- Take the maximum original domain step count over every retained face and both sheets.

Each original face contributes both retained domain step counts. The recursive maximum preserves the supplied domain
order and never constructs replacement geometry. -/
@[expose] def stepsBound : {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} →
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces → Nat
  | _, .nil => 0
  | _, .cons first rest => max (max (first.get.domain 0).steps (first.get.domain 1).steps)
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceDomainBank.stepsBound rest)

/-- Every original selected face and sheet step count is below the retained bank maximum.

The retained face position and sheet select one original step count. The nested maxima bound that count in the head face
and then through the unchanged tail bank. -/
theorem get_steps_le {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces)
    (position : Fin faces.length) (sheet : Fin 2) :
    ((domains.get position).domain sheet).steps ≤
      Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceDomainBank.stepsBound domains := by
  induction domains with
  | nil => exact Fin.elim0 position
  | cons first rest ih =>
      rcases position with ⟨position, bound⟩
      cases position with
      | zero =>
          rcases sheet with ⟨sheet, sheetBound⟩
          have cases : sheet = 0 ∨ sheet = 1 := by omega
          rcases cases with rfl | rfl
          · exact Nat.le_trans
              ((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_left _ _))
              ((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_left _ _))
          · exact Nat.le_trans
              ((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_right _ _))
              ((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_left _ _))
      | succ position =>
        exact (ih ⟨position, Nat.lt_of_succ_lt_succ bound⟩).trans (((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr
          (Order.le_max_right _ _)))

end FaceDomainBank

set_option genInjectivity false in
/-- A retained fragment-accuracy budget for one original face domain and differential.

The original overlap bounds and total-fragment payment determine its sufficient grid and primitive stages. -/
structure DomainScalarBudget {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    (domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet) (source :
      Hyperelliptic.Differentials.Basic.Differential genus) (fragments : Nat) (target :
      Normalization.InverseRootPolynomial.Coordinate) where
  /-- The original common primitive-overlap bounds on the retained face clearance. -/ globalBounds :
    Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
    (Readings.PreparedPrimitiveSamples.differentialNumerator source)
  /-- The original fragment-accuracy certificate paid by the retained domain steps, fragment count and target. -/
    certificate : Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy globalBounds domain.steps fragments target

constructive_injectivity DomainScalarBudget

namespace DomainScalarBudget

/-- Prepare the original domain's fragment-accuracy certificate using the supplied global overlap bounds. -/
@[expose] def build {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    (domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet) (globalBounds :
      Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (Readings.PreparedPrimitiveSamples.differentialNumerator source))
    (fragments : Nat) (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) :
      Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget domain source fragments
      target :=
  ⟨globalBounds, Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy.build globalBounds domain.steps fragments
    target positive⟩

/-- Read the original grid certificate at its exact fragment-paid ownership tolerance. -/
@[expose] def grid {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2} {domain :
  Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget domain source
      fragments target) :
    Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy budget.globalBounds domain.steps
      (Rational.Budget.Aggregate.perTerm target fragments / 64) :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.GridPrimitiveAccuracy.castTarget
    (budget.certificate.ownershipTolerance_eq.trans (congrArg (· / 64) budget.certificate.perFragment_eq))
    budget.certificate.grid

/-- Reading the grid certificate preserves the original fragment certificate's grid stage. -/
theorem grid_index {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2} {domain :
  Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget domain source
      fragments target) : budget.grid.index = budget.certificate.grid.index :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.GridPrimitiveAccuracy.castTarget_index ..

/-- Construct the common point mesh using the original retained scalar accuracy and overlap bounds. -/
@[expose] def meshBudget {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2} {domain :
  Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget domain source
      fragments target) (points : List Normalization.InverseRootPolynomial.Gaussian) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.DomainMeshBudget domain source points
      (Rational.Budget.Aggregate.perTerm target fragments / 64) :=
  ⟨FragmentBounds.build domain.patch source, budget.globalBounds, budget.grid,
    Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels.CommonMesh.build domain.geometry
      (Readings.RectangularExteriorBoundary.Geometry.allCells domain.geometry) points⟩

/-- Transport the original scalar budget along an equality of its domain owner. -/
@[expose] def castDomain {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    {first last : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} (equal : first = last)
      (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget first source
      fragments target) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget last source fragments target
      := by
  cases equal
  exact budget

/-- Domain transport commutes exactly with constructing the retained mesh budget. -/
theorem castDomain_meshBudget {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    {first last : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} (equal : first = last)
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget first source
      fragments target) (points : List Normalization.InverseRootPolynomial.Gaussian) :
    (budget.castDomain equal).meshBudget points = (budget.meshBudget points).castDomain equal := by
  cases equal
  rfl

/-- Domain transport preserves the original fragment minimum stage. -/
theorem castDomain_minimumIndex {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    {first last : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} (equal : first = last)
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget first source
      fragments target) :
    (budget.castDomain equal).certificate.minimumIndex = budget.certificate.minimumIndex := by
  cases equal
  rfl

end DomainScalarBudget

set_option genInjectivity false in
/-- The original domain scalar budgets for both sheets of one retained face.

Both original sheet budgets belong to the displayed face-domain owner.
Their common stage retains the maximum of those same sufficient stages. -/
structure FaceScalarBudget {face : Meshes.PuncturedGridFaces.RegularFace bank} (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face)
    (source : Hyperelliptic.Differentials.Basic.Differential genus) (fragments : Nat) (target :
      Normalization.InverseRootPolynomial.Coordinate) where
  /-- The original scalar budget on the retained face's zero sheet. -/ zero :
    Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget (domains.domain 0) source
    fragments target
  /-- The original scalar budget on the retained face's one sheet. -/ one :
    Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget (domains.domain 1) source
    fragments target

constructive_injectivity FaceScalarBudget

namespace FaceScalarBudget

/-- Prepare both original sheet budgets using one retained set of global face bounds. -/
@[expose] def build {face : Meshes.PuncturedGridFaces.RegularFace bank} (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face) (source :
  Hyperelliptic.Differentials.Basic.Differential genus)
    (fragments : Nat) (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) :
      Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget domains source fragments
      target :=
  let globalBounds := Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds.build face.clearance
    (Readings.PreparedPrimitiveSamples.differentialNumerator source)
  ⟨DomainScalarBudget.build (domains.domain 0) globalBounds fragments target positive,
    Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget.build (domains.domain 1)
      globalBounds fragments target positive⟩

/-- Take the maximum original grid stage of both retained sheet budgets. -/
@[expose] def index {face : Meshes.PuncturedGridFaces.RegularFace bank} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face} (budget :
  Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget domains source fragments target)
  : Nat :=
  max budget.zero.certificate.grid.index budget.one.certificate.grid.index

/-- Read the exact original zero- or one-sheet scalar budget. -/
@[expose] def atSheet {face : Meshes.PuncturedGridFaces.RegularFace bank} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face} (budget :
  Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget domains source fragments target)
  :
    (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget
      (domains.domain sheet) source fragments target
  | ⟨0, _⟩ => budget.zero
  | ⟨1, _⟩ => budget.one
  | ⟨_ + 2, impossible⟩ => (by omega : False).elim

/-- The original selected sheet's grid stage is at most the retained face maximum.

The displayed sheet chooses one original scalar request. Its stage is bounded by the retained maximum of both sheet
requests. -/
theorem atSheet_le {face : Meshes.PuncturedGridFaces.RegularFace bank} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget domains source
      fragments target) (sheet : Fin 2) :
    (budget.atSheet sheet).certificate.grid.index ≤ budget.index := by
  rcases sheet with ⟨sheet, bound⟩
  have cases : sheet = 0 ∨ sheet = 1 := by omega
  rcases cases with rfl | rfl
  · exact ((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_left _ _))
  · exact ((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_right _ _))

/-- Construct both retained sheet point meshes from the original scalar budgets. -/
@[expose] def meshes {face : Meshes.PuncturedGridFaces.RegularFace bank} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget domains source
      fragments target) (points : List Normalization.InverseRootPolynomial.Gaussian) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudget domains source points
      (Rational.Budget.Aggregate.perTerm target fragments / 64) :=
  ⟨budget.zero.meshBudget points, budget.one.meshBudget points⟩

/-- The original face mesh construction retains the exact scalar-budget stage. -/
theorem meshes_index {face : Meshes.PuncturedGridFaces.RegularFace bank} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget domains source
      fragments target) (points : List Normalization.InverseRootPolynomial.Gaussian) : (budget.meshes points).index =
      budget.index := by
  change max budget.zero.grid.index budget.one.grid.index = _
  rw [budget.zero.grid_index, budget.one.grid_index]
  rfl

/-- Transport the retained two-sheet scalar budget along the original face equality. -/
@[expose] def castFace {first last : Meshes.PuncturedGridFaces.RegularFace bank} (equal : first = last) {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames first}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget domains source
      fragments target) : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget
      (domains.castFace equal) source fragments target := by
  cases equal
  exact budget

/-- Face transport commutes exactly with constructing both retained sheet meshes. -/
theorem castFace_meshes {first last : Meshes.PuncturedGridFaces.RegularFace bank} (equal : first = last) {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames first}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget domains source
      fragments target) (points : List Normalization.InverseRootPolynomial.Gaussian) :
    (budget.castFace equal).meshes points = (budget.meshes points).castFace equal := by
  cases equal
  rfl

/-- Face transport preserves the retained common scalar stage. -/
theorem castFace_index {first last : Meshes.PuncturedGridFaces.RegularFace bank} (equal : first = last) {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames first}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget domains source
      fragments target) : (budget.castFace equal).index = budget.index := by
  cases equal
  rfl

/-- Selecting a sheet of the retained mesh budget equals constructing the mesh from that original sheet budget. -/
theorem meshes_atSheet {face : Meshes.PuncturedGridFaces.RegularFace bank} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames face}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget domains source
      fragments target) (points : List Normalization.InverseRootPolynomial.Gaussian) (sheet : Fin 2) :
    (budget.meshes points).atSheet sheet = (budget.atSheet sheet).meshBudget points := by
  rcases sheet with ⟨sheet, bound⟩
  have cases : sheet = 0 ∨ sheet = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

end FaceScalarBudget

/-- Dependent scalar budgets aligned with every original face of the retained domain bank.

The dependent bank retains the original face-domain list and both sheet requests at every face. Each budget has the same
fragment count and target. -/
@[expose] def FaceScalarBudgets (source : Hyperelliptic.Differentials.Basic.Differential genus) (fragments : Nat)
  (target : Normalization.InverseRootPolynomial.Coordinate) :
    {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} →
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces → Type
  | _, .nil => PUnit
  | _, .cons first rest => Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget
    first.get source fragments target ×
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source
    fragments target rest

namespace FaceScalarBudgets

/-- Prepare original two-sheet scalar budgets recursively along the retained domain bank. -/
@[expose] def build (source : Hyperelliptic.Differentials.Basic.Differential genus) (fragments : Nat) (target :
  Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} → (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces) →
      Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments target
      domains
  | _, .nil => ⟨⟩
  | _, .cons first rest => ⟨FaceScalarBudget.build first.get source fragments target positive,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.build source
    fragments target positive rest⟩

/-- Take the maximum original scalar-budget stage across all retained faces. -/
@[expose] def index : {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} → {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces} →
    Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments target
      domains → Nat
  | _, .nil, _ => 0
  | _, .cons _ _, budgets => max budgets.1.index
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index
    budgets.2)

/-- Read the scalar budget at an original retained face index. -/
@[expose] def get : {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} → {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces} →
    Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments target
      domains → (position : Fin faces.length) →
      Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget (domains.get position)
      source fragments target
  | _, .nil, _, position => Fin.elim0 position
  | _, .cons _ _, budgets, ⟨0, _⟩ => budgets.1
  | _, .cons _ _, budgets, ⟨position + 1, bound⟩ =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.get budgets.2
    ⟨position, Nat.lt_of_succ_lt_succ bound⟩

/-- Each original indexed face budget is ready by the retained common stage.

Structural recursion follows the same original face index, selecting either the head maximum bound or the retained tail
bound. -/
theorem get_le {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
    (budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments
      target domains) (position : Fin faces.length) :
    (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.get budgets position).index
      ≤ Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index budgets := by
  induction domains with
  | nil => exact Fin.elim0 position
  | cons first rest ih =>
      rcases position with ⟨position, bound⟩
      cases position with
      | zero => exact ((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_left _ _))
      | succ position =>
        exact (ih budgets.2 ⟨position, Nat.lt_of_succ_lt_succ bound⟩).trans (((congrArg (Nat.le _) (Order.max_eq_natMax
          _ _)).mpr (Order.le_max_right _ _)))

/-- Construct the original dependent mesh budgets from the retained scalar-budget bank and point list. -/
@[expose] def meshes (points : List Normalization.InverseRootPolynomial.Gaussian) : {faces : List
  (Meshes.PuncturedGridFaces.RegularFace bank)} → {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces} →
    Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments target
      domains → Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets source points
      (Rational.Budget.Aggregate.perTerm target fragments / 64) domains
  | _, .nil, _ => ⟨⟩
  | _, .cons _ _, budgets => ⟨budgets.1.meshes points,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes points
    budgets.2⟩

/-- Constructing all retained meshes preserves the original bank's maximum scalar stage. -/
theorem meshes_index {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
    (budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments
      target domains) (points : List Normalization.InverseRootPolynomial.Gaussian) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets.index
      (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes points budgets) =
      Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index budgets := by
  induction domains with
  | nil => rfl
  | cons first rest ih =>
      change max (budgets.1.meshes points).index
        (Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets.index
        (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes points
        budgets.2)) = _
      rw [budgets.1.meshes_index, ih]
      rfl

/-- Indexed mesh lookup equals constructing the mesh from the corresponding original scalar budget. -/
theorem meshes_get {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
    (budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments
      target domains) (points : List Normalization.InverseRootPolynomial.Gaussian) (position : Fin faces.length) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets.get
      (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes points budgets)
      position = (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.get budgets
      position).meshes points := by
  induction domains with
  | nil => exact Fin.elim0 position
  | cons first rest ih =>
      rcases position with ⟨position, bound⟩
      cases position with
      | zero => rfl
      | succ position => exact ih budgets.2 ⟨position, Nat.lt_of_succ_lt_succ bound⟩

end FaceScalarBudgets
end BranchCellBank

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
