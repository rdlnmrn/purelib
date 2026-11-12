module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial.Accuracy
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Nat.Order
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
/-! # Paid ordinary numerator models on the same given physical closed word

The literal retained fragment count selects local requests before all new
observations. Their actual stored floors select one source work/model bank
and one genuine P primitive/shared bank. Original numerical revaluation
keeps the given physical leaves, queries, Finish and every signed join.

Named dependent tails preserve the original product and `Sigma` representation
while keeping projection types compact. Their exposed bodies retain the original
constructor and reduction behavior.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.Closed

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank frames base.faces.regulars} {target tolerance : Rational}
variable {points : List Canonical} {index : Nat} {oldNumerator : CoefficientPolynomial}
variable {budgets : FaceMeshBudgets source points tolerance (numerator := oldNumerator) domains}
variable {numerics : FacePrimitiveBank source index (numerator := oldNumerator) domains}
variable {shared : FaceSharedMeshes (numerator := oldNumerator) budgets numerics}
variable {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
variable {fragments : RegularPrimitiveSplits (base := base) axes splits}
variable {requests : RequestedParents count target parents} {entries : SplitSheets domains fragments requests}
variable {point : LiftedPoint 2} {root : Named}
variable {geometry : CenteredPathChain parents (start := point) (finish := point)}
variable {roots : RootChain parents root root}
variable {included : ∀ value ∈ PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
variable (kept : Closed shared entries geometry roots included)

namespace PolynomialPreparation

variable (differential : OddPowerDifferential curve.polynomial) (ordinary : differential.denominatorPairs = 0)
variable (requested : Rational) (positive : 0 < requested) (minimumFloor modelStage : Nat)

/-- Select the numerical stage from the genuine mesh and leaf floors and an optional independent floor.

The absent-floor branch keeps the original literal maximum. A supplied
floor extends that same maximum before either numerical bank is prepared.
-/
@[expose] def selectFaceStage (meshStage leafStage : Nat) (minimumFaceStage : Option Nat) : Nat :=
  match minimumFaceStage with
  | none => max meshStage leafStage
  | some minimum => max (max meshStage leafStage) minimum

/-- The selected numerical stage meets the actual mesh-budget floor. -/
theorem meshStage_le (meshStage leafStage : Nat) (minimumFaceStage : Option Nat) :
    meshStage ≤ selectFaceStage meshStage leafStage minimumFaceStage := by
  cases minimumFaceStage with
  | none => exact Data.Nat.Order.le_max_left _ _
  | some minimum =>
      exact (Data.Nat.Order.le_max_left meshStage leafStage).trans
        (Data.Nat.Order.le_max_left (max meshStage leafStage) minimum)

/-- The selected numerical stage meets every actual leaf request. -/
theorem leafStage_le (meshStage leafStage : Nat) (minimumFaceStage : Option Nat) :
    leafStage ≤ selectFaceStage meshStage leafStage minimumFaceStage := by
  cases minimumFaceStage with
  | none => exact Data.Nat.Order.le_max_right _ _
  | some minimum =>
      exact (Data.Nat.Order.le_max_right meshStage leafStage).trans
        (Data.Nat.Order.le_max_left (max meshStage leafStage) minimum)

/-- A supplied independent floor is met by the same selected numerical stage. -/
theorem minimumStage_le (meshStage leafStage minimumFaceStage : Nat) :
    minimumFaceStage ≤ selectFaceStage meshStage leafStage (some minimumFaceStage) :=
  Data.Nat.Order.le_max_right _ _

/-- An absent independent floor preserves the original exact stage expression. -/
theorem selectFaceStage_none (meshStage leafStage : Nat) :
    selectFaceStage meshStage leafStage none = max meshStage leafStage := rfl

section

variable (minimumFaceStage : Option Nat)

namespace Preparation

/-- The revalued word and its certified comparison with the retained source model.

This named dependent tail keeps deep projections from duplicating the
remaining preparation type in their `Sigma` arguments.
-/
@[expose] def WordTail
    (nextBudgets : {value : FaceMeshBudgets source points
      (Aggregate.perTerm requested (fragmentCount entries))
      (numerator := differential.numerator.scale differential.scale) domains //
    value = FaceMeshBudgets.onNumerator (differential.numerator.scale differential.scale)
      (Aggregate.perTerm requested (fragmentCount entries)) (Aggregate.perTerm_positive positive _)
      (Closed.originals shared entries geometry roots kept).val.2.1})
    (allocated : {value : PolynomialComparison.Requests nextBudgets.val entries
      (Aggregate.perTerm requested (fragmentCount entries)) //
    value = PolynomialComparison.prepareRequests nextBudgets.val
      (Aggregate.perTerm requested (fragmentCount entries)) (Aggregate.perTerm_positive positive _) entries})
    (sourceFloor : {value : Nat // value = max minimumFloor
    (PolynomialComparison.sourceFloor nextBudgets.val entries allocated.val)})
    (faceStage : {value : Nat // value = selectFaceStage nextBudgets.val.index
    (PolynomialComparison.faceFloor nextBudgets.val entries allocated.val) minimumFaceStage})
    (work : {value : PolynomialWork requests.covered sourceFloor.val differential //
    value = PolynomialWork.build requests.covered sourceFloor.val differential})
    (models : {value : work.val.Models modelStage // value = work.val.models modelStage})
    (primitives : {value : FacePrimitiveBank source faceStage.val
      (numerator := differential.numerator.scale differential.scale) domains //
    value = FacePrimitiveBank.build source faceStage.val domains
      (differential.numerator.scale differential.scale)})
    (nextShared : {value : FaceSharedMeshes (numerator := differential.numerator.scale differential.scale)
      nextBudgets.val primitives.val //
    value = FaceSharedMeshes.build (numerator := differential.numerator.scale differential.scale)
      nextBudgets.val primitives.val ((meshStage_le _ _ minimumFaceStage).trans_eq faceStage.property.symm)}) :
        Type _ :=
  Σ word : {value : Closed.NumeratorWord nextShared.val kept //
    value = Closed.withNumerics kept nextShared.val},
  Σ compared : {value : PolynomialComparison.Cache nextShared.val requests entries geometry roots word.val.val.2
      work.val models.val ordinary //
    value = PolynomialComparison.build nextShared.val requests entries geometry roots word.val.val.2
      work.val models.val ordinary},
  {_value : Unit // compared.val.bound < requested ∧ normSq (compared.val.value -
    (PathModel.mk (PolynomialWork.Models.cells requests.covered work.val models.val)).integralSample) < requested}

/-- The source models, primitive and shared banks, and certified revalued word. -/
@[expose] def ModelTail
    (nextBudgets : {value : FaceMeshBudgets source points
      (Aggregate.perTerm requested (fragmentCount entries))
      (numerator := differential.numerator.scale differential.scale) domains //
    value = FaceMeshBudgets.onNumerator (differential.numerator.scale differential.scale)
      (Aggregate.perTerm requested (fragmentCount entries)) (Aggregate.perTerm_positive positive _)
      (Closed.originals shared entries geometry roots kept).val.2.1})
    (allocated : {value : PolynomialComparison.Requests nextBudgets.val entries
      (Aggregate.perTerm requested (fragmentCount entries)) //
    value = PolynomialComparison.prepareRequests nextBudgets.val
      (Aggregate.perTerm requested (fragmentCount entries)) (Aggregate.perTerm_positive positive _) entries})
    (sourceFloor : {value : Nat // value = max minimumFloor
    (PolynomialComparison.sourceFloor nextBudgets.val entries allocated.val)})
    (faceStage : {value : Nat // value = selectFaceStage nextBudgets.val.index
    (PolynomialComparison.faceFloor nextBudgets.val entries allocated.val) minimumFaceStage})
    (work : {value : PolynomialWork requests.covered sourceFloor.val differential //
    value = PolynomialWork.build requests.covered sourceFloor.val differential}) : Type _ :=
  Σ models : {value : work.val.Models modelStage // value = work.val.models modelStage},
  Σ primitives : {value : FacePrimitiveBank source faceStage.val
      (numerator := differential.numerator.scale differential.scale) domains //
    value = FacePrimitiveBank.build source faceStage.val domains
      (differential.numerator.scale differential.scale)},
  Σ nextShared : {value : FaceSharedMeshes (numerator := differential.numerator.scale differential.scale)
      nextBudgets.val primitives.val //
    value = FaceSharedMeshes.build (numerator := differential.numerator.scale differential.scale)
      nextBudgets.val primitives.val ((meshStage_le _ _ minimumFaceStage).trans_eq faceStage.property.symm)},
  WordTail (kept := kept) (differential := differential) (ordinary := ordinary) (requested := requested) (positive
    := positive) (minimumFloor := minimumFloor) (modelStage := modelStage) (minimumFaceStage := minimumFaceStage)
    nextBudgets allocated sourceFloor faceStage work models primitives nextShared

/-- The source and face stages followed by the retained model and numerical observations. -/
@[expose] def SourceStageTail
    (nextBudgets : {value : FaceMeshBudgets source points
      (Aggregate.perTerm requested (fragmentCount entries))
      (numerator := differential.numerator.scale differential.scale) domains //
    value = FaceMeshBudgets.onNumerator (differential.numerator.scale differential.scale)
      (Aggregate.perTerm requested (fragmentCount entries)) (Aggregate.perTerm_positive positive _)
      (Closed.originals shared entries geometry roots kept).val.2.1})
    (allocated : {value : PolynomialComparison.Requests nextBudgets.val entries
      (Aggregate.perTerm requested (fragmentCount entries)) //
    value = PolynomialComparison.prepareRequests nextBudgets.val
      (Aggregate.perTerm requested (fragmentCount entries)) (Aggregate.perTerm_positive positive _) entries}) :
        Type _ :=
  Σ sourceFloor : {value : Nat // value = max minimumFloor
    (PolynomialComparison.sourceFloor nextBudgets.val entries allocated.val)},
  Σ faceStage : {value : Nat // value = selectFaceStage nextBudgets.val.index
    (PolynomialComparison.faceFloor nextBudgets.val entries allocated.val) minimumFaceStage},
  Σ work : {value : PolynomialWork requests.covered sourceFloor.val differential //
    value = PolynomialWork.build requests.covered sourceFloor.val differential},
  ModelTail (kept := kept) (differential := differential) (ordinary := ordinary) (requested := requested) (positive
    := positive) (minimumFloor := minimumFloor) (modelStage := modelStage) (minimumFaceStage := minimumFaceStage)
    nextBudgets allocated sourceFloor faceStage work

end Preparation

end

/-- Complete actual input/count/allocation data, true P requests and both floors before the observations.

The final payload retains the one original work/model bank, one original P
primitive/shared bank, same physical old/new Closed pair, one whole actual
comparison cache and its internally derived requested bound.
-/
@[expose] def Preparation (minimumFaceStage : Option Nat := none) : Type _ :=
  {value : (OddPowerDifferential curve.polynomial × Nat × Nat × Rational × Nat × Rational) //
    value = (differential, minimumFloor, modelStage, requested, fragmentCount entries,
      Aggregate.perTerm requested (fragmentCount entries))} ×
  (Σ nextBudgets : {value : FaceMeshBudgets source points
      (Aggregate.perTerm requested (fragmentCount entries))
      (numerator := differential.numerator.scale differential.scale) domains //
    value = FaceMeshBudgets.onNumerator (differential.numerator.scale differential.scale)
      (Aggregate.perTerm requested (fragmentCount entries)) (Aggregate.perTerm_positive positive _)
      (Closed.originals shared entries geometry roots kept).val.2.1},
  Σ allocated : {value : PolynomialComparison.Requests nextBudgets.val entries
      (Aggregate.perTerm requested (fragmentCount entries)) //
    value = PolynomialComparison.prepareRequests nextBudgets.val
      (Aggregate.perTerm requested (fragmentCount entries)) (Aggregate.perTerm_positive positive _) entries},
  Preparation.SourceStageTail (kept := kept) (differential := differential) (ordinary := ordinary) (requested :=
    requested) (positive := positive) (minimumFloor := minimumFloor) (modelStage := modelStage) (minimumFaceStage
    := minimumFaceStage) nextBudgets allocated)

/-- The complete genuine-P next-budget field, certified by the original given-word factory.

This exact field type is shared by the original preparation and a caller
that must allocate additional fresh-source requests on that same cache
before any polynomial or primitive bank is observed.
-/
@[expose] def Budgets : Type _ :=
  {value : FaceMeshBudgets source points (Aggregate.perTerm requested (fragmentCount entries))
      (numerator := differential.numerator.scale differential.scale) domains //
    value = FaceMeshBudgets.onNumerator (differential.numerator.scale differential.scale)
      (Aggregate.perTerm requested (fragmentCount entries)) (Aggregate.perTerm_positive positive _)
      (Closed.originals shared entries geometry roots kept).val.2.1}

/-- Execute the original observation pipeline on the SAME supplied certified next-budget cache. -/
private def buildGivenBudgets (minimumFaceStage : Option Nat)
    (nextBudgets : Budgets kept differential requested positive) :
    Preparation kept differential ordinary requested positive minimumFloor modelStage minimumFaceStage :=
  let occurrenceCount := fragmentCount entries
  let localTarget := Aggregate.perTerm requested occurrenceCount
  have localPositive : 0 < localTarget := Aggregate.perTerm_positive positive occurrenceCount
  let inputs : {value : (OddPowerDifferential curve.polynomial × Nat × Nat × Rational × Nat × Rational) //
      value = (differential, minimumFloor, modelStage, requested, occurrenceCount, localTarget)} :=
    ⟨(differential, minimumFloor, modelStage, requested, occurrenceCount, localTarget), rfl⟩
  let allocated : {value : PolynomialComparison.Requests nextBudgets.val entries localTarget //
      value = PolynomialComparison.prepareRequests nextBudgets.val localTarget localPositive entries} :=
    ⟨PolynomialComparison.prepareRequests nextBudgets.val localTarget localPositive entries, rfl⟩
  let sourceFloor : {value : Nat // value = max minimumFloor
      (PolynomialComparison.sourceFloor nextBudgets.val entries allocated.val)} :=
    ⟨max minimumFloor (PolynomialComparison.sourceFloor nextBudgets.val entries allocated.val), rfl⟩
  let faceStage : {value : Nat // value = selectFaceStage nextBudgets.val.index
      (PolynomialComparison.faceFloor nextBudgets.val entries allocated.val) minimumFaceStage} :=
    ⟨selectFaceStage nextBudgets.val.index
      (PolynomialComparison.faceFloor nextBudgets.val entries allocated.val) minimumFaceStage, rfl⟩
  let work : {value : PolynomialWork requests.covered sourceFloor.val differential //
      value = PolynomialWork.build requests.covered sourceFloor.val differential} :=
    ⟨PolynomialWork.build requests.covered sourceFloor.val differential, rfl⟩
  let models : {value : work.val.Models modelStage // value = work.val.models modelStage} :=
    ⟨work.val.models modelStage, rfl⟩
  let primitives : {value : FacePrimitiveBank source faceStage.val
      (numerator := differential.numerator.scale differential.scale) domains //
      value = FacePrimitiveBank.build source faceStage.val domains
      (differential.numerator.scale differential.scale)} :=
    ⟨FacePrimitiveBank.build source faceStage.val domains
      (differential.numerator.scale differential.scale), rfl⟩
  have meshLater : nextBudgets.val.index ≤ faceStage.val :=
    (meshStage_le _ _ minimumFaceStage).trans_eq faceStage.property.symm
  let nextShared : {value : FaceSharedMeshes (numerator := differential.numerator.scale differential.scale)
      nextBudgets.val primitives.val //
      value = FaceSharedMeshes.build (numerator := differential.numerator.scale differential.scale)
        nextBudgets.val primitives.val meshLater} :=
    ⟨FaceSharedMeshes.build (numerator := differential.numerator.scale differential.scale)
      nextBudgets.val primitives.val meshLater, rfl⟩
  let word : {value : Closed.NumeratorWord nextShared.val kept //
      value = Closed.withNumerics kept nextShared.val} :=
    ⟨Closed.withNumerics kept nextShared.val, rfl⟩
  let compared : {value : PolynomialComparison.Cache nextShared.val requests entries geometry roots word.val.val.2
      work.val models.val ordinary //
      value = PolynomialComparison.build nextShared.val requests entries geometry roots word.val.val.2
        work.val models.val ordinary} :=
    ⟨PolynomialComparison.build nextShared.val requests entries geometry roots word.val.val.2
      work.val models.val ordinary, rfl⟩
  have sourcePaid : PolynomialComparison.sourceFloor nextBudgets.val entries allocated.val ≤ sourceFloor.val :=
    (Data.Nat.Order.le_max_right _ _).trans_eq sourceFloor.property.symm
  have facePaid : PolynomialComparison.faceFloor nextBudgets.val entries allocated.val ≤ faceStage.val :=
    (leafStage_le _ _ minimumFaceStage).trans_eq faceStage.property.symm
  have paid := PolynomialComparison.Cache.bound_lt nextBudgets.val nextShared.val requests entries geometry roots
    word.val.val.2 work.val models.val compared.val positive allocated.val sourcePaid facePaid
  ⟨inputs, nextBudgets, allocated, sourceFloor, faceStage, work, models, primitives, nextShared, word, compared,
    (), paid, compared.val.accurate.trans_lt paid⟩

/-- Allocate the original next budget once before the shared model and primitive observation pipeline. -/
private def buildWithFaceStage (minimumFaceStage : Option Nat) :
    Preparation kept differential ordinary requested positive minimumFloor modelStage minimumFaceStage :=
  let occurrenceCount := fragmentCount entries
  let localTarget := Aggregate.perTerm requested occurrenceCount
  have localPositive : 0 < localTarget := Aggregate.perTerm_positive positive occurrenceCount
  let nextBudgets : {value : FaceMeshBudgets source points localTarget
      (numerator := differential.numerator.scale differential.scale) domains //
      value = FaceMeshBudgets.onNumerator (differential.numerator.scale differential.scale)
        localTarget localPositive (Closed.originals shared entries geometry roots kept).val.2.1} :=
    ⟨FaceMeshBudgets.onNumerator (differential.numerator.scale differential.scale)
      localTarget localPositive (Closed.originals shared entries geometry roots kept).val.2.1, rfl⟩
  buildGivenBudgets kept differential ordinary requested positive minimumFloor modelStage
    minimumFaceStage nextBudgets

/-- Prepare the original model and numerical banks with precisely the original two-floor stage selection. -/
def build : Preparation kept differential ordinary requested positive minimumFloor modelStage :=
  buildWithFaceStage kept differential ordinary requested positive minimumFloor modelStage none

/-- Prepare the same single bank pipeline after meeting an independent numerical request floor.

The additional floor is selected before the source work, model and
primitive/shared banks. All physical input caches remain those of the
given closed word.
-/
def buildAtFaceStage (minimumFaceStage : Nat) :
    Preparation kept differential ordinary requested positive minimumFloor modelStage (some minimumFaceStage) :=
  buildWithFaceStage kept differential ordinary requested positive minimumFloor modelStage (some minimumFaceStage)

namespace Preparation

variable {kept differential ordinary requested positive minimumFloor modelStage}
variable {minimumFaceStage : Option Nat}
variable (prepared : Preparation kept differential ordinary requested positive minimumFloor modelStage minimumFaceStage)

/-- Read the actual specification, requested floor/model stage, target and original count/allocation. -/
@[expose, macro_inline] def inputs : OddPowerDifferential curve.polynomial × Nat × Nat × Rational × Nat × Rational :=
  prepared.1.val

/-- Read the P-specific requests prepared on the SAME old geometric mesh bank. -/
@[expose, macro_inline] def meshBudgets : FaceMeshBudgets source points
    (Aggregate.perTerm requested (fragmentCount entries))
    (numerator := differential.numerator.scale differential.scale) domains := prepared.2.1.val

/-- Read every once-prepared original fragment allocation before either observation family. -/
@[expose, macro_inline] def allocations : PolynomialComparison.Requests prepared.meshBudgets entries
    (Aggregate.perTerm requested (fragmentCount entries)) := prepared.2.2.1.val

/-- Read the common actual source floor computed before source work/model preparation. -/
@[expose, macro_inline] def sourceFloor : Nat := prepared.2.2.2.1.val

/-- Read the common actual face stage computed before genuine P-bank preparation. -/
@[expose, macro_inline] def faceStage : Nat := prepared.2.2.2.2.1.val

/-- Read the SAME whole source work product at its actual independently retained floor. -/
@[expose, macro_inline] def work : PolynomialWork requests.covered prepared.sourceFloor differential :=
  prepared.2.2.2.2.2.1.val

/-- Read the SAME whole source model product at the separately given model stage. -/
@[expose, macro_inline] def models : prepared.work.Models modelStage := prepared.2.2.2.2.2.2.1.val

/-- Read the one genuine P primitive bank and its independent old-domain anchors and offsets. -/
@[expose, macro_inline] def primitiveBank : FacePrimitiveBank source prepared.faceStage
    (numerator := differential.numerator.scale differential.scale) domains := prepared.2.2.2.2.2.2.2.1.val

/-- Read the one shared P bank on the SAME retained actual meshes. -/
@[expose, macro_inline] def sharedMeshes : FaceSharedMeshes (numerator := differential.numerator.scale
  differential.scale)
    prepared.meshBudgets prepared.primitiveBank := prepared.2.2.2.2.2.2.2.2.1.val

/-- Read the original Closed.withNumerics result, retaining both actual input and new numerical words. -/
@[expose, macro_inline] def changed : Closed.NumeratorWord prepared.sharedMeshes kept :=
  prepared.2.2.2.2.2.2.2.2.2.1.val

/-- Read the SAME complete given old physical/numerical word. -/
@[expose, macro_inline] def oldWord : Closed shared entries geometry roots included := prepared.changed.val.1

/-- Read the new P word on exactly the original leaves, Entry, Finish and root/join indices. -/
@[expose, macro_inline] def word : Closed prepared.sharedMeshes entries geometry roots included :=
  prepared.changed.val.2

/-- Read the one whole comparison cache on these actual source work/models and actual numerical word. -/
@[expose, macro_inline] def comparison : PolynomialComparison.Cache prepared.sharedMeshes requests entries geometry
  roots
    prepared.word prepared.work prepared.models ordinary := prepared.2.2.2.2.2.2.2.2.2.2.1.val

/-- Read the cached literal outgoing-gap sum without another numerical fold. -/
@[expose, macro_inline] def value : Canonical := prepared.comparison.value

/-- Read the cached single-K sum of actual fragment charges without repeating comparison work. -/
@[expose, macro_inline] def bound : Rational := prepared.comparison.bound

/-- The cached value is exactly the SAME actual full outgoing-gap sum. -/
theorem value_eq : prepared.value = gaussianSum (Closed.gaps prepared.sharedMeshes entries geometry roots
    prepared.word) := prepared.comparison.value_eq

/-- The actual old word remains the literal given whole input. -/
theorem oldWord_eq : prepared.oldWord = kept := prepared.changed.property

/-- The original target and count/allocation remain actual retained input data. -/
theorem inputs_eq : prepared.inputs = (differential, minimumFloor, modelStage, requested,
    fragmentCount entries, Aggregate.perTerm requested (fragmentCount entries)) := prepared.1.property

/-- The P budgets retain their one constructor before any primitive observations. -/
theorem meshBudgets_eq : prepared.meshBudgets = FaceMeshBudgets.onNumerator
    (differential.numerator.scale differential.scale) (Aggregate.perTerm requested (fragmentCount entries))
    (Aggregate.perTerm_positive positive _) (Closed.originals shared entries geometry roots kept).val.2.1 :=
  prepared.2.1.property

/-- The original fragment allocations retain their one complete factory. -/
theorem allocations_eq : prepared.allocations = PolynomialComparison.prepareRequests prepared.meshBudgets
    (Aggregate.perTerm requested (fragmentCount entries)) (Aggregate.perTerm_positive positive _) entries :=
  prepared.2.2.1.property

/-- The actual source floor is precisely the maximum of the requested minimum and all original leaf requirements. -/
theorem sourceFloor_eq : prepared.sourceFloor = max minimumFloor
    (PolynomialComparison.sourceFloor prepared.meshBudgets entries prepared.allocations) := prepared.2.2.2.1.property

/-- The actual face stage is precisely the maximum of both mesh and actual leaf requirements. -/
theorem faceStage_eq : prepared.faceStage = selectFaceStage prepared.meshBudgets.index
    (PolynomialComparison.faceFloor prepared.meshBudgets entries prepared.allocations) minimumFaceStage :=
  prepared.2.2.2.2.1.property

/-- The actual numerical stage meets the retained P-specific mesh requirement. -/
theorem meshStage_le : prepared.meshBudgets.index ≤ prepared.faceStage :=
  (PolynomialPreparation.meshStage_le _ _ minimumFaceStage).trans_eq prepared.faceStage_eq.symm

/-- A present independent numerical floor is paid by the actual retained stage. -/
theorem minimumStage_le {minimum : Nat} (specified : minimumFaceStage = some minimum) :
    minimum ≤ prepared.faceStage := by
  have selected := PolynomialPreparation.minimumStage_le prepared.meshBudgets.index
    (PolynomialComparison.faceFloor prepared.meshBudgets entries prepared.allocations) minimum
  have same : prepared.faceStage = selectFaceStage prepared.meshBudgets.index
      (PolynomialComparison.faceFloor prepared.meshBudgets entries prepared.allocations) (some minimum) :=
    prepared.faceStage_eq.trans (congrArg
      (selectFaceStage prepared.meshBudgets.index
        (PolynomialComparison.faceFloor prepared.meshBudgets entries prepared.allocations)) specified)
  exact selected.trans_eq same.symm

/-- The whole source work retains its original given-cover constructor and the actual computed floor. -/
theorem work_eq : prepared.work = PolynomialWork.build requests.covered prepared.sourceFloor differential :=
  prepared.2.2.2.2.2.1.property

/-- The whole source model bank retains its actual original source-work and stage constructor. -/
theorem models_eq : prepared.models = prepared.work.models modelStage := prepared.2.2.2.2.2.2.1.property

/-- The whole genuine numerator primitive bank retains its one original constructor. -/
theorem primitiveBank_eq : prepared.primitiveBank = FacePrimitiveBank.build source prepared.faceStage domains
      (differential.numerator.scale differential.scale) := prepared.2.2.2.2.2.2.2.1.property

/-- The shared P readings retain their one actual factory on the computed common face stage. -/
theorem sharedMeshes_eq : prepared.sharedMeshes = FaceSharedMeshes.build
    (numerator := differential.numerator.scale differential.scale) prepared.meshBudgets prepared.primitiveBank
    prepared.meshStage_le :=
  prepared.2.2.2.2.2.2.2.2.1.property

/-- The whole revalued old/new pair retains its one original physical-cache-preserving constructor. -/
theorem changed_eq : prepared.changed = Closed.withNumerics kept prepared.sharedMeshes :=
  prepared.2.2.2.2.2.2.2.2.2.1.property

/-- The actual whole comparison bank retains its one original constructor, without observation replay. -/
theorem comparison_eq : prepared.comparison = PolynomialComparison.build prepared.sharedMeshes requests entries
    geometry roots prepared.word prepared.work prepared.models ordinary := prepared.2.2.2.2.2.2.2.2.2.2.1.property

/-- The actual K-weighted sum of all retained original charges meets the requested target. -/
theorem bound_lt : prepared.comparison.bound < requested := prepared.2.2.2.2.2.2.2.2.2.2.2.property.1

/-- The SAME actual numerical gap value and SAME ordinary source-model integral meet the requested error. -/
theorem accurate : normSq (prepared.comparison.value -
    (PathModel.mk (PolynomialWork.Models.cells requests.covered prepared.work prepared.models)).integralSample) <
      requested := prepared.2.2.2.2.2.2.2.2.2.2.2.property.2

/-- The literal complete outgoing gap list, including its genuine closing slot, obeys the requested model bound. -/
theorem gaps_accurate : normSq (gaussianSum (Closed.gaps prepared.sharedMeshes entries geometry roots prepared.word) -
    (PathModel.mk (PolynomialWork.Models.cells requests.covered prepared.work prepared.models)).integralSample) <
      requested :=
  Eq.mp (congrArg (fun value : Canonical => normSq (value -
    (PathModel.mk (PolynomialWork.Models.cells requests.covered prepared.work prepared.models)).integralSample) <
      requested) prepared.comparison.value_eq) prepared.accurate

/-- The actual gap list still has exactly the original literal fragment count, including stationary/repeated roles. -/
theorem gaps_length : (Closed.gaps prepared.sharedMeshes entries geometry roots prepared.word).length =
    fragmentCount entries := Closed.gaps_length prepared.sharedMeshes entries geometry roots prepared.word

end Preparation

/-- Consume a GIVEN original next-budget cache before the single actual model and P-bank pipeline.

The whole original Preparation factory is derived from the supplied budget
factory. The returned budget projection is the actual given cache, so
additional fresh-source allocations can precede observations without a
second budget construction. The absent-floor and default constructors
continue to produce their own original budget once.
-/
def buildAtFaceStageWithBudgets (minimumFaceStage : Nat)
    (nextBudgets : Budgets kept differential requested positive) :
    {prepared : Preparation kept differential ordinary requested positive minimumFloor modelStage
        (some minimumFaceStage) //
      prepared = buildAtFaceStage kept differential ordinary requested positive minimumFloor modelStage
          minimumFaceStage ∧ prepared.meshBudgets = nextBudgets.val} :=
  let prepared := buildGivenBudgets kept differential ordinary requested positive minimumFloor modelStage
    (some minimumFaceStage) nextBudgets
  have factory : prepared = buildAtFaceStage kept differential ordinary requested positive minimumFloor modelStage
      minimumFaceStage := by
    apply congrArg (buildGivenBudgets kept differential ordinary requested positive minimumFloor modelStage
      (some minimumFaceStage))
    exact Subtype.ext nextBudgets.property
  have sameBudget : prepared.meshBudgets = nextBudgets.val := by rfl
  ⟨prepared, factory, sameBudget⟩

end PolynomialPreparation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.Closed
