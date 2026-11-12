module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

/-! # True numerator banks on the same retained physical closed fragment word

The given domain cache and geometric meshes survive. Full-numerator
bounds and requests are selected before the new lazy primitive/readings
bank is forced. The whole old physical word supplies every Point, Finish,
Entry and actual internal/adjacent/closing join cache.
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

/-- Actual supplied domains/target, full-numerator requests, selected common stage and numerical closed-word caches.

The old whole cache remains data. Every new numerical owner is an existing
original bank type, and every complete factory is retained. The new stage
is selected from genuine P-specific budgets before preparing its values.
-/
abbrev NumeratorPreparation (numerator : CoefficientPolynomial) (nextTolerance : Rational)
    (positive : 0 < nextTolerance) :=
  {value : FaceDomainBank frames base.faces.regulars × CoefficientPolynomial × Rational //
    value = (domains, numerator, nextTolerance)} ×
  (Σ nextBudgets : {value : FaceMeshBudgets source points nextTolerance (numerator := numerator) domains //
    value = FaceMeshBudgets.onNumerator numerator nextTolerance positive
      (Closed.originals shared entries geometry roots kept).val.2.1},
  Σ stage : {value : Nat // value = nextBudgets.val.index},
  Σ primitives : {value : FacePrimitiveBank source stage.val (numerator := numerator) domains //
    value = FacePrimitiveBank.build source stage.val domains numerator},
  Σ nextShared : {value : FaceSharedMeshes (numerator := numerator) nextBudgets.val primitives.val //
    value = FaceSharedMeshes.build (numerator := numerator) nextBudgets.val primitives.val
      (Nat.le_of_eq stage.property.symm)},
  Closed.NumeratorWord nextShared.val kept)

section Preparation

variable (domains)

/-- Select real full-numerator requests, then materialize new values on the SAME actual retained physical word.

The original domain cache is an explicit runtime input. The stored old
budget pointer is read from the given Closed cache. Each new request uses
its own genuine numerator bounds and retains the whole old mesh; no old
dx/y accuracy is relabelled. Only after computing the common stage are
new primitive/readings banks prepared and the existing physical caches
reused for their actual numerical gaps.
-/
def prepareNumerator (numerator : CoefficientPolynomial) (nextTolerance : Rational) (positive : 0 < nextTolerance) :
    NumeratorPreparation kept numerator nextTolerance positive :=
  let inputs : {value : FaceDomainBank frames base.faces.regulars × CoefficientPolynomial × Rational //
      value = (domains, numerator, nextTolerance)} := ⟨(domains, numerator, nextTolerance), rfl⟩
  let original := Closed.originals shared entries geometry roots kept
  let nextBudgets : {value : FaceMeshBudgets source points nextTolerance (numerator := numerator) domains //
      value = FaceMeshBudgets.onNumerator numerator nextTolerance positive original.val.2.1} :=
    ⟨FaceMeshBudgets.onNumerator numerator nextTolerance positive original.val.2.1, rfl⟩
  let stage : {value : Nat // value = nextBudgets.val.index} := ⟨nextBudgets.val.index, rfl⟩
  let primitives : {value : FacePrimitiveBank source stage.val (numerator := numerator) domains //
      value = FacePrimitiveBank.build source stage.val domains numerator} :=
    ⟨FacePrimitiveBank.build source stage.val domains numerator, rfl⟩
  let nextShared : {value : FaceSharedMeshes (numerator := numerator) nextBudgets.val primitives.val //
      value = FaceSharedMeshes.build (numerator := numerator) nextBudgets.val primitives.val
        (Nat.le_of_eq stage.property.symm)} :=
    ⟨FaceSharedMeshes.build (numerator := numerator) nextBudgets.val primitives.val
      (Nat.le_of_eq stage.property.symm), rfl⟩
  let word := Closed.withNumerics (numerator := oldNumerator) (index := index)
    (newNumerator := numerator) (newIndex := stage.val) (newBudgets := nextBudgets.val)
    (newNumerics := primitives.val) (shared := shared) (entries := entries) (geometry := geometry) (roots := roots)
    kept nextShared.val
  ⟨inputs, nextBudgets, stage, primitives, nextShared, word⟩

end Preparation

namespace NumeratorPreparation

variable {kept} {numerator : CoefficientPolynomial} {nextTolerance : Rational} {positive : 0 < nextTolerance}
variable (prepared : NumeratorPreparation kept numerator nextTolerance positive)

/-- Read the genuine new numerator request bank on the SAME actual geometric meshes. -/
@[expose] def meshBudgets : FaceMeshBudgets source points nextTolerance (numerator := numerator) domains :=
  prepared.2.1.val

/-- Read the common numerical stage computed before any new primitive bank is forced. -/
@[expose] def stage : Nat := prepared.2.2.1.val

/-- Read the genuine cached P-numerator primitive bank with all of its actual independent offsets. -/
@[expose] def primitiveBank : FacePrimitiveBank source prepared.stage (numerator := numerator) domains :=
  prepared.2.2.2.1.val

/-- Read the actual shared values on those same original geometric meshes and true P primitives. -/
@[expose] def sharedMesh : FaceSharedMeshes (numerator := numerator)
    prepared.meshBudgets prepared.primitiveBank := prepared.2.2.2.2.1.val

/-- Read the complete old input word retained as data, without replacing its observations or numbers. -/
@[expose] def oldWord : Closed shared entries geometry roots included := prepared.2.2.2.2.2.val.1

/-- Read the actual new-numerator closed word on the SAME original source/geometric/root indices. -/
@[expose] def word : Closed prepared.sharedMesh entries geometry roots included := prepared.2.2.2.2.2.val.2

/-- The complete original domain owner and both requested numerical inputs remain actual retained data. -/
theorem inputs_eq : prepared.1.val = (domains, numerator, nextTolerance) := prepared.1.property

/-- The full old word remains its actual original input, including all old numerical/physical caches. -/
theorem oldWord_eq : prepared.oldWord = kept := prepared.2.2.2.2.2.property

/-- Every new accuracy is prepared from actual numerator bounds on the given retained old mesh bank. -/
theorem meshBudgets_eq : prepared.meshBudgets = FaceMeshBudgets.onNumerator numerator nextTolerance positive
    (Closed.originals shared entries geometry roots kept).val.2.1 := prepared.2.1.property

/-- The new common stage is exactly the maximum selected by those same retained P-specific requests. -/
theorem stage_eq : prepared.stage = prepared.meshBudgets.index := prepared.2.2.1.property

/-- The true numerator primitive bank is the original shared constructor on the same domain cache and chosen stage. -/
theorem primitiveBank_eq : prepared.primitiveBank =
    FacePrimitiveBank.build source prepared.stage domains numerator := prepared.2.2.2.1.property

/-- The entire new shared value bank retains its original one-constructor factory and real sufficient stage proof. -/
theorem sharedMesh_eq : prepared.sharedMesh = FaceSharedMeshes.build (numerator := numerator)
    prepared.meshBudgets prepared.primitiveBank
    (Nat.le_of_eq prepared.stage_eq.symm) := prepared.2.2.2.2.1.property

/-- The actual new numerator increments obey the original whole signed K-gap telescope, with all nonzero offsets. -/
theorem telescope : gaussianSum (Closed.increments prepared.sharedMesh entries geometry roots prepared.word) =
    gaussianSum (Closed.gaps prepared.sharedMesh entries geometry roots prepared.word) :=
  Closed.telescope prepared.sharedMesh entries geometry roots prepared.word

/-- Exactly one original outgoing slot survives for each actual original fragment, including literal closing. -/
theorem gaps_length : (Closed.gaps prepared.sharedMesh entries geometry roots prepared.word).length =
    SplitSheets.fragmentCount entries := Closed.gaps_length prepared.sharedMesh entries geometry roots prepared.word

end NumeratorPreparation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.Closed
