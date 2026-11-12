module
import Purelib.Polynomial.Dense.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Geometry.Rectangle.Partition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Riemann.Readings.RectangularPrimitiveBoundary

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Original fine-mesh readings on certified lifted partial edges

Every original fragment keeps its own endpoint parameters inside an actual
lifted grid edge. Reindexing the cached face data preserves its numerical
increment exactly; it does not replace a partial edge with its full side.
-/

open Purelib.Riemann.Integration.RectangularSharedPrimitives renaming SharedPrimitiveValues -> SharedValues

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.BranchCellBank

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {numerator : CoefficientPolynomial}

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {source : Differentials.Basic.Differential
    genus} {points : List Gaussian.Basic.Canonical} {target : Fraction.Rational} {index : Nat}

/-- Transporting the retained original domain identity preserves every point reading exactly. -/
theorem DomainMeshReadings.castDomain_atPoint {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    {first last : Periods.PeriodDomain models sheet} (equal : first = last)
    {budget : CommonMeshes.DomainMeshBudget first source points target (numerator := numerator)}
      {numerics : PrimitiveData.DomainPrimitives first source index (numerator := numerator)}
    (readings : CommonMeshes.DomainMeshReadings budget numerics) (point :
      Gaussian.Basic.Canonical) :
    SharedValues.atPoint
      (CommonMeshes.DomainMeshReadings.castDomain equal readings).readings point
      = SharedValues.atPoint readings.readings point := by
  cases equal
  rfl

/-- Transporting the retained original face identity preserves every selected-sheet point reading exactly. -/
theorem FaceMeshReadings.castFace_atPoint {first last : Meshes.PuncturedGridFaces.RegularFace bank} (equal : first =
  last)
    {domains : DomainBanks.FaceDomains frames first} {budget :
      CommonMeshes.FaceMeshBudget domains source points target (numerator := numerator)}
    {numerics : PrimitiveData.FacePrimitives domains source index (numerator := numerator)} (readings :
      CommonMeshes.FaceMeshReadings budget numerics)
    (sheet : Fin 2) (point : Gaussian.Basic.Canonical) :
    SharedValues.atPoint
      ((CommonMeshes.FaceMeshReadings.castFace equal readings).atSheet
      sheet).readings point = SharedValues.atPoint (readings.atSheet
      sheet).readings point := by
  cases equal
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.BranchCellBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {numerator : CoefficientPolynomial}

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment renaming FragmentSheets -> SheetEntries

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {source : Differentials.Basic.Differential genus} {axes :
    PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : DomainBanks.FaceDomainBank frames base.faces.regulars} {mesh :
    Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Fraction.Rational} {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational}
    {index : Nat}
  {budgets : CommonMeshes.FaceMeshBudgets source points tolerance (numerator := numerator) domains}
    {numerics : PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}

namespace RegularPrimitiveFragment.SheetEntry

variable {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve source} {cuts : List Fraction.Rational}
  {partition : Rectangle.AxisPartition 0 1 cuts}
  {interval : PreparedAxisPartitions.Interval} {fragment :
    RegularFaces.RegularPrimitiveFragment axes parent partition interval}
  {request : Readings.UniformPreparedRequests.LocalRequest parent count target} {assigned :
    SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains
    request}

/-- Read the original partial endpoints through their certified containing
lifted edge. Its complete grid endpoints are retained only for transport. -/
@[expose] def LiftedSource.value (located :
  LiftedEdges.SheetEntry.LiftedSource assigned mesh) (shared :
  CommonMeshes.FaceSharedMeshes budgets numerics) : Gaussian :=
  let readings := ((MeshWords.FaceSharedMeshes.atRoute shared
    located.side.route).atSheet located.side.route.sheet).readings
  SharedValues.atPoint readings fragment.located.last -
    SharedValues.atPoint readings fragment.located.first

/-- The original fragment reading equals the retained indexed face-bank reading on its exact sheet. -/
private theorem original_atPoint (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) (point :
      Gaussian.Basic.Canonical) :
    SharedValues.atPoint
      (BankReadings.meshReadings assigned shared).readings point =
      SharedValues.atPoint
        ((CommonMeshes.FaceSharedMeshes.get shared
          fragment.face.located.index).atSheet assigned.entry.sheet).readings point :=
  (BranchCellBank.DomainMeshReadings.castDomain_atPoint
    assigned.domain_eq.symm
    (((CommonMeshes.FaceSharedMeshes.get shared
      fragment.face.located.index).castFace fragment.face.located.indexed).atSheet assigned.entry.sheet) point).trans
      (BranchCellBank.FaceMeshReadings.castFace_atPoint
        fragment.face.located.indexed (CommonMeshes.FaceSharedMeshes.get shared
        fragment.face.located.index) assigned.entry.sheet point)

/-- The certified lifted source reads the same retained face and sheet as the original fragment. -/
private theorem source_atPoint (located :
  LiftedEdges.SheetEntry.LiftedSource assigned mesh)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) (point :
      Gaussian.Basic.Canonical) :
    SharedValues.atPoint
      ((MeshWords.FaceSharedMeshes.atRoute shared located.side.route).atSheet
        located.side.route.sheet).readings point =
      SharedValues.atPoint
        ((CommonMeshes.FaceSharedMeshes.get shared
          fragment.face.located.index).atSheet assigned.entry.sheet).readings point := by
  have same :=
    BranchCellBank.FaceMeshReadings.castFace_atPoint
    located.side.route.face_eq
    (CommonMeshes.FaceSharedMeshes.get shared located.side.route.position)
      located.side.route.sheet point
  exact same.trans (congrArg₂
    (fun position sheet => SharedValues.atPoint
      ((CommonMeshes.FaceSharedMeshes.get shared position).atSheet
        sheet).readings point)
    located.side.position_eq located.side.sheet_eq)

/-- The lifted partial-edge value equals the original fragment's endpoint difference. -/
theorem LiftedSource.value_eq (located : LiftedEdges.SheetEntry.LiftedSource
  assigned mesh) (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :

      LiftedSource.value
      located shared =
      SharedValues.atPoint
        (BankReadings.meshReadings assigned shared).readings
          fragment.located.last -
      SharedValues.atPoint
        (BankReadings.meshReadings assigned shared).readings
          fragment.located.first := by
  exact congrArg₂ (· - ·)

      ((source_atPoint
      located shared fragment.located.last).trans
      (original_atPoint
      assigned shared fragment.located.last).symm)

      ((source_atPoint
      located shared fragment.located.first).trans
      (original_atPoint
      assigned shared fragment.located.first).symm)

/-- The cached original fragment value equals its exact certified lifted partial-edge reading. -/
theorem BankReading.value_eq_lifted {budgets : CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : PrimitiveData.FacePrimitiveBank source index domains}
    {shared : CommonMeshes.FaceSharedMeshes
  budgets numerics}
    (reading : BankReadings.BankReading assigned shared) (located :
      LiftedEdges.SheetEntry.LiftedSource assigned mesh) : reading.value =
      LiftedSource.value
      located shared :=
  reading.value_eq.trans
    (LiftedSource.value_eq
    located shared).symm

end RegularPrimitiveFragment.SheetEntry

namespace RegularPrimitiveFragments.SheetEntries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries
  (BankReadings)

variable {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve source} {partition :
  Rectangle.AxisPartition 0 1 (axes.parameters parent)}
  {request : Readings.UniformPreparedRequests.LocalRequest parent count target}

set_option genInjectivity false in
/-- The dependent certified lifted sources of the original fragment spine.

Retain each actual partial edge and its original endpoint parameters. -/
inductive LiftedSources (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    {intervals : List PreparedAxisPartitions.Interval} → {fragments :
      RegularFaces.RegularPrimitiveFragments axes parent partition
      intervals} →
      FragmentSheets domains request
        fragments → Type
  /-- The empty original fragment source spine. -/ | nil :
    LiftedSources
    mesh .nil
  /-- Prepend the retained original fragment sources to their exact dependent tail. -/ | cons {interval :
    PreparedAxisPartitions.Interval} {intervals : List
    PreparedAxisPartitions.Interval}
      {head : RegularFaces.RegularPrimitiveFragment axes parent partition
        interval} {tail : RegularFaces.RegularPrimitiveFragments axes parent
        partition intervals}
      {entry : SheetEntries.RegularPrimitiveFragment.SheetEntry head domains
        request} {entries :
        FragmentSheets domains request
        tail}
      (first : LiftedEdges.SheetEntry.LiftedSource entry mesh) (remaining :
        LiftedSources
        mesh entries) :

        LiftedSources
        mesh (.cons entry entries)

constructive_injectivity LiftedSources

namespace LiftedSources

/-- Locate every original fragment occurrence in its certified containing lifted edge. -/
@[expose] def build (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    ∀ {intervals : List PreparedAxisPartitions.Interval} {fragments :
      RegularFaces.RegularPrimitiveFragments axes parent partition
      intervals}
      (entries : FragmentSheets domains
        request fragments),
        LiftedSources
        mesh entries
  | _, _, .nil => .nil
  | _, _, .cons first rest => .cons
    (LiftedEdges.SheetEntry.LiftedSource.build first mesh)
    (build
    mesh rest)

/-- Read the ordered original fragment endpoint differences from one retained shared bank. -/
@[expose] def values (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    ∀ {intervals : List PreparedAxisPartitions.Interval} {fragments :
      RegularFaces.RegularPrimitiveFragments axes parent partition
      intervals}
      {entries : FragmentSheets domains
        request fragments},
        LiftedSources
        mesh entries → List Gaussian.Basic.Canonical
  | _, _, _, .nil => []
  | _, _, _, .cons first rest =>
    RegularPrimitiveFragment.SheetEntry.LiftedSource.value
    first shared ::
    values
    shared rest

/-- The lifted partial-edge values equal the complete original fragment reading list. -/
theorem values_eq {budgets : CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : PrimitiveData.FacePrimitiveBank source index domains}
    {shared : CommonMeshes.FaceSharedMeshes budgets numerics}
    {intervals : List PreparedAxisPartitions.Interval} {fragments :
      RegularFaces.RegularPrimitiveFragments axes parent partition
      intervals}
    {entries : FragmentSheets domains
      request fragments} (located :
      LiftedSources
      mesh entries) (readings :
      SharedSums.RegularPrimitiveFragments.SheetEntries.BankReadings shared
      entries) :
    located.values shared = readings.values := by
  induction located with
  | nil => cases readings; rfl
  | cons first rest ih =>
      cases readings with
      | cons head tail =>
        exact congrArg₂ List.cons
          (RegularPrimitiveFragment.SheetEntry.BankReading.value_eq_lifted head first).symm (ih tail)

end LiftedSources
end RegularPrimitiveFragments.SheetEntries

namespace RegularPrimitiveSplits.SheetEntries

open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment renaming SplitSheets -> SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries
  (BankReadings SharedSum)

set_option genInjectivity false in
/-- The dependent certified lifted sources of the original parent-fragment spine.

Retain each actual partial edge and its original endpoint parameters. -/
inductive LiftedSources (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} → {splits :
      PreparedPrimitiveSplits.PrimitiveSplits axes parents} →
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
      splits} → {requests : Readings.UniformPreparedRequests.RequestedParents count target parents} →
      SheetEntries domains fragments requests → Type 2
  /-- The empty original parent-fragment source spine. -/ | nil :
    LiftedSources
    mesh .nil
  /-- Prepend the retained original parent-fragment sources to their exact dependent tail. -/ | cons {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve source} {parents : List
    (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)}
      {partition : Rectangle.AxisPartition 0 1 (axes.parameters parent)} {splits :
        PreparedPrimitiveSplits.PrimitiveSplits axes parents}
      {head : RegularFaces.RegularPrimitiveFragments axes parent partition
        partition.intervals} {tail : RegularFaces.RegularPrimitiveSplits
        (base := base) axes splits}
      {request : Readings.UniformPreparedRequests.LocalRequest parent count target} {requests :
        Readings.UniformPreparedRequests.RequestedParents count target parents}
      {first : FragmentSheets domains
        request head} {rest : SheetEntries domains tail requests}
      (headSources :
        RegularPrimitiveFragments.SheetEntries.LiftedSources
        mesh first) (tailSources :
        LiftedSources
        mesh rest) :

        LiftedSources
        mesh (.cons first rest)

constructive_injectivity LiftedSources

namespace LiftedSources

/-- Locate every original parent-fragment occurrence in its certified containing lifted edge. -/
@[expose] def build (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    ∀ {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
      PreparedPrimitiveSplits.PrimitiveSplits axes parents}
      {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
        splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
      (entries : SheetEntries domains fragments requests),
        LiftedSources
        mesh entries
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons first rest => .cons
    (RegularPrimitiveFragments.SheetEntries.LiftedSources.build
    mesh first)
    (build
    mesh rest)

/-- Read the ordered original parent-fragment endpoint differences from one retained shared bank. -/
@[expose] def values (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    ∀ {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
      PreparedPrimitiveSplits.PrimitiveSplits axes parents}
      {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
        splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
      {entries : SheetEntries domains fragments requests},
        LiftedSources
        mesh entries → List Gaussian.Basic.Canonical
  | _, _, _, _, _, .nil => []
  | _, _, _, _, _, .cons first rest => first.values shared ++
    values
    shared rest

/-- The lifted partial-edge values equal the complete original parent-fragment reading list. -/
theorem values_eq {budgets : CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : PrimitiveData.FacePrimitiveBank source index domains}
    {shared : CommonMeshes.FaceSharedMeshes budgets numerics}
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
      PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
      splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
    {entries : SheetEntries domains fragments requests} (located :
      LiftedSources
      mesh entries) (readings : BankReadings shared entries) :
    located.values shared = readings.values := by
  induction located with
  | nil => cases readings; rfl
  | cons first rest ih =>
      cases readings with
      | cons head tail => exact congrArg₂ List.append (first.values_eq head) (ih tail)

/-- The finite sum of the actual lifted partial-edge readings equals the retained original shared sum. -/
theorem sum_eq {budgets : CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : PrimitiveData.FacePrimitiveBank source index domains}
    {shared : CommonMeshes.FaceSharedMeshes budgets numerics}
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
      PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
      splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
    {entries : SheetEntries domains fragments requests} (located :
      LiftedSources
      mesh entries) (summary :
      SharedSum shared
      entries) :
    Gaussian.Norm.Sum.Basic.gaussianSum (located.values shared) = summary.value := by
  rw [located.values_eq summary.readings, summary.value_eq, summary.values_eq]

end LiftedSources
end RegularPrimitiveSplits.SheetEntries
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid
