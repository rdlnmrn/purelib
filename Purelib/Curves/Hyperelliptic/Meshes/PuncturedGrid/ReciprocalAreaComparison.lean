module
import Purelib.Data.Rat.Bounds.Quarter
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularReciprocalAreaComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RamifiedReciprocalAreaComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

public section

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation

/-!
# Intrinsic reciprocal-chart requests for the shared grid surface

The curve's degree shape chooses the regular construction or the ramified
construction. Each outcome retains its actual comparison certificate and
caches its complete source and cap paths. Surface consumers share this
interface for endpoint, translated-area and full-path error estimates.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {start finish : Gaussian.Basic.Canonical} {segment : Geometry.ClearPath.ClearSegment curve.polynomial
    (Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {placement : Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement piece
    differential parentSheet}

set_option genInjectivity false in
/-- Intrinsic degree shape selects the actual chart construction. -/
inductive CapRequest (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation regular compared)
  (target areaTarget : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original regular cap request selected by even degree. -/ | regular (request :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest prepared target
    areaTarget floor)
  /-- The original ramified cap request with its retained odd-degree identity. -/ | ramified (degree :
    curve.polynomial.natDegree = 2 * genus + 1)
      (request : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
        prepared target areaTarget floor)

constructive_injectivity CapRequest

namespace CapRequest

variable {prepared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation
  regular compared} {target areaTarget : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest in
/-- Use the curve's original degree shape to prepare the regular or ramified request with both positive targets. -/
@[expose] def build (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation regular compared)
  (target areaTarget : Normalization.InverseRootPolynomial.Coordinate)
    (positive : 0 < target) (areaPositive : 0 < areaTarget) (floor : Nat) :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest prepared target
      areaTarget floor :=
  match curve.degreeShape with
  | .even degree => .regular
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest.build prepared
    degree target areaTarget positive areaPositive floor)
  | .odd degree => .ramified degree
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest.build
    prepared target areaTarget positive areaPositive floor)

/-- Either original cap construction retains a positive scalar target. -/
theorem positive : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
  prepared target areaTarget floor → 0 < target
  | .regular request => request.positive
  | .ramified _ request => request.positive

/-- Read the exact original face-fragment budget from the selected cap request. -/
@[expose] def budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
  prepared target areaTarget floor →
    Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy compared.entered.globalBounds compared.entered.domain.steps
      compared.entered.mesh.splits.pieceCount (((target / 4) / 4) / 4)
  | .regular request => request.budget
  | .ramified _ request => request.budget

/-- Read the selected original cap model's required stage. -/
@[expose] def capIndex : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
  prepared target areaTarget floor → Nat
  | .regular request => request.request.index
  | .ramified _ request => request.request.index

/-- Take the maximum of the original cap stage and retained face-grid stage. -/
@[expose] def index (request :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest prepared target
  areaTarget floor) : Nat := max request.capIndex request.budget.grid.index

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest in
/-- Read the selected original cap request's numerical reading stage. -/
@[expose] def readingIndex :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest prepared target
  areaTarget floor → Nat
  | .regular request => request.readingIndex
  | .ramified _ request => request.readingIndex

variable {index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest in
/-- The actual evaluation certificate of the selected original regular or ramified cap construction. -/
@[expose] def Data (request :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest prepared target
  areaTarget floor)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth readingIndex :
      Nat) : Type 2 :=
  match request with
  | .regular request =>
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest.Evaluation
    request sample depth readingIndex
  | .ramified _ request =>
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest.Evaluation
    request sample depth readingIndex

namespace Data

variable {request :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest prepared
  target areaTarget floor}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
/-- Read the complete original source increment path from the selected certificate. -/
@[expose] def sourcePath (data :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data request sample
  depth readingIndex) : List Gaussian :=
  match request, data with
  | .regular _, data => (data.cap.original.parents.pairs.map Prod.fst).flatten
  | .ramified _ _, data => (data.cap.separated.parents.pairs.map Prod.fst).flatten

/-- Read the complete original regular or ramified cap increment path. -/
@[expose] def capPath (data :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data request sample
  depth readingIndex) : List Gaussian :=
  match request, data with
  | .regular _, data => (data.cap.parents.pairs.map Prod.snd).flatten
  | .ramified _ _, data => (data.cap.blocks.map (fun block => block.1 :: block.2)).flatten

/-- Read the original summary of the exact retained source path. -/
@[expose] def left (data :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data request sample
  depth readingIndex) : Path.IncrementArea.Summary
  (Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data.sourcePath data)
  :=
  match request, data with
  | .regular _, data => data.cap.original.left
  | .ramified _ _, data => data.cap.separated.left

/-- Read the original summary of the exact retained cap path. -/
@[expose] def right (data :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data request sample
  depth readingIndex) : Path.IncrementArea.Summary
  (Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data.capPath data) :=
  match request, data with
  | .regular _, data => data.cap.cap
  | .ramified _ _, data => data.cap.cap

end Data

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest in
set_option genInjectivity false in
/-- Retain the selected chart certificate and flatten each actual path once. -/
structure Evaluation (request :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest prepared target
  areaTarget floor)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth readingIndex :
      Nat) where
  /-- The actual original selected cap evaluation certificate. -/ data :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data request sample
    depth readingIndex
  /-- The two complete original increment paths cached once. -/ paths : List Gaussian.Basic.Canonical × List
    Gaussian.Basic.Canonical
  /-- The cached paths equal the exact source and cap projections of the retained original certificate. -/ paths_eq :
    paths =
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data.sourcePath data,
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data.capPath data)

constructive_injectivity Evaluation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest in
/-- Evaluate the selected original cap request and cache both complete actual paths once. -/
@[expose] def evaluate (request :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest prepared target
  areaTarget floor)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth readingIndex :
      Nat)
    (later : request.index ≤ index) (readingLater : request.readingIndex ≤ readingIndex) :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
      sample depth readingIndex :=
  let data : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data request
    sample depth readingIndex := match request with
    | .regular request => request.evaluate sample depth readingIndex later readingLater
    | .ramified _ request => request.evaluate sample depth readingIndex later readingLater
  ⟨data, (Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data.sourcePath
    data, Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data.capPath
    data), rfl⟩

namespace Evaluation

variable {request :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest prepared
  target areaTarget floor}

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
/-- Read the cached original complete source path. -/
@[expose] def sourcePath (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) : List Gaussian := evaluated.paths.1

/-- Read the cached original complete cap path. -/
@[expose] def capPath (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) : List Gaussian := evaluated.paths.2

/-- Transport the existing original source summary to the exact cached path. -/
@[expose] def left (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) : Path.IncrementArea.Summary evaluated.sourcePath := by
  rw
    [sourcePath,
    evaluated.paths_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data.left
    evaluated.data

/-- Transport the existing original cap summary to the exact cached path. -/
@[expose] def right (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) : Path.IncrementArea.Summary evaluated.capPath := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation.capPath,
    evaluated.paths_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Data.right
    evaluated.data

/-- Read the original entered-face reference from the retained selected certificate. -/
@[expose] def reference (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference compared.entered ((target / 4) / 4) :=
  match request, evaluated.data with
  | .regular _, data => data.reference
  | .ramified _ _, data => data.reference

/-- Read the exact original controlled-sum request used by the selected source evaluation. -/
@[expose] def source (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) :
    Readings.PreparedControlledPrimitiveRequests.ControlledSumRequest compared.entered.cache.parents genus (((target /
      4) / 4) / 4) :=
  match request, evaluated.data with
  | .regular _, data => data.cap.original.compared.source
  | .ramified _ _, data => data.cap.separated.compared.source

/-- The retained face reference uses the original request's exact fragment budget. -/
theorem budget_eq (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) :
    evaluated.reference.budget = request.budget := by
  cases request with
  | regular request => exact evaluated.data.budget_eq
  | ramified degree request => exact evaluated.data.budget_eq

/-- The retained reference and source evaluation use exactly the same original controlled request. -/
theorem source_eq (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) :
    evaluated.reference.request = evaluated.source := by
  cases request with
  | regular request => exact evaluated.data.source_eq
  | ramified degree request => exact evaluated.data.source_eq

/-- The retained reference value equals the original source summary's total. -/
theorem value_eq (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) :
    evaluated.reference.value = evaluated.left.total := by
  rcases evaluated with ⟨data, paths, rfl⟩
  cases request with
  | regular request => exact data.value_eq
  | ramified degree request => exact data.value_eq

/-- The complete original source total satisfies the retained geometric magnitude bound. -/
theorem source_bounded (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) :
    Data.Gaussian.Norm.Basic.normSq evaluated.left.total ≤ prepared.sourceBound := by
  rcases evaluated with ⟨data, paths, rfl⟩
  cases request with
  | regular request => exact data.source_bounded
  | ramified degree request => exact data.source_bounded

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest in
/-- The two complete original path totals differ by less than one quarter of the scalar target. -/
theorem total_close (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.left.total - evaluated.right.total) < target / 4 := by
  rcases evaluated with ⟨data, paths, rfl⟩
  cases request with
  | regular request =>
      have quarterPositive := Fraction.Order.Field.div_pos_direct request.positive (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
      have localPositive := Fraction.Order.Field.div_pos_direct quarterPositive (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
      exact data.cap.total_close.trans ((Rat.Bounds.Quarter.quarter_lt_self localPositive).trans
        (Rat.Bounds.Quarter.quarter_lt_self quarterPositive))
  | ramified degree request => exact data.cap.total_close

/-- The two complete original path areas differ by less than the retained area target. -/
theorem area_close (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.left.area - evaluated.right.area) < areaTarget := by
  rcases evaluated with ⟨data, paths, rfl⟩
  cases request with
  | regular request => exact data.cap.area_close
  | ramified degree request => exact data.cap.area_close

/-- The actual shared face-corner increment differs from the original source total by less than one sixteenth of the
target. -/
theorem corner_source_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      compared.domains = domains.atRoute placement.location)
    {faceIndex : Nat} (later : request.budget.grid.index ≤ faceIndex) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement placement.location - evaluated.left.total) < (target / 4)
      / 4 := by
  rcases evaluated with ⟨data, paths, rfl⟩
  cases request with
  | regular request => exact data.corner_source_error aligned later shared
  | ramified degree request => exact data.corner_source_error aligned later shared

/-- The actual shared face-corner increment differs from the original cap total by less than the scalar target. -/
theorem corner_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      compared.domains = domains.atRoute placement.location)
    {faceIndex : Nat} (later : request.budget.grid.index ≤ faceIndex) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement placement.location - evaluated.right.total) < target := by
  rcases evaluated with ⟨data, paths, rfl⟩
  cases request with
  | regular request => exact data.corner_error aligned later shared
  | ramified degree request => exact data.corner_error aligned later shared

/-- The original oriented triangle-source increment differs from the retained cap total by less than the target. -/
theorem triangle_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      compared.domains = domains.atRoute placement.location)
    {faceIndex : Nat} (later : request.budget.grid.index ≤ faceIndex) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (placement.location.sourceEdge.increment readings.values -
      evaluated.right.total) < target := by
  rcases evaluated with ⟨data, paths, rfl⟩
  cases request with
  | regular request => exact data.triangle_error aligned later readings
  | ramified degree request => exact data.triangle_error aligned later readings

/-- The actual triangle chord and full retained cap trace satisfy the anchor-weighted error bound with the cap's
internal area preserved. -/
theorem triangle_area_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      compared.domains = domains.atRoute placement.location)
    {faceIndex : Nat} (later : request.budget.grid.index ≤ faceIndex) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) (anchor :
      Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Path.BoundaryRibbon.area anchor (anchor +
      placement.location.sourceEdge.increment readings.values) + evaluated.right.area -
      Path.IncrementArea.traceArea anchor evaluated.capPath) ≤ 4 * Data.Gaussian.Norm.Basic.normSq anchor * target
        := by
  rcases evaluated with ⟨data, paths, rfl⟩
  cases request with
  | regular request => exact data.triangle_area_error aligned later readings anchor
  | ramified degree request => exact data.triangle_area_error aligned later readings anchor

/-- The full original source and cap traces at the same supplied anchor satisfy the retained area and endpoint-error
allowance. -/
theorem translated_area_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation request
  sample depth readingIndex) (anchor : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.traceArea anchor evaluated.sourcePath -
      Path.IncrementArea.traceArea anchor evaluated.capPath) <
      2 * (areaTarget + 4 * Data.Gaussian.Norm.Basic.normSq anchor * (target / 4)) := by
  rcases evaluated with ⟨data, paths, rfl⟩
  cases request with
  | regular request => exact data.translated_area_error anchor
  | ramified degree request => exact data.translated_area_error anchor

end

end Evaluation
end CapRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
