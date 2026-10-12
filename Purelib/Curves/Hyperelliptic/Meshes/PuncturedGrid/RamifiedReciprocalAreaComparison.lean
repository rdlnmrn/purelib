module
import Purelib.Data.Rat.Bounds.Quarter
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEstimates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
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
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

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
# Connected cap paths consumed by the actual shared grid primitives

Preparation retains the entered face occurrence and its original parent
cache. A request selects the face-comparison floor before evaluating one cap
sample. The shared triangle edge is compared with the total of that same
connected cap path. Full source/cap area and primitive-origin terms remain
explicit; the path's internal area is not replaced by its endpoint chord.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences

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
/-- A scalar and area request on the original ramified cap preparation.

Retain the entered face and parents, fragment budget and connected request with their original independent targets. -/
structure RamifiedCapRequest (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation regular compared)
  (target areaTarget : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original scalar comparison target is positive. -/ positive : 0 < target
  /-- The fragment budget for the actual original domain steps and piece count. -/ budget :
    Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy compared.entered.globalBounds compared.entered.domain.steps
    compared.entered.mesh.splits.pieceCount (((target / 4) / 4) / 4)
  /-- The original connected cap request with its retained scalar and area targets. -/ request :
    Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest prepared.path (target / 4) areaTarget (max floor
    budget.minimumIndex)

constructive_injectivity RamifiedCapRequest

namespace RamifiedCapRequest

variable {prepared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation
  regular compared} {target areaTarget : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Allocate the original cap and fragment targets and prepare the connected request above the supplied floor. -/
@[expose] def build (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation regular compared)
  (target areaTarget : Normalization.InverseRootPolynomial.Coordinate)
    (positive : 0 < target) (areaPositive : 0 < areaTarget) (floor : Nat) :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest prepared
      target areaTarget floor :=
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  have localPositive := Fraction.Order.Field.div_pos_direct quarterPositive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  let budget := Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy.build compared.entered.globalBounds
    compared.entered.domain.steps
    compared.entered.mesh.splits.pieceCount (((target / 4) / 4) / 4)
    (Fraction.Order.Field.div_pos_direct localPositive (by decide))
  ⟨positive, budget, Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest.build prepared.path (target /
    4) areaTarget quarterPositive areaPositive
    (max floor budget.minimumIndex)⟩

/-- One common polynomial stage can serve the cap and the face bank. -/
@[expose] def index (request :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest prepared target
  areaTarget floor) : Nat := max request.request.index request.budget.grid.index

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  in
/-- Read the exact numerical index required by the retained original connected request. -/
@[expose] def readingIndex (request :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest prepared target
  areaTarget floor) : Nat := request.request.readingIndex

variable {index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  in
set_option genInjectivity false in
/-- The actual original cap evaluation and its same-source reference.

Retain budget, source-request and value identities so the reference uses the exact evaluated source cache. -/
structure Evaluation (request :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest prepared target
  areaTarget floor)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth readingIndex :
      Nat) where
  /-- The actual evaluation of the original connected cap request. -/ cap :
    Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest.Evaluation request.request sample depth
    readingIndex
  /-- The reference built from the exact original evaluated cap source request. -/ reference :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference compared.entered ((target / 4) / 4)
  /-- The reference uses the exact original retained fragment budget. -/ budget_eq : reference.budget = request.budget
  /-- The reference retains the same original source request as the cap evaluation. -/ source_eq : reference.request =
    cap.separated.compared.source
  /-- The reference value equals the actual original evaluated source total. -/ value_eq : reference.value =
    cap.separated.left.total

constructive_injectivity Evaluation

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  in
/-- Construct the face reference from an existing cap evaluation's source
request. This is also the entry point for retained chart replacements. -/
@[expose] def evaluateWithCap (request :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest prepared target
  areaTarget floor)
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest.Evaluation request.request sample
      depth readingIndex) :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest.Evaluation
      request sample depth readingIndex :=
  let reference := Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference.ofRequest request.budget
    evaluated.separated.compared.source
    (by rw [evaluated.separated.compared.minimum_eq]; exact Data.Nat.Order.le_max_right _ _)
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct request.positive (by decide)) (by decide))
  ⟨evaluated, reference, rfl, rfl, evaluated.separated.source_total.symm⟩

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  in
/-- Acquire the original connected cap, then consume its retained source
through the shared face-reference constructor. -/
@[expose] def evaluate (request :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest prepared target
  areaTarget floor)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth readingIndex :
      Nat)
    (later : request.index ≤ index) (readingLater : request.readingIndex ≤ readingIndex) :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest.Evaluation
      request sample depth readingIndex :=
  request.evaluateWithCap
    (request.request.evaluate sample depth readingIndex ((Data.Nat.Order.le_max_left _ _).trans later) readingLater)

namespace Evaluation

variable {request :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  prepared target areaTarget floor}

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  in
/-- A magnitude fixed by the retained geometric bank, before either
requested polynomial stage, controls the actual full source total. -/
theorem source_bounded (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest.Evaluation
  request sample depth readingIndex) :
    Data.Gaussian.Norm.Basic.normSq evaluated.cap.separated.left.total ≤ prepared.sourceBound := open Purelib in by
  have bounded := Hyperelliptic.Charts.Reciprocal.Disk.SideEstimates.bounds evaluated.cap.separated.parents
    request.request.separated.parent_le_one
    (Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum_nonnegative
      prepared.path.covers) le_rfl
  rw [prepared.sourceBound_eq, evaluated.cap.separated.left.total_eq, Path.IncrementArea.sum_flatten,
    Data.List.Map.map_map]
  apply Path.IncrementArea.sum_bound_of_length
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum_nonnegative
        prepared.path.covers) (by decide)))
  · intro value member
    obtain ⟨pair, member, equal⟩ := Data.List.Map.mem_map.mp member
    rw [← equal]
    exact (bounded pair member).2.2.1
  · rewrite [Data.List.Map.length_map, evaluated.cap.separated.parents.pairs_length]
    exact Nat.le_refl _

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  in
/-- The original corner reading differs from its exact retained source reference by less than one sixteenth of the
target. -/
theorem corner_source_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest.Evaluation
  request sample depth readingIndex)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      compared.domains = domains.atRoute placement.location)
    {faceIndex : Nat} (later : request.budget.grid.index ≤ faceIndex) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement placement.location - evaluated.cap.separated.left.total) <
      (target / 4) / 4 := by
  have referenceLater : evaluated.reference.budget.grid.index ≤ faceIndex := by rw [evaluated.budget_eq]; exact later
  have accurate := Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences.reference_accurate compared aligned
    evaluated.reference referenceLater shared
  rw [evaluated.value_eq] at accurate
  exact accurate

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  in
/-- The original corner reading and retained cap total differ by less than the scalar target. -/
theorem corner_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest.Evaluation
  request sample depth readingIndex)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      compared.domains = domains.atRoute placement.location)
    {faceIndex : Nat} (later : request.budget.grid.index ≤ faceIndex) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement placement.location - evaluated.cap.cap.total) < target :=
      by
  have faceError := evaluated.corner_source_error aligned later shared
  have quarterPositive := Fraction.Order.Field.div_pos_direct request.positive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  have paid := Fraction.Order.Arithmetic.add_lt_add_direct
    (faceError.trans (Rat.Bounds.Quarter.quarter_lt_self quarterPositive)) evaluated.cap.total_close
  exact (Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2) paid).trans_eq (by
      rw [show 2 * (target / 4 + target / 4) = target / 4 * 4 by ring1]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  in
/-- The oriented triangle edge is the occurrence used by sewing. -/
theorem triangle_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest.Evaluation
  request sample depth readingIndex)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      compared.domains = domains.atRoute placement.location)
    {faceIndex : Nat} (later : request.budget.grid.index ≤ faceIndex) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (placement.location.sourceEdge.increment readings.values -
      evaluated.cap.cap.total) < target := by
  rw [readings.route_increment]
  exact evaluated.corner_error aligned later shared

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  in
/-- Passing from the actual triangle edge to the full cap trace retains
its internal area. The displayed correction cannot be discarded merely
because the edge increments are close. The anchor may include sewing offsets. -/
theorem triangle_area_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest.Evaluation
  request sample depth readingIndex)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      compared.domains = domains.atRoute placement.location)
    {faceIndex : Nat} (later : request.budget.grid.index ≤ faceIndex) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) (anchor :
      Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Path.BoundaryRibbon.area anchor (anchor +
      placement.location.sourceEdge.increment readings.values) + evaluated.cap.cap.area -
      Path.IncrementArea.traceArea anchor (evaluated.cap.blocks.map (fun block => block.1 :: block.2)).flatten) ≤
        4 * Data.Gaussian.Norm.Basic.normSq anchor * target := by
  rw [Path.IncrementArea.traceArea_eq, ← evaluated.cap.cap.area_eq, ← evaluated.cap.cap.total_eq]
  have identity : Path.BoundaryRibbon.area anchor (anchor + placement.location.sourceEdge.increment readings.values) +
    evaluated.cap.cap.area -
      (evaluated.cap.cap.area + Path.BoundaryRibbon.area anchor evaluated.cap.cap.total) =
      Path.BoundaryRibbon.area anchor (placement.location.sourceEdge.increment readings.values -
        evaluated.cap.cap.total) := by
    apply Gaussian.Basic.ext <;> simp only [Path.BoundaryRibbon.area, Data.Gaussian.Basic.conj,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im, -eq_self, -iff_self] <;> ring1
  rw [identity]
  exact (Path.BoundaryRibbon.area_bound _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (evaluated.triangle_error aligned later readings).le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Gaussian.Norm.Basic.normSq_nonneg anchor)))

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest
  in
/-- Full source and connected cap traces include the same supplied origin.
The final endpoint discrepancy is paid without normalizing that origin. -/
theorem translated_area_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedCapRequest.Evaluation
  request sample depth readingIndex) (anchor : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.traceArea anchor (evaluated.cap.separated.parents.pairs.map
      Prod.fst).flatten -
      Path.IncrementArea.traceArea anchor (evaluated.cap.blocks.map (fun block => block.1 :: block.2)).flatten) <
        2 * (areaTarget + 4 * Data.Gaussian.Norm.Basic.normSq anchor * (target / 4)) := evaluated.cap.trace_error
          anchor

end Evaluation
end RamifiedCapRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
