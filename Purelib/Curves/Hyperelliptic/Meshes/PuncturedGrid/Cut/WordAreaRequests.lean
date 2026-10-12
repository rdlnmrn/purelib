module
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordErrors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryContactSources
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Cut.WordErrors
import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests
public import Purelib.Topology.Surface.Cut.WordAreaBounds
public import Purelib.Topology.Surface.Boundary.NormalFormArea
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests

open Purelib.Data.List

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.NormalFormArea.CutBoundaryWord

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Cut.WordAreaBounds

open Purelib.Topology.Surface.Cut.WordAreaBounds.CutBoundaryWord

open Purelib.Topology.Surface.Cut.WordAreaBounds.PrimitivePoint

open Purelib.Topology.Surface.Cut.WordErrors

open Purelib.Topology.Surface.Cut.WordErrors.CutBoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Word

public section

/-!
# Automatic full word-area precision on the shared period surface

One fixed boundary magnitude pays both products in every word correction.
The existing word request then pays all prefix and full-sum count factors.
The resulting comparison keeps the physical-boundary matrix explicit; it
does not identify the computed handles with a standard homology basis.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Topology.Surface.Boundary.BoundaryContactSources (paired_boundary_members)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid (BoundaryProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts (BoundaryContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences (BoundaryReference)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks (FaceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison (PrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgramBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutChordPrograms)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies (PrimitiveFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily (Requested)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests (WordBudget)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing (boundaryWord boundaryWord_provenance)
open Purelib.Topology.Surface.Sewing.CenteredSewnSamples (Centered)
open _root_.Purelib.Topology.Surface.Boundary (NormalFormArea)
open Purelib.Topology.Surface.Cut.WordAreaBounds.CutWordArea (areaWeight areaWeight_nonnegative)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutWordEntry)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded bounded_of_conjugate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)
open _root_.Purelib.LinearAlgebra.Alternating (NormalForm)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus} {boundary :
    BoundaryProgram lifted
    source}
  {segments : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period}
    {differential : Fin genus}
  {comparison : PrimitiveBank
    (FaceBank.ofSegments boundary.program segments)
    differential}
  {pairing : ProjectedEdgePairing
    lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.boundary}
  {count : Nat} {programs : Data.Vector
    (CutCycleProgram lifted source) count}

set_option genInjectivity false in
/-- A computed positive area request for the complete original boundary word.

The retained boundary magnitude and word count pay every correction product; the actual period and contact requests
share one cached minimum stage. -/
structure WordAreaBudget (family : PeriodFamilies.PrimitiveFamily programs comparison.domains differential)
    (prepared : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch pairing
      (PeriodMatrix.standardDifferential differential) comparison.domains)
    (reference : BoundaryPrimitiveReferences.BoundaryReference boundary comparison prepared.prepared)
    (lengthBound : Nat) (pathTarget areaTarget : InverseRootPolynomial.Coordinate) (targets : Data.Vector
      InverseRootPolynomial.Coordinate count) (floor : Nat) where
  /-- The requested complete word-area target is strictly positive. -/ positive : 0 < areaTarget
  /-- The cached correction weight from the original boundary magnitude and complete word count. -/ weight :
    InverseRootPolynomial.Coordinate
  /-- The retained correction weight is the exact original word-area weight. -/ weight_eq : weight =
    CutWordArea.areaWeight reference.bound boundary.count
  /-- The cached positive word-error target allocated from the original area target. -/ wordTarget :
    InverseRootPolynomial.Coordinate
  /-- The word-error target is the weighted allowance for the retained correction scale. -/ wordTarget_eq : wordTarget =
    Weighted.allowance areaTarget weight
  /-- The cached stage floor shared by the original reference and word request. -/ minimum : Nat
  /-- The retained minimum is the maximum of the supplied floor and original reference contact stage. -/ minimum_eq :
    minimum = max floor reference.reference.contactRequest.index
  /-- The actual original word request paying the retained positive correction allowance. -/ word :
    WordRequests.WordBudget family prepared lengthBound pathTarget wordTarget targets minimum

constructive_injectivity WordAreaBudget

namespace WordAreaBudget

variable {family : PrimitiveFamily programs
  comparison.domains differential}
  {prepared : BoundaryContactPreparations
    lifted.cutPolygon.patch pairing (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential)
    comparison.domains}
  {reference : BoundaryReference boundary
    comparison prepared.prepared}
  {lengthBound : Nat} {pathTarget areaTarget : Coordinate} {targets
    : Data.Vector Coordinate count} {floor :
    Nat}

/-- Compute the original boundary correction weight and common reference stage, then prepare the exact retained word
request. -/
@[expose] def build (family : PeriodFamilies.PrimitiveFamily programs comparison.domains differential)
    (prepared : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch pairing
      (PeriodMatrix.standardDifferential differential) comparison.domains)
    (reference : BoundaryPrimitiveReferences.BoundaryReference boundary comparison prepared.prepared)
    (lengthBound : Nat) (pathTarget : InverseRootPolynomial.Coordinate) (pathPositive : 0 < pathTarget)
    (areaTarget : InverseRootPolynomial.Coordinate) (areaPositive : 0 < areaTarget)
    (targets : Data.Vector InverseRootPolynomial.Coordinate count) (positive : ∀ index, 0 < targets index)
      (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family prepared reference lengthBound
      pathTarget areaTarget targets floor :=
  let weight := CutWordArea.areaWeight reference.bound boundary.count
  let wordTarget := Weighted.allowance areaTarget weight
  have wordPositive := Weighted.allowance_positive areaPositive
    (CutWordArea.areaWeight_nonnegative reference.bound_positive.le boundary.count)
  let minimum := max floor reference.reference.contactRequest.index
  ⟨areaPositive, weight, rfl, wordTarget, rfl, minimum, rfl,
    WordBudget.build family prepared boundary.count boundary.count_eq
      lengthBound pathTarget pathPositive wordTarget wordPositive targets positive minimum⟩

/-- The actual word-period stage pays the original boundary reference contact request. -/
theorem reference_later (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family
  prepared reference lengthBound pathTarget areaTarget targets floor) :
    reference.reference.contactRequest.index ≤ budget.word.request.periods.index := by
  have floorLe : reference.reference.contactRequest.index ≤ budget.minimum := by
    rw [budget.minimum_eq]
    exact Data.Nat.Order.le_max_right _ _
  exact floorLe.trans budget.word.floor_le

/-- The actual word-period stage retains the supplied original minimum floor. -/
theorem floor_le (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family prepared
  reference lengthBound pathTarget areaTarget targets floor) :
    floor ≤ budget.word.request.periods.index := by
  have floorLe : floor ≤ budget.minimum := by rw [budget.minimum_eq]; exact Data.Nat.Order.le_max_left _ _
  exact floorLe.trans budget.word.floor_le

/-- The retained per-pair allowance equals the original weighted area allocation at the complete word count. -/
theorem perPair_eq (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family
  prepared reference lengthBound pathTarget areaTarget targets floor) :
    budget.word.request.perPair = Aggregate.perTerm
      (Weighted.allowance areaTarget
        (CutWordArea.areaWeight reference.bound lifted.cutPolygon.patch.cut.boundary.length))
          lifted.cutPolygon.patch.cut.boundary.length := by
  have targetEq := budget.wordTarget_eq.trans
    (congrArg (Weighted.allowance areaTarget)
      (budget.weight_eq.trans (congrArg (CutWordArea.areaWeight reference.bound) boundary.count_eq)))
  exact budget.word.perPair_eq.trans (congrArg
    (fun amount => Aggregate.perTerm amount lifted.cutPolygon.patch.cut.boundary.length) targetEq)

/-- The original complete closed-word correction satisfies the requested area target using the retained boundary
magnitude and contact estimates. -/
theorem correction_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget
  family prepared reference lengthBound pathTarget areaTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested
      budget.word.request.periods minimumStages}
    (sample : Requested.Sewn requested lifted.cutPolygon.patch) (centered : CenteredSewnSamples.Centered sample.surface)
    (wordSample : CutBoundaryWord.AreaSample (ProjectedEdgePairing.boundaryWord pairing) centered.energyValues
      (centered.energyValues lifted.cutPolygon.patch.cut.anchor)) :
    Data.Gaussian.Norm.Basic.normSq wordSample.closedCorrection < areaTarget := by
  have endpoints (edge : Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count) (member : edge ∈
    lifted.cutPolygon.patch.cut.boundary) :
      PrimitivePoint.Bounded (centered.energyValues edge.start) reference.bound ∧ PrimitivePoint.Bounded
        (centered.energyValues edge.finish) reference.bound := by
    constructor
    · apply PrimitivePoint.bounded_of_conjugate (centered.conjugate _)
      rw [centered.right_eq, centered.primitives_eq]
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        reference.start_bounded budget.reference_later sample.triangles sample.surface edge member
    · apply PrimitivePoint.bounded_of_conjugate (centered.conjugate _)
      rw [centered.right_eq, centered.primitives_eq]
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        reference.finish_bounded budget.reference_later sample.triangles sample.surface edge member
  have entryMember (entry : BoundaryWord.CutWordEntry lifted.cutPolygon.patch.cut.vertexLabels
    (ProjectedEdgePairing.boundaryWord pairing).alphabet.generators)
      (member : entry ∈ (ProjectedEdgePairing.boundaryWord pairing).alphabet.entries) : entry.edge ∈
        lifted.cutPolygon.patch.cut.boundary := by
    exact (congrArg (fun edges => entry.edge ∈ edges) (ProjectedEdgePairing.boundaryWord pairing).alphabet.edges_eq).mp
      (Map.mem_map_of_mem member)
  rw [AreaSample.closedCorrection_eq_of_centered wordSample centered.anchor_eq_zero]
  apply AreaSample.correction_accurate wordSample lifted.cutPolygon.patch.cut.closed budget.positive
    reference.bound_positive.le
  · have bounded := WordErrors.word_errors_bounded budget.word.request sample centered wordSample
    rw [budget.perPair_eq] at bounded
    exact bounded
  · intro entry member
    rw [SignedGenerator.linear_eq,
      AreaSample.values_apply]
    have provenance := ProjectedEdgePairing.boundaryWord_provenance pairing entry member
    unfold CutWordEntry.PairProvenance at provenance
    split at provenance
    · rename_i reversed
      rw [if_pos reversed]
      obtain ⟨pair, pairMember, generatorEq, _⟩ := provenance
      rw [generatorEq]
      have bounded := endpoints pair.first (BoundaryContactSources.paired_boundary_members pairing pair pairMember).1
      exact Bounded.neg
        (Bounded.sub bounded.2 bounded.1)
    · rename_i forward
      rw [if_neg forward, ← provenance]
      have bounded := endpoints entry.edge (entryMember entry member)
      exact Bounded.sub bounded.2 bounded.1
  · intro entry member
    exact (endpoints entry.edge (entryMember entry member)).1

/-- The target concerns the actual cached surface boundary and its entire computed matrix, with no caller-supplied drift
or magnitude inequalities. -/
theorem boundary_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family
  prepared reference lengthBound pathTarget areaTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested
      budget.word.request.periods minimumStages}
    (sample : Requested.Sewn requested lifted.cutPolygon.patch) (centered : CenteredSewnSamples.Centered sample.surface)
    (wordSample : CutBoundaryWord.AreaSample (ProjectedEdgePairing.boundaryWord pairing) centered.energyValues
      (centered.energyValues lifted.cutPolygon.patch.cut.anchor)) :
    Data.Gaussian.Norm.Basic.normSq (sample.surface.boundaryArea -
      Pairing.contract (fun row column => (ProjectedEdgePairing.boundaryWord pairing).signature.matrix row column)
        wordSample.values) < areaTarget := by
  rw [← centered.boundary_area, wordSample.closed_area_eq lifted.cutPolygon.patch.cut.closed]
  have cancel : Pairing.contract (fun row column => (ProjectedEdgePairing.boundaryWord pairing).signature.matrix row
    column) wordSample.values + wordSample.closedCorrection -
      Pairing.contract (fun row column => (ProjectedEdgePairing.boundaryWord pairing).signature.matrix row column)
        wordSample.values = wordSample.closedCorrection :=
    Algebra.Group.add_sub_cancel_left _ _
  rw [cancel]
  exact budget.correction_accurate sample centered wordSample

/-- Normalizing the paired block removes only the now-paid compatibility correction. The one-sided and mixed
physical-boundary matrix remains. -/
theorem handles_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family
  prepared reference lengthBound pathTarget areaTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested
      budget.word.request.periods minimumStages}
    (sample : Requested.Sewn requested lifted.cutPolygon.patch) (centered : CenteredSewnSamples.Centered sample.surface)
    (wordSample : CutBoundaryWord.AreaSample (ProjectedEdgePairing.boundaryWord pairing) centered.energyValues
      (centered.energyValues lifted.cutPolygon.patch.cut.anchor))
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord (ProjectedEdgePairing.boundaryWord pairing)) {raw
      : List
      (Handle.Basic.PivotIndices (ProjectedEdgePairing.boundaryWord pairing).alphabet.count)}
    (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw) (evaluated :
      Topology.Surface.Boundary.NormalFormArea normal
      wordSample.values) :
    Data.Gaussian.Norm.Basic.normSq (sample.surface.boundaryArea - (2 * evaluated.area +
      Pairing.contract (fun row column => integral.remaining row column) wordSample.values)) < areaTarget := by
  rw [← centered.boundary_area, AreaSample.closed_handle_area_eq wordSample integral normal evaluated
    lifted.cutPolygon.patch.cut.closed]
  have cancel : (2 * evaluated.area + Pairing.contract (fun row column => integral.remaining row column)
    wordSample.values) + wordSample.closedCorrection -
      (2 * evaluated.area + Pairing.contract (fun row column => integral.remaining row column) wordSample.values) =
        wordSample.closedCorrection :=
    Algebra.Group.add_sub_cancel_left _ _
  rw [cancel]
  exact budget.correction_accurate sample centered wordSample

end WordAreaBudget
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests
