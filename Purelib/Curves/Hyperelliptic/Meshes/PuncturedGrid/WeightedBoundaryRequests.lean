module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Surface.Boundary.BoundaryContactErrors
import Purelib.Topology.Surface.Boundary.BoundaryContactSources
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
public import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Approximation.Budget.WeightedDefectBudget
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra

open Purelib.Data.Nat

open Purelib.Approximation.Budget.WeightedDefectBudget.ProjectedEdgePairing

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-!
# Requested weighted cut-boundary errors on the actual period surface

A fixed coarse boundary reference determines the endpoint magnitude before
the fine contact and period requests. Both phases reuse the same combined
contact preparation. Every period uses one shared sewn surface, whose
centered paired-defect sum is paid without discarding the physical boundary.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedBoundaryRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid (BoundaryProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences (BoundaryReference)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts (BoundaryContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks (FaceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison (PrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies (PrimitiveFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily (Requested)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests (ContactBudget)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryContactSources)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.CenteredSewnSamples (Centered)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

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
/-- A paid weighted cut-boundary defect request on the original common period surface.

The original coarse boundary magnitude determines the weight before the shared fine contact and period stages are
chosen. -/
structure AreaBudget (family : PeriodFamilies.PrimitiveFamily programs comparison.domains differential)
    (prepared : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch pairing
      (PeriodMatrix.standardDifferential differential) comparison.domains)
    (reference : BoundaryPrimitiveReferences.BoundaryReference boundary comparison prepared.prepared)
    (lengthBound : Nat) (pathTarget areaTarget : PreparedPrimitiveChargeBounds.Coordinate) (targets :
      Data.Vector PreparedPrimitiveChargeBounds.Coordinate count) (floor : Nat) where
  /-- The requested weighted area-error target is strictly positive. -/ positive : 0 < areaTarget
  /-- The cached weight determined by the original coarse boundary reference. -/ weight :
    PreparedPrimitiveChargeBounds.Coordinate
  /-- The cached weight is exactly four times the original reference magnitude bound. -/ weight_eq : weight = 4 *
    reference.bound
  /-- The cached unweighted endpoint-error allowance paying the original area target. -/ endpointTarget :
    PreparedPrimitiveChargeBounds.Coordinate
  /-- The endpoint allowance is exactly the weighted budget allocation at the retained reference weight. -/
    endpointTarget_eq : endpointTarget = Weighted.allowance areaTarget weight
  /-- The cached common lower stage for the fine contact and period requests. -/ minimum : Nat
  /-- The retained minimum is exactly the maximum of the caller floor and original reference stage. -/ minimum_eq :
    minimum = max floor reference.reference.contactRequest.index
  /-- The retained common contact and period budget paying these exact original targets and stage floor. -/ request :
    ContactPeriodRequests.ContactBudget family prepared lengthBound pathTarget endpointTarget targets minimum

constructive_injectivity AreaBudget

namespace AreaBudget

variable {family : PrimitiveFamily programs
  comparison.domains differential}
  {prepared : BoundaryContactPreparations
    lifted.cutPolygon.patch pairing (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential)
    comparison.domains}
  {reference : BoundaryReference boundary
    comparison prepared.prepared}
  {lengthBound : Nat} {pathTarget areaTarget : Coordinate}
    {targets : Data.Vector Coordinate count}
    {floor : Nat}

/-- Use the original coarse boundary reference to allocate the weighted defect target and prepare the shared fine
contact and period requests. -/
def build (family : PeriodFamilies.PrimitiveFamily programs comparison.domains differential)
    (prepared : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch pairing
      (PeriodMatrix.standardDifferential differential) comparison.domains)
    (reference : BoundaryPrimitiveReferences.BoundaryReference boundary comparison prepared.prepared)
    (lengthBound : Nat) (pathTarget : PreparedPrimitiveChargeBounds.Coordinate) (pathPositive : 0 < pathTarget)
    (areaTarget : PreparedPrimitiveChargeBounds.Coordinate) (areaPositive : 0 < areaTarget)
    (targets : Data.Vector PreparedPrimitiveChargeBounds.Coordinate count) (positive : ∀ index, 0 < targets
      index) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedBoundaryRequests.AreaBudget family prepared reference lengthBound
      pathTarget areaTarget targets floor :=
  let weight := 4 * reference.bound
  let endpointTarget := Weighted.allowance areaTarget weight
  have endpointPositive := Weighted.allowance_positive areaPositive
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : PreparedPrimitiveChargeBounds.Coordinate) ≤ 4)
      reference.bound_positive.le)
  let minimum := max floor reference.reference.contactRequest.index
  ⟨areaPositive, weight, rfl, endpointTarget, rfl, minimum, rfl,
    ContactBudget.build family prepared lengthBound pathTarget pathPositive endpointTarget endpointPositive targets
      positive minimum⟩

/-- The retained period request stage also pays the original coarse boundary reference. -/
theorem reference_later (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedBoundaryRequests.AreaBudget family
  prepared reference lengthBound pathTarget areaTarget targets floor) :
    reference.reference.contactRequest.index ≤ budget.request.periods.index := by
  have floorLe : reference.reference.contactRequest.index ≤ budget.minimum := by
    rw [budget.minimum_eq]
    exact Order.le_max_right _ _
  exact floorLe.trans (budget.request.contacts.floor_le.trans budget.request.periods.surface_later)

/-- The retained period request stage meets the original caller floor. -/
theorem floor_le (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedBoundaryRequests.AreaBudget family prepared
  reference lengthBound pathTarget areaTarget targets floor) :
    floor ≤ budget.request.periods.index := by
  have floorLe : floor ≤ budget.minimum := by rw [budget.minimum_eq]; exact Order.le_max_left _ _
  exact floorLe.trans (budget.request.contacts.floor_le.trans budget.request.periods.surface_later)

/-- Each actual paired boundary defect receives exactly the count allocation of the original weighted endpoint
allowance. -/
theorem perPair_eq (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedBoundaryRequests.AreaBudget family
  prepared reference lengthBound pathTarget areaTarget targets floor) :
    budget.request.perPair = Aggregate.perTerm
      (Weighted.allowance areaTarget (4 * reference.bound)) budget.request.pairCount :=
  budget.request.perPair_eq.trans
    ((congrArg (fun amount => Aggregate.perTerm amount budget.request.pairCount) budget.endpointTarget_eq).trans
      (congrArg (fun weight => Aggregate.perTerm (Weighted.allowance areaTarget weight)
        budget.request.pairCount) budget.weight_eq))

/-- Every actual retained centered boundary-pair defect satisfies its original per-pair allowance. -/
theorem centered_defect_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedBoundaryRequests.AreaBudget
  family prepared reference lengthBound pathTarget areaTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.request.periods
      minimumStages}
    (sample : Requested.Sewn requested lifted.cutPolygon.patch) (centered : CenteredSewnSamples.Centered sample.surface)
    (data : ProjectedEdgePairing.PrimitiveSample pairing centered.energyValues)
    (entry : ProjectedEdgePair.Sample (labels := lifted.cutPolygon.patch.cut.vertexLabels) centered.energyValues)
    (member : entry ∈ data.samples) : Data.Gaussian.Norm.Basic.normSq entry.defect.right <
      budget.request.perPair := by
  rw [centered.defect_normSq]
  have pairMember : entry.pair ∈ pairing.pairs := by rw [← data.pairs_eq]; exact Map.mem_map_of_mem member
  rcases List.mem_iff_getElem.mp pairMember with ⟨position, bound, equal⟩
  have accurate := budget.request.boundary_accurate sample ⟨position, bound⟩
  unfold BoundaryContactErrors.BoundaryContactSources.mismatch at accurate
  simpa only [equal] using accurate

/-- This is the weighted area defect from the complete boundary identity, not merely a sum of endpoint differences. The
coarse magnitude and both pair-count factors are paid before constructing the shared fine sample. -/
theorem defectSum_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedBoundaryRequests.AreaBudget
  family prepared reference lengthBound pathTarget areaTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.request.periods
      minimumStages}
    (sample : Requested.Sewn requested lifted.cutPolygon.patch) (centered : CenteredSewnSamples.Centered sample.surface)
    (data : ProjectedEdgePairing.PrimitiveSample pairing centered.energyValues) :
      Data.Gaussian.Norm.Basic.normSq data.defectSum < areaTarget := by
  have countEq : data.samples.length = budget.request.pairCount := by
    have equal := congrArg List.length data.pairs_eq
    rw [Map.length_map] at equal
    exact equal.trans budget.request.pairCount_eq.symm
  apply PrimitiveSample.defectSum_accurate data budget.positive reference.bound_positive.le budget.request.pairCount
    countEq
  · intro entry member
    apply PrimitivePoint.bounded_of_conjugate (ProjectedEdgePair.Sample.defect_conjugate entry centered.conjugate)
    have accurate := (budget.centered_defect_accurate sample centered data entry member).le
    rw [budget.perPair_eq] at accurate
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using accurate
  · intro entry member
    apply PrimitivePoint.bounded_of_conjugate (centered.conjugate _)
    rw [centered.right_eq, centered.primitives_eq]
    have pairMember : entry.pair ∈ pairing.pairs := by rw [← data.pairs_eq]; exact Map.mem_map_of_mem member
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
      reference.finish_bounded budget.reference_later sample.triangles sample.surface entry.pair.second
        (BoundaryContactSources.paired_boundary_members pairing entry.pair pairMember).2

/-- Only the now-paid compatibility defect is removed up to the requested error. Genuine physical-boundary area and the
actual jump sum remain. -/
theorem boundary_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedBoundaryRequests.AreaBudget family
  prepared reference lengthBound pathTarget areaTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.request.periods
      minimumStages}
    (sample : Requested.Sewn requested lifted.cutPolygon.patch) (centered : CenteredSewnSamples.Centered sample.surface)
    (data : ProjectedEdgePairing.PrimitiveSample pairing centered.energyValues) :
    Data.Gaussian.Norm.Basic.normSq (sample.surface.boundaryArea - (data.boundaryArea + data.jumpSum)) <
      areaTarget := by
  rw [centered.boundary_decomposition data, Group.add_sub_cancel_left]
  exact budget.defectSum_accurate sample centered data

end AreaBudget
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedBoundaryRequests
