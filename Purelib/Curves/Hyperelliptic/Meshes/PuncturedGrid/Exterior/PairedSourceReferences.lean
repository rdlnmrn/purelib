module
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularPointReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PointReferences
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonBlockArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes

public section

/-! The paired cap evaluation supplies both references to the actual shared
face bank. Both fragment budgets are selected before the source primitives. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceOccurrence)
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences (Reference)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- The fragment-accuracy allocation for the original occurrence's first source primitive at one quarter of the target.
-/
@[expose] def SourceBudget (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (target : Normalization.InverseRootPolynomial.Coordinate) :=
  Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy occurrence.compared.entered.globalBounds
    occurrence.compared.entered.domain.steps
    occurrence.compared.entered.mesh.splits.pieceCount (target / 4)

/-- The corresponding quarter-target fragment allocation for the same retained occurrence with its differential recast.
-/
@[expose] def OtherSourceBudget (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (target : Normalization.InverseRootPolynomial.Coordinate) :=
  Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy (occurrence.recastComparison other).entered.globalBounds
    (occurrence.recastComparison other).entered.domain.steps
    (occurrence.recastComparison other).entered.mesh.splits.pieceCount (target / 4)

set_option genInjectivity false in
/-- Two source-fragment allocations and a paired parent request on one original exterior occurrence.

The cached stage floor pays both retained fragment bounds before acquiring the two source primitive banks. -/
structure PairedSourcePlan (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (other : Hyperelliptic.Differentials.Basic.Differential genus) (target :
      Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The complete paired source-reference target is strictly positive. -/ positive : 0 < target
  /-- The retained first-differential source-fragment budget. -/ first :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.SourceBudget occurrence target
  /-- The retained recast second-differential source-fragment budget. -/ second :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.OtherSourceBudget occurrence other target
  /-- The cached common floor for both original fragment budgets and the requested minimum. -/ floor : Nat
  /-- The common floor is exactly the maximum of the supplied minimum and the two fragment thresholds. -/ floor_eq :
    floor = max minimum (max first.minimumIndex second.minimumIndex)
  /-- The quarter-target paired parent request on the occurrence's original cached parent list. -/ parents :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
    occurrence.compared.entered.cache.parents (target / 4) floor

constructive_injectivity PairedSourcePlan

namespace PairedSourcePlan
variable {occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Allocate both source-fragment budgets and prepare the original paired parent request at their common floor. -/
@[expose] def build (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (occurrence :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    (other : Hyperelliptic.Differentials.Basic.Differential genus) (target :
      Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (minimum : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target minimum
      := open Purelib.Data.Rat in by
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  let first : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.SourceBudget occurrence target :=
    Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy.build _ _ _ (target / 4) quarterPositive
  let second : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.OtherSourceBudget occurrence other
    target := Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy.build _ _ _ (target / 4) quarterPositive
  let floor := max minimum (max first.minimumIndex second.minimumIndex)
  exact ⟨positive, first, second, floor, rfl,
    occurrence.pairedAreaRequest prepared member other (target / 4) quarterPositive floor⟩

/-- The common stage threshold for the original parent request and both retained grid budgets. -/
@[expose] def index (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  occurrence other target minimum) : Nat :=
  max plan.parents.index (max plan.first.grid.index plan.second.grid.index)

variable {stage fine : Nat} {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence
    other target minimum}

/-- The exact paired parent evaluation retained by this source plan on the supplied two cap samples. -/
@[expose] def ParentEvaluation (plan :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (fine : Nat) :=
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation plan.parents sample otherSample fine

set_option genInjectivity false in
/-- Two primitive references read from one retained paired parent evaluation.

Their budgets equal the original source plan's two allocations, and their values equal the two cached source-summary
totals from that same evaluation. -/
structure Sources (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine) where
  /-- The first original primitive reference at the complete source target. -/ first :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference occurrence.compared.entered target
  /-- The corresponding reference for the recast second differential. -/ second :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference (occurrence.recastComparison other).entered
    target
  /-- The first reference retains the exact original first-fragment budget. -/ first_budget : first.budget = plan.first
  /-- The second reference retains the exact original second-fragment budget. -/ second_budget : second.budget =
    plan.second
  /-- The first reference value is the sum of the retained paired source summaries' left totals. -/ first_value :
    first.value = Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (evaluated.retained.map (fun entry => entry.certified.compared.firstSummary.totalValue.left))
  /-- The second reference value is the sum of the same paired source summaries' right totals. -/ second_value :
    second.value = Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (evaluated.retained.map (fun entry => entry.certified.compared.firstSummary.totalValue.right))

constructive_injectivity Sources

/-- No primitive or parent preparation is repeated: the references consume
the source sums certified by this exact paired-area evaluation. -/
@[expose] def sources (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.Sources
  evaluated := by
  let first := Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.sourceRequest evaluated
  let second := Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.otherSourceRequest evaluated
  have firstLater : plan.first.minimumIndex ≤ first.val.minimumIndex := by
    rw [first.property.2, plan.floor_eq]
    exact (Data.Nat.Order.le_max_left ..).trans (Data.Nat.Order.le_max_right ..)
  have secondLater : plan.second.minimumIndex ≤ second.val.minimumIndex := by
    rw [second.property.2, plan.floor_eq]
    exact (Data.Nat.Order.le_max_right ..).trans (Data.Nat.Order.le_max_right ..)
  exact ⟨Reference.ofRequest plan.first first.val firstLater plan.positive,
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference.ofRequest plan.second second.val secondLater
      plan.positive, rfl, rfl,
    first.property.1, second.property.1⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
/-- The shared first-differential edge reading is within the target of the same cached paired source total. -/
theorem Sources.first_accurate {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine}
    (sources : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.Sources evaluated)
      {faceIndex : Nat} (later : plan.index ≤ faceIndex)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement occurrence.placement.location -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (evaluated.retained.map (fun entry => entry.certified.compared.firstSummary.totalValue.left))) < target := by
  have after : sources.first.budget.grid.index ≤ faceIndex := by
    rw [sources.first_budget]
    exact ((Data.Nat.Order.le_max_left ..).trans (Data.Nat.Order.le_max_right ..)).trans later
  have accurate := Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences.reference_accurate
    occurrence.compared occurrence.aligned sources.first after shared
  rw [sources.first_value] at accurate
  exact accurate

/-- The shared recast second-differential edge reading is within the target of its cached paired source total. -/
theorem Sources.second_accurate {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine}
    (sources : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.Sources evaluated)
      {faceIndex : Nat} (later : plan.index ≤ faceIndex)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other faceIndex domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement occurrence.placement.location -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (evaluated.retained.map (fun entry => entry.certified.compared.firstSummary.totalValue.right))) < target := by
  have after : sources.second.budget.grid.index ≤ faceIndex := by
    rw [sources.second_budget]
    exact ((Data.Nat.Order.le_max_right ..).trans (Data.Nat.Order.le_max_right ..)).trans later
  have accurate := Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences.reference_accurate
    (occurrence.recastComparison other) (occurrence.recastComparison_aligned other) sources.second after shared
  rw [sources.second_value] at accurate
  exact accurate

/-- Fine trace endpoints may use different retained grid owners. Their
ownership error is paid before comparison with the cached source total. -/
theorem Sources.first_points_accurate {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine}
    (sources : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.Sources evaluated)
      {faceIndex : Nat} (later : plan.index ≤ faceIndex)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives occurrence.compared.entered.domain
      differential faceIndex)
    {count : Nat} {points : Fin count → Normalization.InverseRootPolynomial.Gaussian}
    (readings : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (first last : Fin count) (firstEq : points first = occurrence.start) (lastEq : points last = occurrence.finish) :
    Data.Gaussian.Norm.Basic.normSq ((readings.values last - readings.values first) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (evaluated.retained.map (fun entry => entry.certified.compared.firstSummary.totalValue.left))) < target := by
  have after : sources.first.budget.grid.index ≤ faceIndex := by
    rw [sources.first_budget]
    exact ((Data.Nat.Order.le_max_left ..).trans (Data.Nat.Order.le_max_right ..)).trans later
  have accurate := Hyperelliptic.Meshes.PuncturedGrid.Face.PointReferences.point_accurate
    sources.first after data readings first last firstEq lastEq
  rw [sources.first_value] at accurate
  exact accurate

/-- The second-differential endpoint reading difference meets the original target against its cached paired source
total.

The supplied points retain their actual grid owners; the shared late budget pays their ownership error before the source
comparison. -/
theorem Sources.second_points_accurate {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine}
    (sources : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.Sources evaluated)
      {faceIndex : Nat} (later : plan.index ≤ faceIndex)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives (occurrence.recastComparison
      other).entered.domain other faceIndex)
    {count : Nat} {points : Fin count → Normalization.InverseRootPolynomial.Gaussian}
    (readings : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (first last : Fin count) (firstEq : points first = occurrence.start) (lastEq : points last = occurrence.finish) :
    Data.Gaussian.Norm.Basic.normSq ((readings.values last - readings.values first) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (evaluated.retained.map (fun entry => entry.certified.compared.firstSummary.totalValue.right))) < target := by
  have after : sources.second.budget.grid.index ≤ faceIndex := by
    rw [sources.second_budget]
    exact ((Data.Nat.Order.le_max_right ..).trans (Data.Nat.Order.le_max_right ..)).trans later
  have accurate := Hyperelliptic.Meshes.PuncturedGrid.Face.PointReferences.point_accurate
    sources.second after data readings first last firstEq lastEq
  rw [sources.second_value] at accurate
  exact accurate

end PairedSourcePlan
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
