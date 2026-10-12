module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Decide
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration.BasisCommonParentRequest.Plan

open
  Acquisition.Sample

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Compare entire restored parent polygons, retaining the polygon of block totals. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Basis.CommonParentBank (BasisCommonParentBank)
open Basis.CommonParentPlans (Plans NumericalBank Readings)
open Basis.CommonParentSamples (FanPreparations Samples)
open Basis.CommonParentJoins.BasisCommonParentBank (Junctions)
open Basis.CommonPreparedBank.Samples (PreparedComparisons)
open Basis.CommonParentConnection.Samples (firstValues
  restoredPaths)
open Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    UniformBounds regular.padded}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {basis : BasisBounds bounds}
  {allowance coefficientTarget : Coordinate} {coverFloor floor :
    Nat}
  {index minimum readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

open Basis.CommonEnergyPreparation (EnergyPreparation)

variable {stage energyFloor radialDepth : Nat} {coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Samples

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (Summary pathArea)
open
  Basis.CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison
  (restoredTotalBound restored_after_area_bound restored_after_total_bounds)

/-- Read the literal path indexed by a retained cached summary. -/
@[expose] def summaryPath {path : List InverseRootPolynomial.Gaussian} (_ : IncrementArea.Summary path) : List Gaussian
  := path

/-- Pair the prepared child paths with the literal restored chart paths, retaining the original parent order and
incoming direct endpoint. -/
@[expose] def restoredPairs : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) →
    InverseRootPolynomial.Gaussian → List (List InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, .nil, _, _, _, _, _, _, _, _, _ => []
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, previous =>
      (summaryPath
        (PreparedComparison.restoredIntegral comparisons.1 previous), Acquisition.Sample.restoredPath samples.1
        previous) ::
        restoredPairs tail
          sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2 samples.1.endpoints.last.2

/-- Append cached prepared block summaries once, without traversing their fine paths again. The dependent path is the
left side of the retained pairs. -/
@[expose] def preparedSummary : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) →
    (previous : InverseRootPolynomial.Gaussian) → IncrementArea.Summary
      ((restoredPairs anchors
        sources bank plans inputs readings prepared samples comparisons previous).map Prod.fst).flatten
  | _, .nil, _, _, _, _, _, _, _, _, _ => IncrementArea.Summary.build []
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, previous =>
      (PreparedComparison.restoredIntegral comparisons.1 previous).append
        (preparedSummary
          tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2
          samples.1.endpoints.last.2)

/-- The four retained comparison bounds for one original prepared/chart block pair.

The signed area error, total error and both actual totals keep their distinct homogeneous coefficient factors. -/
private def BlockBounds (pair : List InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea pair.2) ≤ 82 * (4 *
    allowance) ^ 2 * (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2 ∧
  Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
    Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ (4 * allowance) ^ 2 *
    PreparedObservationCoercivity.coefficientNormSq coefficients ∧
  Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤
    PreparedComparison.restoredTotalBound (basis := basis) (allowance := allowance) *
    PreparedObservationCoercivity.coefficientNormSq coefficients ∧
  Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤
    PreparedComparison.restoredTotalBound (basis := basis) (allowance := allowance) *
    PreparedObservationCoercivity.coefficientNormSq coefficients

/-- Transport the cached area and total bounds to the exact paths indexed by the original summaries. -/
private theorem bounds_of_summaries {leftPath rightPath : List InverseRootPolynomial.Gaussian} (left :
  IncrementArea.Summary leftPath) (right : IncrementArea.Summary rightPath)
    (area : Data.Gaussian.Norm.Basic.normSq (left.area - right.area) ≤ 82 * (4 * allowance) ^ 2 *
      (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2)
    (total : Data.Gaussian.Norm.Basic.normSq (left.total - right.total) ≤ (4 * allowance) ^ 2 *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    (bounded : Data.Gaussian.Norm.Basic.normSq left.total ≤ PreparedComparison.restoredTotalBound (basis :=
      basis) (allowance := allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients ∧
      Data.Gaussian.Norm.Basic.normSq right.total ≤ PreparedComparison.restoredTotalBound (basis := basis)
        (allowance := allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients) :
    BlockBounds (basis := basis)
      (allowance := allowance) (coefficients := coefficients) (leftPath, rightPath) := by
  change Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea leftPath - IncrementArea.pathArea rightPath) ≤
    _ ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum leftPath -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum rightPath) ≤ _ ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum leftPath) ≤ _ ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum rightPath) ≤ _
  rw [← left.area_eq, ← right.area_eq, ← left.total_eq, ← right.total_eq]
  exact ⟨area, total, bounded⟩

/-- The retained first-block comparison bounds, with the trivial condition for an empty parent bank. -/
private def HeadBounds : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) →
    InverseRootPolynomial.Gaussian → Prop
  | _, .nil, _, _, _, _, _, _, _, _, _ => True
  | _, .cons _ _ _ _, _, _, _, _, _, _, samples, comparisons, previous =>
      BlockBounds (basis := basis)
        (allowance := allowance) (coefficients := coefficients)
        (summaryPath
          (PreparedComparison.restoredIntegral comparisons.1 previous), Acquisition.Sample.restoredPath samples.1
          previous)

/-- Every original restored block satisfies its comparison bounds once the first block and actual junction stages are
paid. -/
private theorem boundsFromHead (branch : HyperellipticReciprocal.originOrder curve = 1) : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) →
    (joins : BasisCommonParentBank.Junctions anchors sources bank) → joins.stage anchors sources bank ≤ stage →
    (previous : InverseRootPolynomial.Gaussian) →
      HeadBounds anchors sources
      bank plans inputs readings prepared samples comparisons previous →
    ∀ pair ∈ restoredPairs anchors
      sources bank plans inputs readings prepared samples comparisons previous,
      BlockBounds (basis := basis)
        (allowance := allowance) (coefficients := coefficients) pair
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, member => False.elim (List.not_mem_nil member)
  | _, .cons _ _ _ .nil, _, _, _, _, _, _, _, _, _, _, _, head, pair, member => by
      rcases List.Membership.mem_cons.mp member with same | empty
      · exact same ▸ head
      · exact False.elim (List.not_mem_nil empty)
  | _, .cons _ _ _ (.cons _ _ _ _), _, bank, plans, inputs, readings, prepared, samples, comparisons, joins, later, _,
    head, pair, member =>
    by
      rcases List.Membership.mem_cons.mp member with same | member
      · exact same ▸ head
      · have nextArea := PreparedComparison.restored_after_area_bound samples.1 comparisons.2.1 joins.1.request branch
          ((Nat.Order.le_max_left ..).trans later) ((Nat.Order.le_max_left ..).trans later)
        have nextTotals := PreparedComparison.restored_after_total_bounds samples.1 comparisons.2.1 joins.1.request
          branch
          ((Nat.Order.le_max_left ..).trans later) ((Nat.Order.le_max_left ..).trans later)
        have nextError : Data.Gaussian.Norm.Basic.normSq ((PreparedComparison.restoredIntegral comparisons.2.1
          samples.1.endpoints.last.2).total -
            (Acquisition.Sample.restoredChart samples.2.1 samples.1.endpoints.last.2).total) ≤ (4 * allowance) ^ 2 *
              PreparedObservationCoercivity.coefficientNormSq coefficients := by
          rw [PreparedComparison.restored_total_difference comparisons.2.1]
          exact comparisons.2.1.total_bounded
        exact
          boundsFromHead
          branch _ _ bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2 joins.2
          ((Nat.Order.le_max_right ..).trans later) samples.1.endpoints.last.2
          (bounds_of_summaries _ _
            nextArea nextError nextTotals) pair member

/-- The original first prepared/chart block meets its bounds at its own direct starting endpoint. -/
private theorem firstBounds (branch : HyperellipticReciprocal.originOrder curve = 1) : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) →
    HeadBounds anchors sources
      bank plans inputs readings prepared samples comparisons
      (Samples.firstValues anchors sources bank plans inputs readings prepared samples).1
  | _, .nil, _, _, _, _, _, _, _, _ => trivial
  | _, .cons _ _ _ _, _, _, _, _, _, _, samples, comparisons => by
      apply bounds_of_summaries
        (PreparedComparison.restoredIntegral comparisons.1 samples.1.endpoints.first.2)
        (Acquisition.Sample.restoredChart samples.1 samples.1.endpoints.first.2)
          (PreparedComparison.restored_first_area_bound comparisons.1)
      · rw [PreparedComparison.restored_total_difference comparisons.1]
        exact comparisons.1.total_bounded
      · exact PreparedComparison.restored_first_total_bounds comparisons.1 branch

/-- The second paths of the retained block pairs are exactly the original restored chart paths. -/
theorem restoredPairs_right : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) →
    (previous : InverseRootPolynomial.Gaussian) →
    (restoredPairs anchors sources
      bank plans inputs readings prepared samples comparisons previous).map Prod.snd =
      Samples.restoredPaths anchors sources bank plans inputs readings prepared samples previous
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, previous =>
      congrArg (List.cons (Acquisition.Sample.restoredPath samples.1 previous))

          (restoredPairs_right
          tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2
          samples.1.endpoints.last.2)

/-- There is exactly one retained prepared/chart block pair per original parent. -/
theorem restoredPairs_length : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) →
    (previous : InverseRootPolynomial.Gaussian) →
    (restoredPairs anchors sources
      bank plans inputs readings prepared samples comparisons previous).length = parents.length
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, _ =>
      congrArg Nat.succ

          (restoredPairs_length
          tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2
          samples.1.endpoints.last.2)

/-- Both internal errors and the complete polygon of parent totals are paid. The count is the original parent count, not
a refinement-dependent mesh size. -/
@[expose] def concatenationScale (count : Nat) : Coordinate :=
  2 * ((count : InverseRootPolynomial.Coordinate) ^ 2 * (82 * (4 * allowance) ^ 2) +
    16 * (count : InverseRootPolynomial.Coordinate) ^ 4 * (4 * allowance) ^ 2 * PreparedComparison.restoredTotalBound
      (basis := basis) (allowance := allowance))

/-- The retained initial value has a ceiling fixed before source acquisition. -/
theorem firstValue_bound (branch : HyperellipticReciprocal.originOrder curve = 1) : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) →
    Data.Gaussian.Norm.Basic.normSq (Samples.firstValues anchors sources bank plans inputs readings prepared
      samples).1 ≤
      (2 + 8 * basis.coefficient) * PreparedObservationCoercivity.coefficientNormSq coefficients
  | _, .nil, _, _, _, _, _, _, _, _ => by
      change Data.Gaussian.Norm.Basic.normSq (0 : InverseRootPolynomial.Gaussian) ≤ _
      rw [Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct
        (add_nonneg (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 8)
            basis.coefficient_nonnegative))
        (FiniteSum.Fin.sumFin_zero.symm.trans_le
          (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
            Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))))
  | _, .cons _ _ _ _, _, _, _, _, _, _, samples, _ =>
      PreparedComparison.first_direct_bound samples.1 branch

/-- The sum of actual block-total discrepancies equals the difference of the two concatenated totals. -/
private theorem paired_total_sum (pairs : List (List InverseRootPolynomial.Gaussian × List
  InverseRootPolynomial.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum
      pair.1 - Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.fst).flatten -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.snd).flatten := by
  induction pairs with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons pair tail ih =>
      simp only [-eq_self, -iff_self, List.map_cons, List.flatten_cons, IncrementArea.sum_append,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih]
      ring1

/-- The extra starting-value ribbon is controlled by the initial direct endpoint, independently of the number of
acquired chart intervals. -/
@[expose] def traceComparisonScale (count : Nat) : Coordinate :=
  2 * (concatenationScale (basis
    := basis) (allowance := allowance) count +
    4 * (2 + 8 * basis.coefficient) * (count : InverseRootPolynomial.Coordinate) ^ 2 * (4 * allowance) ^ 2)

variable {parents : List (CenteredEdge curve differential)}
  {anchors : ParentCovers parents} {sources :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents}
  {bank : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors
    sources basis allowance coefficientTarget coverFloor floor}
  {plans : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials
    minimum anchors sources bank} {inputs :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors sources}
  {readings : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank
    plans inputs stage}
  {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor
    anchors sources bank plans inputs readings}

/-- The concatenated prepared and chart areas satisfy the retained homogeneous comparison bound.

The estimate pays both each original block's area discrepancy and the complete polygon formed by its actual total
increments. -/
theorem restored_concatenation_bound
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples)
    (joins : BasisCommonParentBank.Junctions anchors sources bank) (branch : HyperellipticReciprocal.originOrder curve =
      1)
    (later : joins.stage anchors sources bank ≤ stage) :
    let previous := (Samples.firstValues anchors sources bank plans inputs readings prepared samples).1
    let pairs := restoredPairs
      anchors sources bank plans inputs readings prepared samples comparisons previous
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea (pairs.map Prod.fst).flatten -
      IncrementArea.pathArea (Samples.restoredPaths anchors sources bank plans inputs readings prepared samples
        previous).flatten) ≤
      concatenationScale (basis :=
        basis) (allowance := allowance) parents.length * (PreparedObservationCoercivity.coefficientNormSq coefficients)
        ^ 2 := by
  dsimp only
  have bounded := boundsFromHead
    branch anchors sources bank plans inputs readings prepared samples comparisons joins later _
    (firstBounds branch anchors
      sources bank plans inputs readings prepared samples comparisons)
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have boundNonnegative : 0 ≤ PreparedComparison.restoredTotalBound (basis := basis) (allowance := allowance) := by
    unfold PreparedComparison.restoredTotalBound
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      (add_nonneg (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 12))
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 64)
          basis.coefficient_nonnegative))
  have estimate := IncrementAreaComparison.blocks_area_difference_bound
    (restoredPairs anchors sources
      bank plans inputs readings prepared samples comparisons
      (Samples.firstValues anchors sources bank plans inputs readings prepared samples).1)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct (4 * allowance))
      normNonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct boundNonnegative normNonnegative)
    (fun pair member => (bounded pair member).1)
    (fun pair member => (bounded pair member).2.1)
    (fun pair member => (bounded pair member).2.2.1)
    (fun pair member => (bounded pair member).2.2.2)
  rw [restoredPairs_right,
    restoredPairs_length] at estimate
  exact estimate.trans_eq (by
    unfold concatenationScale
    ring1)

/-- Total errors accumulate over the same ordered block pairs as the area comparison. No equality of prepared and chart
totals is assumed. -/
theorem restored_total_error
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples)
    (joins : BasisCommonParentBank.Junctions anchors sources bank) (branch : HyperellipticReciprocal.originOrder curve =
      1)
    (later : joins.stage anchors sources bank ≤ stage) :
    let previous := (Samples.firstValues anchors sources bank plans inputs readings prepared samples).1
    let pairs := restoredPairs
      anchors sources bank plans inputs readings prepared samples comparisons previous
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.fst).flatten
      -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (Samples.restoredPaths anchors sources bank plans inputs readings
        prepared samples previous).flatten) ≤
      (parents.length : InverseRootPolynomial.Coordinate) ^ 2 * (4 * allowance) ^ 2 *
        PreparedObservationCoercivity.coefficientNormSq coefficients := by
  dsimp only
  have bounded := boundsFromHead
    branch anchors sources bank plans inputs readings prepared samples comparisons joins later _
    (firstBounds branch anchors
      sources bank plans inputs readings prepared samples comparisons)
  let pairs := restoredPairs
    anchors sources bank plans inputs readings prepared samples comparisons
    (Samples.firstValues anchors sources bank plans inputs readings prepared samples).1
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) ((4 * allowance) ^ 2 *
      PreparedObservationCoercivity.coefficientNormSq coefficients) (by
      intro value member
      obtain ⟨pair, inPairs, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      exact (bounded pair inPairs).2.1)
  rw [paired_total_sum,
    List.Map.length_map] at estimate
  dsimp only [-eq_self, -iff_self, pairs] at estimate
  rw [restoredPairs_right,
    restoredPairs_length] at estimate
  exact estimate.trans_eq (by ring1)

/-- Trace transport retains the initial-value ribbon against the accumulated total error; an area-only comparison would
omit this term. -/
theorem restored_trace_error
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples)
    (joins : BasisCommonParentBank.Junctions anchors sources bank) (branch : HyperellipticReciprocal.originOrder curve =
      1)
    (later : joins.stage anchors sources bank ≤ stage) :
    let previous := (Samples.firstValues anchors sources bank plans inputs readings prepared samples).1
    let pairs := restoredPairs
      anchors sources bank plans inputs readings prepared samples comparisons previous
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.traceArea previous (pairs.map Prod.fst).flatten -
      IncrementArea.traceArea previous (Samples.restoredPaths anchors sources bank plans inputs readings prepared
        samples previous).flatten) ≤
      CommonPreparedConcatenation.Samples.traceComparisonScale (basis := basis) (allowance := allowance) parents.length
        * (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2 := by
  dsimp only
  let previous := (Samples.firstValues anchors sources bank plans inputs readings prepared samples).1
  let pairs := restoredPairs
    anchors sources bank plans inputs readings prepared samples comparisons previous
  let left := (pairs.map Prod.fst).flatten
  let right := (Samples.restoredPaths anchors sources bank plans inputs readings prepared samples previous).flatten
  have first := firstValue_bound
    branch anchors sources bank plans inputs readings prepared samples comparisons
  have total :=
    restored_total_error samples
    comparisons joins branch later
  have area :=
    restored_concatenation_bound
    samples comparisons joins branch later
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct first total (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    ((Data.Gaussian.Norm.Basic.normSq_nonneg _).trans first)
  have ribbon : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area previous
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum left - Data.Gaussian.Norm.Sum.Basic.gaussianSum right)) ≤
      4 * (2 + 8 * basis.coefficient) * (parents.length : InverseRootPolynomial.Coordinate) ^ 2 * (4 * allowance) ^ 2 *
        (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2 := by
    calc
      _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq previous * Data.Gaussian.Norm.Basic.normSq
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum left - Data.Gaussian.Norm.Sum.Basic.gaussianSum right) :=
        BoundaryRibbon.area_bound _ _
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq previous * Data.Gaussian.Norm.Basic.normSq
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum left - Data.Gaussian.Norm.Sum.Basic.gaussianSum right)) :=
        by
        ring1
      _ ≤ 4 * ((2 + 8 * basis.coefficient) * PreparedObservationCoercivity.coefficientNormSq coefficients *
          ((parents.length : InverseRootPolynomial.Coordinate) ^ 2 * (4 * allowance) ^ 2 *
            PreparedObservationCoercivity.coefficientNormSq coefficients)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
            decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
      _ = _ := by ring1
  have identity : IncrementArea.traceArea previous left - IncrementArea.traceArea previous right =
      (IncrementArea.pathArea left - IncrementArea.pathArea right) + BoundaryRibbon.area previous
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum left - Data.Gaussian.Norm.Sum.Basic.gaussianSum right) := by
    rw [IncrementArea.traceArea_eq, IncrementArea.traceArea_eq]
    apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, BoundaryRibbon.area,
      Data.Gaussian.Basic.conj, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
      Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im]
      <;> ring1
  change Data.Gaussian.Norm.Basic.normSq (IncrementArea.traceArea previous left - IncrementArea.traceArea
    previous right) ≤ _
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct area
      ribbon) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq
      (by
        unfold CommonPreparedConcatenation.Samples.traceComparisonScale
        ring1))

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation
