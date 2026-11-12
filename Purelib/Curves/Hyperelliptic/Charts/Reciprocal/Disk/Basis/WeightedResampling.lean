module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedPathReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open
  PreparedPathReadback.BasisPreparedCommonRequest.Acquisition.ChildPairs

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.AffineBasisEnergy

public section

/-! Resample the actual weighted source polygons retained by the common
prepared bank. The coefficient dependence remains homogeneous. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.ReciprocalDiskArcOwners

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest (BasisPreparedCommonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest
  (Acquisition)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (Plans NumericalBank Readings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples (FanPreparations Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples (PreparedComparisons)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr sumFin_mul_right sumFin_zero)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Integration.Path.IncrementArea (pathArea)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {covers :
    BasisSourceCovers parent} {index : Nat}

/-- The finite squared coefficient norm is nonnegative. -/
private theorem coefficient_nonnegative (coefficients : GaussianVector genus) :
    0 ≤ coefficientNormSq coefficients := FiniteSum.Fin.sumFin_zero.symm.trans_le
  (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Coordinate)) _ (fun row =>
    normSq_nonneg (coefficients row)))

/-- The exact cached bank supplies its own homogeneous increment slope. -/
theorem increment_bound (originals : BasisSourceLocations.PrimitiveBank covers index)
    (coefficients : GaussianVector genus) {first last : Coordinate}
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    Basic.normSq
      (PrimitiveBank.value
      originals coefficients last -
      PrimitiveBank.value
      originals coefficients first) ≤
      BasisSourceCovers.primitiveSlope
        covers * coefficientNormSq coefficients * (last - first)^2 := by
  let values := fun row => (originals.get row).primitive.value.eval (parent.edge.point last) -
    (originals.get row).primitive.value.eval (parent.edge.point first)
  let budget := WeightedNormBudget.build values
  have each (row : Fin genus) : Basic.normSq (values row) ≤ (covers.get
    row).data.sourceSlope * (last - first)^2 :=
    (originals.get row).increment_bound firstInside lastInside
  have paid : budget.scale ≤ BasisSourceCovers.primitiveSlope covers * (last - first)^2 := by
    rw [budget.scale_eq]
    have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct (Order.Positivity.sumFin_mono _ _ each)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [sumFin_mul_right] at bound
    exact bound.trans_eq (by unfold BasisSourceCovers.primitiveSlope; ring1)
  have equal : PrimitiveBank.value originals coefficients last - PrimitiveBank.value originals coefficients first =
      sumFin (fun row => coefficients row * values row) := by
    unfold PrimitiveBank.value
    rw [← sumFin_sub]
    exact sumFin_congr (fun row => by dsimp only [values]; ring1)
  rw [equal]
  exact (budget.bound coefficients).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct paid
      (coefficient_nonnegative
      coefficients)).trans_eq (by ring1))

/-- Changing the dyadic depth changes increment-path area by exactly the same amount as dyadic boundary area. -/
private theorem path_difference (value : Coordinate → Gaussian) (first
  second : Nat) :
    pathArea (dyadicIncrements value first 0 1) - pathArea
      (dyadicIncrements value second 0 1) =
      dyadicArea value first 0 1 - dyadicArea value second 0 1 := by
  have left := DyadicPrimitivePaths.traceArea_dyadicIncrements value first 0 1
  have right := DyadicPrimitivePaths.traceArea_dyadicIncrements value second 0 1
  rw [IncrementArea.traceArea_eq, DyadicPrimitivePaths.dyadicIncrements_sum] at left right
  rw [← left, ← right]
  ring1

variable {patch : PreparedPatch parent} {data :
  Data patch count} {cover :
  Cover data}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {minimum floor depth : Nat}
  {common : BasisCommonCover cover covers minimum}
    {areaAllowance sourceTarget coefficientTarget : Coordinate}
  {request : BasisPreparedCommonRequest
    regular common areaAllowance sourceTarget coefficientTarget floor}
  {box : Geometry.Rational.Box} {polynomials :
    RegularBasisPolynomials cap index box}
  {originals :
    BasisSourceLocations.PrimitiveBank
    covers index} {cells :
    BasisSourceLocations.SampleBank covers
    index}
  {coefficients : GaussianVector genus}
  {acquired :
    Acquisition
    request polynomials originals cells coefficients depth}

/-- Every finer source polygon is compared to the actual cached prepared source summary. No integral model or primitive
origin is replaced. -/
theorem BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted.source_resampling_bound
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) {scheduled : Nat}
    (later : common.depth + acquired.extraDepth ≤ scheduled) :
    Basic.normSq (pathArea (dyadicIncrements
      (PrimitiveBank.value originals coefficients) scheduled 0 1) - weighted.source.area) ≤
      quarterRadius (4 * (BasisSourceCovers.primitiveSlope covers)^2) (common.depth +
        acquired.extraDepth) *
        (coefficientNormSq coefficients)^2 := by
  have bounded := DyadicAreaRefinement.dyadicArea_refinement_bound (PrimitiveBank.value originals coefficients)
    (Arithmetic.mul_nonneg_direct (BasisSourceCovers.primitiveSlope_nonnegative covers)
      (coefficient_nonnegative
      coefficients))
    (fun _ _ firstInside lastInside =>
      increment_bound
      originals coefficients firstInside lastInside)
    (common.depth + acquired.extraDepth) (scheduled - (common.depth + acquired.extraDepth))
    (first := 0) (last := 1) ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩ (by decide)
  rw [Data.Nat.Subtraction.add_sub_of_le later, (show (1 : Fraction.Rational) - 0 = 1 by
    ring1), one_pow, Fraction.Field.mul_one_direct] at bounded
  rw [weighted.source.area_eq, Weighted.source_path weighted,
    path_difference]
  exact bounded.trans_eq (by
    rw [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]; ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.ReciprocalDiskArcOwners

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (Plans NumericalBank Readings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples (FanPreparations Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples (PreparedComparisons)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {bounds :
    UniformBounds regular.padded}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {data : UniformReciprocalModels.Data patch count}
  {basis : BasisBounds bounds}
  {allowance coefficientTarget : Coordinate} {coverFloor floor :
    Nat}
  {index minimum readingIndex : Nat} {box : Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)

variable {stage energyFloor radialDepth : Nat} {coefficients :
  GaussianVector genus}

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Integration.Path.IncrementArea (pathArea traceArea)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

/-- A coefficient-independent slope is selected from the retained covers. -/
@[expose] def weightedSourceSlopeMaximum : {parents : List (CenteredEdge curve
  differential)} →
    ParentCovers parents → SourceLocations.BasisParentSourceCovers parents →
      Coordinate
  | _, .nil, _ => 0
  | _, .cons _ _ _ tail, sources => max (BasisSourceCovers.primitiveSlope sources.head)

        (weightedSourceSlopeMaximum
        tail sources.tail)

/-- The maximum retained weighted source slope is nonnegative, including an empty parent bank. -/
theorem weightedSourceSlopeMaximum_nonnegative {parents : List (CenteredEdge curve
  differential)}
    (anchors : ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
      :
    0 ≤
      weightedSourceSlopeMaximum
      anchors sources := by
  cases anchors with
  | nil => exact le_rfl
  | cons =>
    exact (BasisSourceCovers.primitiveSlope_nonnegative sources.head).trans
      (Basic.le_max_left _ _)

/-- Maximum actual combined depth, also defined for an empty basis. -/
@[expose] def sourceDepthMaximum : {parents : List (CenteredEdge curve differential)} →
    (anchors : ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : Plans capSample polynomials minimum anchors sources bank) → (inputs :
      NumericalBank index anchors sources) →
    (readings : Readings anchors sources bank plans inputs stage) →
    (prepared : FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    PreparedComparisons anchors sources bank plans inputs readings prepared samples → Nat
  | _, .nil, _, _, _, _, _, _, _, _ => 0
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons =>
      max (bank.1.common.depth + comparisons.1.integrals.extraDepth)

          (sourceDepthMaximum
          tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2)

/-- Pair scheduled source polygons with the actual cached weighted source polygons in their original parent order. -/
@[expose] def sourceResamplingPairs (scheduled : Nat) : {parents : List (CenteredEdge curve
  differential)} →
    (anchors : ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : Plans capSample polynomials minimum anchors sources bank) → (inputs :
      NumericalBank index anchors sources) →
    (readings : Readings anchors sources bank plans inputs stage) →
    (prepared : FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    PreparedComparisons anchors sources bank plans inputs readings prepared samples → List (List
      Gaussian × List Gaussian)
  | _, .nil, _, _, _, _, _, _, _, _ => []
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons =>
      (dyadicIncrements (PrimitiveBank.value inputs.1.originals coefficients) scheduled 0 1,
        comparisons.1.weighted.values.map Prod.fst) ::

          sourceResamplingPairs
          scheduled tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2

/-- There is exactly one retained resampling pair per original parent. -/
private theorem sourceResamplingPairs_length (scheduled : Nat) : ∀ {parents : List
  (CenteredEdge curve differential)}
    (anchors : ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : Plans capSample polynomials minimum anchors sources bank) (inputs :
      NumericalBank index anchors sources)
    (readings : Readings anchors sources bank plans inputs stage)
    (prepared : FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : PreparedComparisons anchors sources bank plans inputs readings prepared samples),

      (sourceResamplingPairs
      scheduled anchors sources bank plans inputs readings prepared samples comparisons).length = parents.length
  | _, .nil, _, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons => congrArg Nat.succ
    (sourceResamplingPairs_length
    scheduled tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2)

/-- Each scheduled source polygon has exactly the same total displacement as its retained cached source polygon. -/
private theorem sourceResamplingPairs_totals (scheduled : Nat) : ∀ {parents : List
  (CenteredEdge curve differential)}
    (anchors : ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : Plans capSample polynomials minimum anchors sources bank) (inputs :
      NumericalBank index anchors sources)
    (readings : Readings anchors sources bank plans inputs stage)
    (prepared : FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : PreparedComparisons anchors sources bank plans inputs readings prepared samples),
    ∀ pair ∈
      sourceResamplingPairs
      scheduled anchors sources bank plans inputs readings prepared samples comparisons,
      gaussianSum pair.1 = gaussianSum pair.2
  | _, .nil, _, _, _, _, _, _, _, _, _, member => by cases member
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, pair, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with equal | member
      · subst pair
        rw [Weighted.source_path comparisons.1.weighted, DyadicPrimitivePaths.dyadicIncrements_sum,
          DyadicPrimitivePaths.dyadicIncrements_sum]
      · exact
          sourceResamplingPairs_totals
          scheduled tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2 pair member

/-- Every retained resampling pair satisfies the shared homogeneous area bound once its actual source depth is paid. -/
private theorem sourceResamplingPairs_bounds (scheduled : Nat) : ∀ {parents : List
  (CenteredEdge curve differential)}
    (anchors : ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : Plans capSample polynomials minimum anchors sources bank) (inputs :
      NumericalBank index anchors sources)
    (readings : Readings anchors sources bank plans inputs stage)
    (prepared : FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : PreparedComparisons anchors sources bank plans inputs readings prepared samples)
    {slope : Coordinate},
      weightedSourceSlopeMaximum
      anchors sources ≤ slope →

      sourceDepthMaximum
      anchors sources bank plans inputs readings prepared samples comparisons ≤ scheduled →
    ∀ pair ∈
      sourceResamplingPairs
      scheduled anchors sources bank plans inputs readings prepared samples comparisons,
      Basic.normSq (pathArea pair.1 - pathArea pair.2) ≤
        quarterRadius (4 * slope^2) coverFloor * (coefficientNormSq
          coefficients)^2
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, member => by cases member
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, slope, slopeUpper,
    depthUpper, pair, member =>
    by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with equal | member
      · subst pair
        have later := (Data.Nat.Order.le_max_left _ _).trans depthUpper
        have bound :=
          ReciprocalDiskArcOwners.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted.source_resampling_bound
          comparisons.1.weighted later
        have floorLe : coverFloor ≤ bank.1.common.depth + comparisons.1.integrals.extraDepth :=
          ((Data.Nat.Order.le_max_left _ _).trans_eq bank.1.common.depth_eq.symm).trans (Nat.le_add_right _ _)
        have localNonnegative := BasisSourceCovers.primitiveSlope_nonnegative sources.head
        have scale := Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.pow_le_pow_direct localNonnegative
            ((Basic.le_max_left _ _).trans slopeUpper) 2) (by
                decide : (0 : Coordinate) ≤ 4)
        have decay := quarterRadius_antitone
          (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 4)
            (Arithmetic.sq_nonneg_direct (BasisSourceCovers.primitiveSlope sources.head))) floorLe
        have scaled : quarterRadius (4 * (BasisSourceCovers.primitiveSlope sources.head)^2) coverFloor ≤
            quarterRadius (4 * slope^2) coverFloor := by
          rw [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
          exact Arithmetic.mul_le_mul_of_nonneg_right_direct scale
            (Arithmetic.pow_nonneg_direct (by decide : (0 : Coordinate) ≤ 1 / 4) _)
        rw [comparisons.1.weighted.source.area_eq] at bound
        exact bound.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct (decay.trans scaled)
          (Arithmetic.sq_nonneg_direct _))
      · exact
          sourceResamplingPairs_bounds
          scheduled tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2
          ((Basic.le_max_right _ _).trans slopeUpper)
            ((Data.Nat.Order.le_max_right _ _).trans depthUpper) pair member

/-- Equal per-pair displacements turn the complete trace-area difference into the sum of the original per-pair area
errors.

The bound pays the square of the actual pair count and retains the same starting value for both concatenated traces. -/
private theorem equalTotals_trace_bound (pairs : List (List Gaussian × List
  Gaussian)) (start : Gaussian)
    {areaError : Coordinate} (areas : ∀ pair ∈ pairs, Basic.normSq
      (pathArea pair.1 - pathArea pair.2) ≤ areaError)
    (totals : ∀ pair ∈ pairs, gaussianSum pair.1 =
      gaussianSum pair.2) :
    Basic.normSq (traceArea start (pairs.map Prod.fst).flatten -
      traceArea start (pairs.map Prod.snd).flatten) ≤
      (pairs.length : Coordinate)^2 * areaError := by
  have difference : ∀ start : Gaussian,
      traceArea start (pairs.map Prod.fst).flatten - traceArea start (pairs.map
        Prod.snd).flatten =
        gaussianSum (pairs.map (fun pair => pathArea pair.1 -
          pathArea pair.2)) := by
    clear areas start
    induction pairs with
    | nil => intro start; change (0 : Gaussian) - 0 = 0; ring1
    | cons pair pairs ih =>
        intro start
        have head := totals pair (List.mem_cons_self ..)
        have remaining := ih (fun value member => totals value (List.mem_cons_of_mem _ member)) (start +
          gaussianSum pair.2)
        change traceArea start (pair.1 ++ _) - traceArea start (pair.2 ++ _) = _
        rw [IncrementArea.traceArea_append, IncrementArea.traceArea_append, head]
        rw [show ∀ a b c d : Gaussian, a + b - (c + d) = (a - c) + (b - d) from fun _ _ _ _ => by
          ring1, remaining]
        rw [IncrementArea.traceArea_eq, IncrementArea.traceArea_eq, head]
        change _ = (pathArea pair.1 - pathArea pair.2) +
          gaussianSum (pairs.map (fun pair => pathArea pair.1 -
          pathArea pair.2))
        ring1
  rw [difference start]
  have bound := Sum.Bounds.normSq_sum_le (pairs.map (fun pair => pathArea pair.1 -
    pathArea pair.2)) areaError (by
    intro value member
    obtain ⟨pair, inPairs, rfl⟩ := Map.mem_map.mp member
    exact areas pair inPairs)
  rw [Map.length_map] at bound
  exact bound.trans_eq (by ring1)

/-- Full weighted source traces share one homogeneous resampling bound. Cross-parent ribbons and the initial value
cancel only through the proved per-parent total equalities, without assuming any polygon has zero area. -/
theorem source_trace_resampling_bound {parents : List (CenteredEdge curve differential)}
    (anchors : ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : Plans capSample polynomials minimum anchors sources bank) (inputs :
      NumericalBank index anchors sources)
    (readings : Readings anchors sources bank plans inputs stage)
    (prepared : FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : PreparedComparisons anchors sources bank plans inputs readings prepared samples)
    (scheduled : Nat) (later :
      sourceDepthMaximum
      anchors sources bank plans inputs readings prepared samples comparisons ≤ scheduled)
    (start : Gaussian) :
    let pairs :=
      sourceResamplingPairs
      scheduled anchors sources bank plans inputs readings prepared samples comparisons
    Basic.normSq (traceArea start (pairs.map Prod.fst).flatten -
      traceArea start (pairs.map Prod.snd).flatten) ≤
      (parents.length : Coordinate)^2 * quarterRadius (4 *
        (weightedSourceSlopeMaximum
        anchors sources)^2) coverFloor *
        (coefficientNormSq coefficients)^2 := by
  have bound :=
    equalTotals_trace_bound

      (sourceResamplingPairs
      scheduled anchors sources bank plans inputs readings prepared samples comparisons) start

      (sourceResamplingPairs_bounds
      scheduled anchors sources bank plans inputs readings prepared samples comparisons le_rfl later)

      (sourceResamplingPairs_totals
      scheduled anchors sources bank plans inputs readings prepared samples comparisons)
  rw
    [sourceResamplingPairs_length]
    at bound
  exact bound.trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples
