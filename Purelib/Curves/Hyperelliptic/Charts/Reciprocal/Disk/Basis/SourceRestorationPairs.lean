module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
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
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationBudget
import Mathlib.Algebra.Ring.Defs
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

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Restored/source block pairs on the exact retained parent bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs

open SourceRestorationBudget.BasisCommonParentRequest.Plan.Acquisition.Sample
open CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition

open Purelib.Data.Rat

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor : Nat}
  {index minimum readingIndex : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {stage energyFloor radialDepth : Nat} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  genus}

namespace Samples

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

open
  CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison
  (restoredTotalBound restored_after_area_bound restored_after_total_bounds)

namespace SourceRestoration

/-- The original path indexed by a retained increment-area summary.

The readback retains the summary's exact original path index and does not reconstruct or select another path. -/
@[expose] def summaryPath {path : List Normalization.InverseRootPolynomial.Gaussian} (_ : Path.IncrementArea.Summary
  path) : List Gaussian := path

/-- Pair complete restored polygons with the retained source polygons in
original parent order, including the actual incoming predecessor at each step. -/
@[expose] def pairs : {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) → (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents) →
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
      sources bank) → (inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
      sources) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
      stage) →
    (prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors
      sources bank plans inputs readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared) →
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples) →
    Normalization.InverseRootPolynomial.Gaussian → List (List Normalization.InverseRootPolynomial.Gaussian × List
      Normalization.InverseRootPolynomial.Gaussian)
  | _, .nil, _, _, _, _, _, _, _, _, _ => []
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, previous =>
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.summaryPath
        ((Sample.PreparedComparison.restoredIntegral
        comparisons.1 previous)), comparisons.1.weighted.values.map Prod.fst) ::
        pairs
          tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2
          samples.1.endpoints.last.2

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration
/-- The restored sides of the original block pairs are exactly the complete restored parent polygons. -/
theorem left : {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) → (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents) →
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
      sources bank) → (inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
      sources) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
      stage) →
    (prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors
      sources bank plans inputs readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared) →
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples) →
    (previous : Normalization.InverseRootPolynomial.Gaussian) →
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs anchors sources
      bank plans inputs readings prepared samples comparisons previous).map Prod.fst =
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.restoredPairs anchors sources bank
        plans inputs readings prepared samples comparisons previous).map Prod.fst
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, previous =>
      congrArg (List.cons
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.summaryPath
        ((Sample.PreparedComparison.restoredIntegral
        comparisons.1 previous))))
        (left tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2
          samples.1.endpoints.last.2)

/-- The source sides of the original block pairs are exactly the retained source-resampling polygons at the chosen
schedule. -/
theorem right (scheduled : Nat) : {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve
  differential)} →
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) → (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents) →
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
      sources bank) → (inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
      sources) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
      stage) →
    (prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors
      sources bank plans inputs readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared) →
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples) →
    (previous : Normalization.InverseRootPolynomial.Gaussian) →
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs anchors sources
      bank plans inputs readings prepared samples comparisons previous).map Prod.snd =
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.sourceResamplingPairs
        scheduled anchors sources bank plans inputs readings prepared samples comparisons).map Prod.snd
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, _ =>
      congrArg (List.cons (comparisons.1.weighted.values.map Prod.fst))
        (right scheduled tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2
          samples.1.endpoints.last.2)

end

/-- The original restoration/source pairing has one block for each retained parent. -/
theorem length : {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) → (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents) →
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
      sources bank) → (inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
      sources) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
      stage) →
    (prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors
      sources bank plans inputs readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared) →
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples) →
    (previous : Normalization.InverseRootPolynomial.Gaussian) →
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs anchors sources
      bank plans inputs readings prepared samples comparisons previous).length = parents.length
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, _ =>
      congrArg Nat.succ

          (length
          tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2
          samples.1.endpoints.last.2)

open
  SourceRestorationBudget.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison
  (uniformSourceAreaError uniformSourceTotalError)
open
  CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison
  (incoming_gap)

/-- The larger of the retained restored-total bound and original source-slope bound. -/
@[expose] def totalBound (slope : Normalization.InverseRootPolynomial.Coordinate) : Coordinate := max
  (Sample.PreparedComparison.restoredTotalBound
  (basis := basis) (allowance := allowance)) slope

/-- The area, increment and magnitude bounds for one original restored/source block pair.

The area error is quadratic in the coefficient norm, while increment and total bounds retain their original linear
coefficient weighting. -/
@[expose] def BlockBounds (slope : Normalization.InverseRootPolynomial.Coordinate) (pair : List
  Normalization.InverseRootPolynomial.Gaussian × List Normalization.InverseRootPolynomial.Gaussian) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea pair.1 - Path.IncrementArea.pathArea pair.2) ≤
    PreparedComparison.uniformSourceAreaError
    allowance slope * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2 ∧
  Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
    Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤
    PreparedComparison.uniformSourceTotalError
    allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ∧
  Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.totalBound (basis :=
    basis) (allowance := allowance) slope * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ∧
  Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.totalBound (basis :=
    basis) (allowance := allowance) slope * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration in
/-- Exact original area and increment summaries transport the paid restoration estimates to their indexed block paths.
-/
private theorem bounds_of_summaries (slope : Normalization.InverseRootPolynomial.Coordinate) {leftPath rightPath : List
  Normalization.InverseRootPolynomial.Gaussian}
    (left : Path.IncrementArea.Summary leftPath) (right : Path.IncrementArea.Summary rightPath)
    (area : Data.Gaussian.Norm.Basic.normSq (left.area - right.area) ≤
      PreparedComparison.uniformSourceAreaError
      allowance slope * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2)
    (total : Data.Gaussian.Norm.Basic.normSq (left.total - right.total) ≤
      PreparedComparison.uniformSourceTotalError
      allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (leftBound : Data.Gaussian.Norm.Basic.normSq left.total ≤
      Sample.PreparedComparison.restoredTotalBound
      (basis := basis) (allowance := allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    {sourceSlope : Normalization.InverseRootPolynomial.Coordinate} (sourceLe : sourceSlope ≤ slope)
    (rightBound : Data.Gaussian.Norm.Basic.normSq right.total ≤ sourceSlope *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.BlockBounds (basis :=
      basis) (allowance := allowance) (coefficients := coefficients) slope (leftPath, rightPath) := open Purelib.Algebra
      in open Purelib.Data.Rat in by
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  change Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea leftPath - Path.IncrementArea.pathArea
    rightPath) ≤ _ ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum leftPath -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum rightPath) ≤ _ ∧ Data.Gaussian.Norm.Basic.normSq
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum leftPath) ≤ _ ∧ Data.Gaussian.Norm.Basic.normSq
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum rightPath) ≤ _
  rw [← left.area_eq, ← right.area_eq, ← left.total_eq, ← right.total_eq]
  exact ⟨area, total, leftBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Basic.le_max_left _ _) nonnegative),
    rightBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (sourceLe.trans
      (Fraction.Order.Basic.le_max_right _ _)) nonnegative)⟩

/-- The original first block satisfies the common restoration/source bounds, with the empty parent list vacuous. -/
private def HeadBounds (slope : Normalization.InverseRootPolynomial.Coordinate) : {parents : List
  (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) → (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents) →
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
      sources bank) → (inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
      sources) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
      stage) →
    (prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors
      sources bank plans inputs readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared) →
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples) →
    Normalization.InverseRootPolynomial.Gaussian → Prop
  | _, .nil, _, _, _, _, _, _, _, _, _ => True
  | _, .cons _ _ _ _, _, _, _, _, _, _, _, comparisons, previous =>
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.BlockBounds (basis :=
        basis) (allowance := allowance) (coefficients := coefficients) slope
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.summaryPath
          ((Sample.PreparedComparison.restoredIntegral
          comparisons.1 previous)), comparisons.1.weighted.values.map Prod.fst)

/-- Propagate a paid first-block estimate through the original parent sequence using the scheduled retained incoming
joins. -/
private theorem boundsFromHead (slope : Normalization.InverseRootPolynomial.Coordinate) (branch :
  Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) : {parents : List
  (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) → (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents) →
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
      sources bank) → (inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
      sources) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
      stage) →
    (prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors
      sources bank plans inputs readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared) →
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples) →
    (joins : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors
      sources bank) → joins.stage anchors sources bank ≤ stage →
    (previous : Normalization.InverseRootPolynomial.Gaussian) →
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.HeadBounds slope
      anchors sources bank plans inputs readings prepared samples comparisons previous →

      WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
      anchors sources ≤ slope →
    ∀ pair ∈ Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs anchors
      sources bank plans inputs readings prepared samples comparisons previous,
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.BlockBounds (basis :=
        basis) (allowance := allowance) (coefficients := coefficients) slope pair
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, member => False.elim (List.not_mem_nil member)
  | _, .cons _ _ _ .nil, _, _, _, _, _, _, _, _, _, _, _, head, _, pair, member => by
      rcases List.Membership.mem_cons.mp member with same | empty
      · exact same ▸ head
      · exact False.elim (List.not_mem_nil empty)
  | _, .cons _ _ _ (.cons _ _ _ _), sources, bank, plans, inputs, readings, prepared, samples, comparisons, joins,
    later, _, head, slopeLe, pair, member =>
    by
      rcases List.Membership.mem_cons.mp member with same | member
      · exact same ▸ head
      · have tailSlope := (Fraction.Order.Basic.le_max_right _ _).trans slopeLe
        have nextSlope := (Fraction.Order.Basic.le_max_left _ _).trans tailSlope
        have nextGap :=
          Sample.PreparedComparison.incoming_gap
          samples.1 samples.2.1 joins.1.request branch
          ((Nat.Order.le_max_left ..).trans later) ((Nat.Order.le_max_left ..).trans later)
        have nextTotals :=
          Sample.PreparedComparison.restored_after_total_bounds
          samples.1 comparisons.2.1 joins.1.request branch
          ((Nat.Order.le_max_left ..).trans later) ((Nat.Order.le_max_left ..).trans later)
        have nextHead :=
          bounds_of_summaries
          slope

            ((Sample.PreparedComparison.restoredIntegral
            comparisons.2.1 samples.1.endpoints.last.2)) comparisons.2.1.weighted.source

            ((PreparedComparison.restored_source_area_uniform
            comparisons.2.1) _ nextGap nextSlope)

            ((PreparedComparison.restored_source_total_uniform
            comparisons.2.1) _ nextGap) nextTotals.1 nextSlope
            (PreparedComparison.source_total_bound
            comparisons.2.1)
        exact
          boundsFromHead
          slope branch _ _ bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2 joins.2
          ((Nat.Order.le_max_right ..).trans later) samples.1.endpoints.last.2 nextHead tailSlope pair member

/-- The original initial source value pays the first restoration block at the common source-slope bound. -/
private theorem firstBounds (slope : Normalization.InverseRootPolynomial.Coordinate) (branch :
  Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) : {parents : List
  (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) → (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents) →
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
      sources bank) → (inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
      sources) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
      stage) →
    (prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors
      sources bank plans inputs readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared) →
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples) →

      WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
      anchors sources ≤ slope →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.HeadBounds slope anchors
      sources bank plans inputs readings prepared samples comparisons
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues anchors sources bank plans
        inputs readings prepared samples).1
  | _, .nil, _, _, _, _, _, _, _, _, _ => trivial
  | _, .cons _ _ _ _, sources, bank, _, _, _, _, samples, comparisons, slopeLe => by
      have nextSlope := (Fraction.Order.Basic.le_max_left _ _).trans slopeLe
      have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
        Algebra.FiniteSum.Fin.sumFin_zero.symm.trans_le
        (Algebra.FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
          Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
          (coefficients row)))
      have gap : Data.Gaussian.Norm.Basic.normSq (samples.1.endpoints.first.2 - samples.1.endpoints.first.2) ≤
          bank.1.request.restoration.target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
            by
        rw [_root_.sub_self, Gaussian.Norm.Basic.normSq_zero]
        exact Rat.Fraction.Order.Arithmetic.mul_nonneg_direct bank.1.request.restoration.positive.le nonnegative
      exact
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.bounds_of_summaries
        slope
        ((Sample.PreparedComparison.restoredIntegral
        comparisons.1 samples.1.endpoints.first.2)) comparisons.1.weighted.source

          ((PreparedComparison.restored_source_area_uniform
          comparisons.1) _ gap nextSlope)
          ((PreparedComparison.restored_source_total_uniform
          comparisons.1) _ gap)

          ((Sample.PreparedComparison.restored_first_total_bounds
          comparisons.1) branch).1 nextSlope
          (PreparedComparison.source_total_bound
          comparisons.1)

variable {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} {sources :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
    allowance coefficientTarget coverFloor floor}
  {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
    sources bank} {inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
    sources}
  {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
    stage}
  {prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors sources
    bank plans inputs readings}

/-- All block errors refer to these exact restored/source pairs and the
scheduled incoming joins on the original parent bank. -/
theorem bounded (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients
  radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples)
    (joins : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors
      sources bank) (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : joins.stage anchors sources bank ≤ stage) :
    ∀ pair ∈ Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs anchors
      sources bank plans inputs readings prepared samples comparisons
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues anchors sources bank plans
        inputs readings prepared samples).1,
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.BlockBounds (basis :=
        basis) (allowance := allowance) (coefficients := coefficients)

          (WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
          anchors sources) pair :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.boundsFromHead _ branch
    anchors sources bank plans inputs readings prepared samples comparisons joins later _
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.firstBounds _ branch
      anchors sources bank plans inputs readings prepared samples comparisons le_rfl) le_rfl

end SourceRestoration
end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs
