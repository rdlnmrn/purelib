module
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedWeightedSourceMass
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedNestedDyadicPaths
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.Readings.PreparedWeightedRefinementArea
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledSourcePaths
import Purelib.Riemann.Paths.PreparedWeightedRefinementTrace
import Purelib.Integration.Path.DyadicBlockLinearReadback
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledSourcePaths

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank

open Purelib.Data.List

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation

public section

/-! Identify the complete weighted source polygon on the actual refinement
with the source polygon used by the retained-bank resampling estimate. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledWeightedPaths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (Plans NumericalBank Readings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples (FanPreparations Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples (PreparedComparisons)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples (scheduledRowRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples
  (sourceResamplingPairs)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledSourcePaths.Samples (sourceFunctions
  scheduledRowRequests_path sourceResampling_source)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest (BasisPreparedAreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)

variable {stage energyFloor radialDepth : Nat} {coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Samples

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Integration.Path.IncrementArea (pathArea traceArea)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)
open Purelib.Riemann.Readings.PreparedDyadicPrimitiveArea (dyadicPrimitivePath)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Readings.PreparedWeightedRefinementArea (WeightedRefinement)

/-- The concatenated original dyadic parent paths contain exactly the parent count times the dyadic edge count. -/
private theorem flattened_length (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential))
    (value : InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian) (depth : Nat) :
    ((parents.map (fun parent => DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.edge.point
      parameter)) depth 0 1)).flatten).length =
      parents.length * 2 ^ depth := by
  induction parents with
  | nil => exact (Nat.zero_mul _).symm
  | cons parent parents ih =>
      rw [List.map_cons, List.flatten_cons, Purelib.Data.List.Append.length_append,
        DyadicPrimitivePaths.dyadicIncrements_length, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- The retained dyadic refinement has exactly the original parent count times its dyadic subdivision count. -/
private theorem dyadic_child_count {parents children : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential)}
    {refinement : PreparedSubedgeRootQueries.RootSubedgeRefinement parents children} {depth : Nat}
    (paths : PreparedNestedDyadicPaths.DyadicPaths depth refinement) :
    children.length = parents.length * 2 ^ depth := by
  have equal := congrArg List.length (paths.flatten (fun value => value) 0)
  rw [flattened_length children (fun
    value => value) 0,
    flattened_length parents (fun value
      => value) (depth + 0), Nat.add_zero, pow_zero, Nat.mul_one] at equal
  exact equal

/-- There is exactly one retained source-function family per original parent. -/
private theorem sourceFunctions_length : ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential)}
    (anchors : UniformReciprocalCover.ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (inputs : CommonParentPlans.NumericalBank index anchors sources), (Samples.sourceFunctions anchors sources
      inputs).length = parents.length
  | _, .nil, _, _ => rfl
  | _, .cons _ _ _ tail, sources, inputs => congrArg Nat.succ
    (sourceFunctions_length
    tail sources.tail inputs.2)

/-- Combine the exact row readbacks across every original parent boundary. The source resampling theorem and model
comparison now share a literal path. -/
theorem scheduledWeightedSource_path {parents children : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential)}
    (anchors : UniformReciprocalCover.ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) (inputs :
      CommonParentPlans.NumericalBank index anchors sources)
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage)
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples)
    (refinement : PreparedSubedgeRootQueries.RootSubedgeRefinement parents children) {scheduled : Nat}
    (paths : PreparedNestedDyadicPaths.DyadicPaths scheduled refinement)
    (weighted : PreparedWeightedRefinementArea.WeightedRefinement
      (Samples.scheduledRowRequests anchors sources bank plans inputs readings prepared samples comparisons) refinement)
        :
    (weighted.weightedPairs coefficients).map Prod.fst =
      ((Samples.sourceResamplingPairs scheduled anchors sources bank plans inputs readings prepared samples
        comparisons).map Prod.fst).flatten := by
  let columns := List.ofFn (fun column : Fin children.length => fun row => (weighted.read column row).1)
  have lengths : columns.length = (Samples.sourceFunctions anchors sources inputs).length * 2 ^ scheduled := by
    rw [OfFn.Basic.length_ofFn,
      sourceFunctions_length]
    exact dyadic_child_count paths
  have rows (row : Fin genus) : columns.map (fun column => column row) =
      ((Samples.sourceFunctions anchors sources inputs).map (fun values => DyadicPrimitivePaths.dyadicIncrements (values
        row) scheduled 0 1)).flatten := by
    rw [OfFn.Basic.map_ofFn]
    exact (PreparedWeightedSourceMass.source_row weighted paths row).trans
      (Samples.scheduledRowRequests_path scheduled anchors sources bank plans inputs readings prepared samples
        comparisons row)
  have combined := DyadicBlockLinearReadback.dyadicBlocks_linear_readback
    (Samples.sourceFunctions anchors sources inputs) (fun row => coefficients row) scheduled columns lengths rows
  have left : (weighted.weightedPairs coefficients).map Prod.fst =
      columns.map (fun column => FiniteSum.Fin.sumFin (fun row => coefficients row * column row)) := by
    unfold PreparedWeightedRefinementArea.WeightedRefinement.weightedPairs
    rw [Purelib.Data.List.Map.map_map, OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn]
    rfl
  exact left.trans (combined.trans
    (Samples.sourceResampling_source scheduled anchors sources bank plans inputs readings prepared samples
      comparisons).symm)

/-- Read the combined model side directly on the same ordered children. -/
theorem weightedSample_path {parents children : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {requests : (row : Fin genus) → UniformPreparedRequests.RequestedParents count allowance
      (parents.map (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential row)))}
    {refinement : PreparedSubedgeRootQueries.RootSubedgeRefinement parents children}
    (weighted : PreparedWeightedRefinementArea.WeightedRefinement requests refinement) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (weighted.weightedPairs coefficients).map Prod.snd = children.map (fun child =>
      FiniteSum.Fin.sumFin (fun row => coefficients row *
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential row) child).model.integralSample))
          := by
  let columns := List.ofFn (fun column : Fin children.length => fun row => (weighted.read column row).2)
  let actual := children.map (fun child => fun row : Fin genus =>
    (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential row) child).model.integralSample)
  have lengths : columns.length = actual.length := by
    rw [OfFn.Basic.length_ofFn, Purelib.Data.List.Map.length_map]
  have rows (row : Fin genus) : columns.map (fun column => column row) = actual.map (fun column => column row) := by
    rw [OfFn.Basic.map_ofFn]
    change List.ofFn (fun column => (weighted.read column row).2) = _
    rw [PreparedWeightedRefinementTrace.sample_row weighted]
    change (((children.map _).map _).map _) = (children.map _).map _
    rw [Purelib.Data.List.Map.map_map, Purelib.Data.List.Map.map_map, Purelib.Data.List.Map.map_map]
    rfl
  have combined := DyadicBlockLinearReadback.weighted_map_eq (fun row => coefficients row) columns actual lengths rows
  have left : (weighted.weightedPairs coefficients).map Prod.snd =
      columns.map (fun column => FiniteSum.Fin.sumFin (fun row => coefficients row * column row)) := by
    unfold PreparedWeightedRefinementArea.WeightedRefinement.weightedPairs
    rw [Purelib.Data.List.Map.map_map, OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn]
    rfl
  exact left.trans (combined.trans (Purelib.Data.List.Map.map_map ..))

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledWeightedPaths
