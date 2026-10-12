module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedDyadicPrimitiveArea
import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Periods.PeriodMatrix

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank

open Purelib.Data.Vector

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Read the exact numerical source bank in both scheduled row paths and
the combined resampling polygon, preserving the original parent order. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledSourcePaths

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

/-- Parameterized source functions reuse the cached original polynomial for each row of each parent. -/
@[expose] def sourceFunctions : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    CommonParentPlans.NumericalBank index anchors sources → List (Fin genus → InverseRootPolynomial.Coordinate →
      InverseRootPolynomial.Gaussian)
  | _, .nil, _, _ => []
  | parent :: _, .cons _ _ _ tail, sources, inputs =>
      (fun row parameter => (inputs.1.originals.get row).primitive.value.eval (parent.edge.point parameter)) ::
        sourceFunctions tail
          sources.tail inputs.2

/-- Transporting the retained request along an equality of counts preserves its exact original primitive polynomial. -/
private theorem primitive_cast {source : Differentials.Basic.Differential genus} {parent :
  PreparedSubdivisionModelCore.CenteredEdge curve source}
    {first second : Nat} {target : InverseRootPolynomial.Coordinate} (equal : first = second)
    (request : UniformPreparedRequests.LocalRequest parent first target) :
    (Eq.mp (congrArg (fun count => UniformPreparedRequests.LocalRequest parent count target) equal)
      request).request.model.primitive.value =
      request.request.model.primitive.value := by
  cases equal
  rfl

/-- Tolerance weakening and the count cast retain the exact original polynomial at every parameter, not just its
endpoint increment. -/
theorem scheduledRowRequests_path (scheduled : Nat) :
    ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (anchors : UniformReciprocalCover.ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) (inputs :
      CommonParentPlans.NumericalBank index anchors sources)
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage)
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) (row : Fin
      genus),
    PreparedDyadicPrimitiveArea.dyadicPrimitivePath scheduled (Samples.scheduledRowRequests anchors sources bank plans
      inputs readings prepared samples comparisons row) =
      ((sourceFunctions anchors sources
        inputs).map (fun values => DyadicPrimitivePaths.dyadicIncrements (values row) scheduled 0 1)).flatten
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, row => by
      rw [Samples.scheduledRowRequests]
      dsimp only [PreparedDyadicPrimitiveArea.dyadicPrimitivePath]
      apply congrArg₂ List.append
      · have count_eq : (sources.head.get row).count = genus := by
          unfold SourceLocations.BasisParentSourceCovers.head
          rw [DependentVector.ofFn_get]
          cases sources.get row
          rfl
        rw [primitive_cast count_eq]
        change DyadicPrimitivePaths.dyadicIncrements (fun parameter =>
          (comparisons.1.integrals.prepared.get row).localRequest.request.model.primitive.value.eval _) scheduled 0 1 =
            _
        rw [comparisons.1.integrals.primitive_eq row]
        rfl
      · exact
          scheduledRowRequests_path
          scheduled tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2 row

/-- The resampling source is the same parent bank combined with the supplied coefficients before taking each complete
dyadic path. -/
theorem sourceResampling_source (scheduled : Nat) :
    ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (anchors : UniformReciprocalCover.ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) (inputs :
      CommonParentPlans.NumericalBank index anchors sources)
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage)
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples),
    ((Samples.sourceResamplingPairs scheduled anchors sources bank plans inputs readings prepared samples
      comparisons).map Prod.fst).flatten =
      ((sourceFunctions anchors sources
        inputs).map (fun values =>
        DyadicPrimitivePaths.dyadicIncrements (fun parameter => FiniteSum.Fin.sumFin (fun row => coefficients row *
          values row parameter)) scheduled 0 1)).flatten
  | _, .nil, _, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons => by
      apply congrArg₂ List.append rfl
      exact
        sourceResampling_source
        scheduled tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledSourcePaths
